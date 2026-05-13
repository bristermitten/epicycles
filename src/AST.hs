{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Core AST, evaluation, and HOAS encoding.
module AST (
    AST (..),
    ShowAST,
    pattern Param,
    EpicycleId (..),
    numberCurve,
    evalExpr,
    evalEpiParams,
    CurveExpr (..),
    Curve,
    Expr (..),
    ApproxEq (..),
    BindableNum (..),
    IEnv,
    ASTSort (..),
    SortVal (..),
    Stage (..),
    XEpicycle,
    CurveState (..),
    EpicycleParamType,
    EpicycleParam (..),
    SEpicycleParam (..),
)
where

import GUI.Util (showFixed, showRational)
import Pretty (PrettyCurve (pretty, prettyPrec), SyntaxHighlight (..), annotate)
import Prettyprinter (Doc)
import Prettyprinter qualified as PP
import Unembedding
import Unembedding qualified as Ue
import Unembedding.Env (Env (..), Ix, lookEnv)
import Unembedding.Env qualified as Ue

-- | singleton type thing to mark whether an ast node is a number or a curve
type data ASTSort = SNum Type | SCurve

-- | reifies a 'ASTSort' into a Haskell type
data SortVal (s :: ASTSort) where
    VNum :: (BindableNum n) => n -> SortVal (SNum n)
    VCurve :: Curve -> SortVal SCurve

deriving instance Show (SortVal s)

type IEnv = Ue.Env SortVal

data CurveState env = CurveState
    { curveAST :: AST Numbered env SCurve
    , envParams :: IEnv env
    }
    deriving (Show)

    

-- | Class for approximate equality of values
class ApproxEq a where
    approxEq :: a -> a -> Bool

instance ApproxEq Double where
    approxEq a b = abs (a - b) < 1e-5 * max 1 (abs a) 
    -- the choice of 1e-5 is a bit arbitrary and maybe not very principled but seems to work well in practice

instance ApproxEq Int where
    approxEq = (==)

instance ApproxEq Rational where
    approxEq = (==)

-- | class for types which can be used as literals in the AST
class (Num n, Eq n, ApproxEq n, Show n) => BindableNum n where
    isFinite :: n -> Bool
    safeDiv :: n -> n -> Maybe n
    divBN :: n -> n -> n
    prettyLit :: n -> Doc SyntaxHighlight

instance BindableNum Double where
    isFinite x = not (isNaN x || isInfinite x)
    safeDiv _ 0 = Nothing
    safeDiv a b = let r = a / b in if isFinite r then Just r else Nothing
    divBN a b = a / b
    prettyLit x = annotate HLLiteral (pretty $ showFixed 3 x)

instance BindableNum Int where
    isFinite _ = True
    safeDiv _ 0 = Nothing
    -- to make sure GetPut holds, we only allow division when it divides evenly
    safeDiv a b
        | a `mod` b == 0 = Just (a `div` b)
        | otherwise = Nothing
    divBN a b = a `div` b
    prettyLit x = annotate HLLiteral (pretty x)

instance BindableNum Rational where
    isFinite _ = True
    safeDiv _ 0 = Nothing
    safeDiv a b = Just (a / b)
    divBN a b = a / b
    prettyLit x = annotate HLLiteral (PP.pretty (showRational 3 x))

type data Stage = Parsed | Numbered

type family XEpicycle (p :: Stage) where
    XEpicycle Parsed = ()
    XEpicycle Numbered = EpicycleId

type family XParam (s :: ASTSort) where
    XParam SCurve = Void -- we can never bind curves
    XParam (SNum n) = ()

-- | De-Bruijn indexed concrete syntax for expressions.
data AST (x :: Stage) (env :: [ASTSort]) (s :: ASTSort) where
    -- | A literal value
    Lit :: (BindableNum n) => n -> AST x env (SNum n)
    -- | Reference a variable / parameter from the environment
    Param_ :: XParam s -> Ix env s -> AST x env s
    -- | Addition of two expressions
    Add :: (BindableNum n) => AST x env (SNum n) -> AST x env (SNum n) -> AST x env (SNum n)
    -- | Multiplication of two expressions
    Mul :: (BindableNum n) => AST x env (SNum n) -> AST x env (SNum n) -> AST x env (SNum n)
    -- | Reciprocal of an expression
    Recip :: (BindableNum n, Fractional n) => AST x env (SNum n) -> AST x env (SNum n)
    -- | Define an epicycle with radius, frequency, and phase.
    Epicycle :: XEpicycle x -> AST x env (SNum Rational) -> AST x env (SNum Int) -> AST x env (SNum Rational) -> AST x env SCurve
    -- | Append two curves together
    Append :: AST x env SCurve -> AST x env SCurve -> AST x env SCurve
    -- | Let-binding
    Let :: (Typeable n, BindableNum n) => AST x env (SNum n) -> AST x (SNum n : env) a -> AST x env a

pattern Param :: (XParam s ~ ()) => Ix env s -> AST x env s
pattern Param ix = Param_ () ix

{-# COMPLETE Lit, Param, Add, Mul, Recip, Epicycle, Append, Let #-}

instance LiftVariables (AST Parsed) where
    type Var (AST Parsed) = Ix
    type LiftConstraint (AST Parsed) s = (XParam s ~ ())
    liftVar = Param

instance Expr (EnvI (AST Parsed)) where
    lit x = liftFO0 (Lit x)
    add = liftFO2 Add
    mul = liftFO2 Mul
    recip = liftFO1 Recip

    let_ =
        liftSOn
            @(AST Parsed)
            (ol0 @(AST Parsed) :. ol1 @(AST Parsed) :. ENil)
            Let

instance CurveExpr (EnvI (AST Parsed)) where
    epicycle = liftFO3 (Epicycle ())
    cappend = liftFO2 Append

liftFO3 :: (forall env. sem env a -> sem env b -> sem env c -> sem env d) -> EnvI sem a -> EnvI sem b -> EnvI sem c -> EnvI sem d
liftFO3 f x y z = liftFO (\(ECons xx (ECons yy (ECons zz _))) -> f xx yy zz) (ECons x (ECons y (ECons z ENil)))

-- | Data-less tag for a curve used for type safety in GADTs
data Curve deriving (Show, Eq)

-- | A unique identifier for an epicycle
newtype EpicycleId = EpicycleId Int deriving (Show, Eq, Ord)

instance PrettyCurve EpicycleId where
    prettyPrec _ (EpicycleId n) = pretty 'e' <> pretty n

{- | Uniquely number the epicycles in a curve AST, producing a 'Numbered' AST
-}
numberAST :: AST Parsed '[] SCurve -> State EpicycleId (AST Numbered '[] SCurve)
numberAST = go
  where
    go :: AST Parsed env SCurve -> State EpicycleId (AST Numbered env SCurve)
    go (Epicycle () r f p) = do
        eid <- get
        modify' (\(EpicycleId n) -> EpicycleId (n + 1))
        r' <- goVal r
        f' <- goVal f
        p' <- goVal p
        pure (Epicycle eid r' f' p')
    go (Append a b) = Append <$> go a <*> go b
    go (Let val body) = do
        val' <- goVal val
        Let val' <$> go body

    goVal :: AST Parsed env (SNum n) -> State EpicycleId (AST Numbered env (SNum n))
    goVal (Lit x) = pure (Lit x)
    goVal (Param ix) = pure (Param ix)
    goVal (Add a b) = Add <$> goVal a <*> goVal b
    goVal (Mul a b) = Mul <$> goVal a <*> goVal b
    goVal (Recip a) = Recip <$> goVal a
    goVal (Let val body) = Let <$> goVal val <*> goVal body

instance {-# INCOHERENT #-} (CurveExpr e) => Semigroup (e SCurve) where
    (<>) = cappend

numberCurve :: (forall e. (CurveExpr e) => e SCurve) -> AST Numbered '[] SCurve
numberCurve term =
    let ast :: AST Parsed '[] SCurve = Ue.runClose term
     in numberAST ast `evalState` EpicycleId 0

evalExpr :: IEnv env -> AST phase env (SNum n) -> n
evalExpr _ (Lit x) = x
evalExpr env (Param_ _ ix) = case lookEnv env ix of
    VNum v -> v
evalExpr env (Add a b) = evalExpr env a + evalExpr env b
evalExpr env (Mul a b) = evalExpr env a * evalExpr env b
evalExpr env (Recip a) = 1 / evalExpr env a
evalExpr env (Let val body) =
    let v = evalExpr env val
     in evalExpr (ECons (VNum v) env) body

data EpicycleParam
    = Radius
    | Frequency
    | Phase
    deriving (Eq, Show, Ord, Enum, Bounded, Generic)

data SEpicycleParam (p :: EpicycleParam) where
    SRadius :: SEpicycleParam Radius
    SFrequency :: SEpicycleParam Frequency
    SPhase :: SEpicycleParam Phase

type family EpicycleParamType param where
    EpicycleParamType Radius = Rational
    EpicycleParamType Frequency = Int
    EpicycleParamType Phase = Rational

evalEpiParam :: SEpicycleParam param -> EpicycleId -> IEnv env -> AST Numbered env SCurve -> Maybe (EpicycleParamType param)
evalEpiParam param eid env (Epicycle eid' r f p) =
    if eid == eid'
        then case param of
            SRadius -> Just (evalExpr env r)
            SFrequency -> Just (evalExpr env f)
            SPhase -> Just (evalExpr env p)
        else Nothing
evalEpiParam param eid env (Append a b) =
    case evalEpiParam param eid env a of
        Just v -> Just v
        Nothing -> evalEpiParam param eid env b
evalEpiParam param eid env (Let val body) =
    evalEpiParam param eid (ECons (VNum (evalExpr env val)) env) body

evalEpiParams :: IEnv env -> AST Numbered env SCurve -> EpicycleId -> Maybe (Rational, Int, Rational)
evalEpiParams env ast eid =
    (,,)
        <$> evalEpiParam SRadius eid env ast
        <*> evalEpiParam SFrequency eid env ast
        <*> evalEpiParam SPhase eid env ast

-- | HOAS representation of expressions.
class Expr (e :: ASTSort -> Type) where
    lit :: (BindableNum n) => n -> e (SNum n)
    add :: (BindableNum n) => e (SNum n) -> e (SNum n) -> e (SNum n)
    mul :: (BindableNum n) => e (SNum n) -> e (SNum n) -> e (SNum n)
    recip :: (BindableNum n, Fractional n) => e (SNum n) -> e (SNum n)
    let_ :: (Typeable n, BindableNum n) => e (SNum n) -> (e (SNum n) -> e a) -> e a

class (Expr e) => CurveExpr e where
    epicycle :: e (SNum Rational) -> e (SNum Int) -> e (SNum Rational) -> e SCurve
    cappend :: e SCurve -> e SCurve -> e SCurve

deriving instance (Show (XEpicycle x), Show (XParam s)) => Show (AST x env s)

-- | convenience type synonym for a show constraint on ASTs
type ShowAST v = (forall sigma. Show (AST Numbered sigma v))
