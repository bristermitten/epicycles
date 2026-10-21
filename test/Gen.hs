{-# LANGUAGE NoStrict #-}
{-# LANGUAGE UndecidableInstances #-}

-- | hedgehog generators for AST terms
module Gen where

import AST
import Hedgehog (Gen)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Data.Type.Equality ((:~:) (Refl))
import Text.Show (showsPrec)

import ContextualEmbeddings
import Utils
import Update.SnS.Common

-- | a context description where every variable is a Double so that we can autogenerate 'Param's
type Doubles = Env ((:~:) (SNum Double))


-- | produce a list of generators for indexes of each possible parameter in the environment
genIx :: Doubles env -> [Gen (Ix env (SNum Double))]
genIx ENil = []
genIx (ECons Refl rest) = pure IxZ : map (fmap IxS) (genIx rest)

-- | an expression over the given context, with a "fuel" parameter to avoid arbitrarily large expressions
genExprIn :: Doubles env -> Int -> Gen (AST x env (SNum Double))
genExprIn ctx n =
    Gen.choice $
        (Lit <$> genNonZero)
            : map (fmap Param) (genIx ctx)
            ++ if n <= 0
                then []
                else
                    [ Add <$> sub <*> sub
                    , Mul <$> sub <*> sub
                    , Recip <$> sub
                    , Let <$> sub <*> genExprIn (ECons Refl ctx) (n - 1)
                    ]
  where
    sub = genExprIn ctx (n - 1)

genClosedExpr :: Gen (AST x Empty (SNum Double))
genClosedExpr = genExprIn ENil 3


-- | a 'Doubles' of some unknown @env@
data SomeDoubles = forall env. DiffEnv env => SomeDoubles (Doubles env)

-- | create a 'Doubles' for an env of a given length
mkDoubles :: Int -> SomeDoubles
mkDoubles k
    | k <= 0 = SomeDoubles ENil
    | otherwise = case mkDoubles (k - 1) of SomeDoubles ctx -> SomeDoubles (ECons Refl ctx)

-- | an expression over an environment of arbitrary size
data SomeExpr x = forall env. DiffEnv env => SomeExpr (Doubles env) (AST x env (SNum Double))

instance (Show (XEpicycle x)) => Show (SomeExpr x) where
    showsPrec d (SomeExpr _ e) = showsPrec d e

genSomeExpr :: Gen (SomeExpr x)
genSomeExpr = do
    k <- Gen.int (Range.linear 0 50)
    case mkDoubles k of SomeDoubles ctx -> SomeExpr ctx <$> genExprIn ctx 3


genEnv :: forall env. Gen Double -> Doubles env -> Gen (IEnv env)
genEnv _  ENil = pure ENil
genEnv genDouble (ECons Refl env) = do
    env' <- genEnv genDouble env
    i <- genDouble
    pure (ECons (VNum i) env')