-- | Delta language for the FuseDM backward strategy.
module Delta (
    NumDelta (..),
    AtomicNumDelta (..),
    CurveDelta (..),
    pattern NumDeltaId,
    pattern NumDeltaAdd,
    pattern NumDeltaMul,
    pattern NumDeltaReplace,
    applyAtomicNumDelta,
    applyNumDelta,
    embedANumDelta,
    numDeltaCompose,
    simplifyAtomicNumDelta,
    simplifyNumDelta,
    splitNumSuffix,
    DeltaEnv,
    EnvDelta (..),
    simplifyDelta,
    applyDeltaEnv,
    embedNumDelta,
    zeroDeltas,
    longestCommonSuffix,
    sizeOfDelta,
)
where

import AST (AST (..), ASTSort (..), BindableNum, EpicycleId, IEnv, SortVal (..))
import Data.List.NonEmpty qualified as NE
import Unembedding.Env qualified as Ue

{- | an 'atomic' numeric delta, i.e. "NumDelta" in the dissertation
except composition
-}
data AtomicNumDelta n
    = -- | id_n
      ANumDeltaId
    | -- | +_Delta n
      ANumDeltaAdd n
    | -- | *_Delta n
      ANumDeltaMul n
    | -- | repl_n n
      ANumDeltaReplace n
    deriving (Show)

{- | an actual numeric delta including composition
we separate them to make the composition / semigroup more type safe
since atomic deltas can't compose
-}
data NumDelta n
    = AtomicNumDelta (AtomicNumDelta n)
    | ComposeNumDeltas (NonEmpty (AtomicNumDelta n))
    deriving (Show)

pattern NumDeltaId :: NumDelta n
pattern NumDeltaId = AtomicNumDelta ANumDeltaId

pattern NumDeltaAdd :: n -> NumDelta n
pattern NumDeltaAdd n = AtomicNumDelta (ANumDeltaAdd n)

pattern NumDeltaMul :: n -> NumDelta n
pattern NumDeltaMul n = AtomicNumDelta (ANumDeltaMul n)

pattern NumDeltaReplace :: n -> NumDelta n
pattern NumDeltaReplace n = AtomicNumDelta (ANumDeltaReplace n)

{-# COMPLETE NumDeltaId, NumDeltaAdd, NumDeltaMul, NumDeltaReplace, ComposeNumDeltas #-}

{- | apply a numeric delta to a number.
corresponds to the judgement dv◁ v ⇝ v′
-}
applyAtomicNumDelta :: (Num n) => AtomicNumDelta n -> n -> n
applyAtomicNumDelta ANumDeltaId n = n -- D-Id-N
applyAtomicNumDelta (ANumDeltaReplace n') _ = n' -- D-Repl-N
applyAtomicNumDelta (ANumDeltaAdd n') n = n + n' -- D-Add-N
applyAtomicNumDelta (ANumDeltaMul n') n = n * n' -- D-Mul-N

-- | apply a 'NumDelta' to a number
applyNumDelta :: (Num n) => NumDelta n -> n -> n
applyNumDelta (AtomicNumDelta d) x = applyAtomicNumDelta d x
applyNumDelta (ComposeNumDeltas ds) x = foldr applyAtomicNumDelta x ds -- D-Comp-N

-- | a delta over curves
data CurveDelta
    = -- | id_c
      CurveDeltaId
    | -- | epicycle_Delta
      CurveDeltaEpi
        -- | id_c
        EpicycleId
        -- | dv_n_r
        (NumDelta Rational)
        -- | dv_n_ω
        (NumDelta Int)
        -- | dv_n_ϕ
        (NumDelta Rational)
    | -- | dv_c1 ⊕_Delta dv_c2
      CurveDeltaAppend
        -- | dv_c1
        CurveDelta
        -- | dv_c2
        CurveDelta
    deriving (Show)

-- | Compose two numeric deltas, removing redundant identities.
numDeltaCompose :: forall n. (Eq n, Num n) => NumDelta n -> NumDelta n -> NumDelta n
numDeltaCompose d1 d2 =
    simplifyList (simplifyAtomicNumDelta <$> (toList' d1 <> toList' d2))
  where
    toList' (AtomicNumDelta d) = [d]
    toList' (ComposeNumDeltas ds) = NE.toList ds

    -- returns identity on an empty list, otherwise composes the list into a single delta
    simplifyList :: [AtomicNumDelta n] -> NumDelta n
    simplifyList =
        maybe
            NumDeltaId
            ComposeNumDeltas
            . filterNonId

    -- remove all identities
    filterNonId :: [AtomicNumDelta n] -> Maybe (NonEmpty (AtomicNumDelta n))
    filterNonId = nonEmpty . filter (/= ANumDeltaId)

instance (Num n, Eq n) => Semigroup (NumDelta n) where
    (<>) = numDeltaCompose

simplifyAtomicNumDelta :: (Num n, Eq n) => AtomicNumDelta n -> AtomicNumDelta n
simplifyAtomicNumDelta (ANumDeltaAdd 0) = ANumDeltaId
simplifyAtomicNumDelta (ANumDeltaMul 1) = ANumDeltaId
simplifyAtomicNumDelta dv = dv

simplifyNumDelta :: (Num n, Eq n) => NumDelta n -> NumDelta n
simplifyNumDelta (AtomicNumDelta d) = AtomicNumDelta (simplifyAtomicNumDelta d)
simplifyNumDelta (ComposeNumDeltas deltas) =
    -- Filter out identities and see if anything is left
    let filtered =
            NE.filter
                (\dv -> simplifyNumDelta (AtomicNumDelta dv) /= NumDeltaId)
                deltas
     in case filtered of
            [] -> NumDeltaId
            [x] -> AtomicNumDelta x
            (x : xs) -> ComposeNumDeltas (x :| xs)

instance (Eq n, Num n) => Monoid (NumDelta n) where
    mempty = NumDeltaId

-- | singleton-esque wrapper for numeric deltas over some @'SNum' n@
data EnvDelta (s :: ASTSort) where
    EDNum :: (BindableNum n) => NumDelta n -> EnvDelta (SNum n)

deriving instance Show (EnvDelta s)

deriving instance Eq (EnvDelta s)

simplifyDelta :: EnvDelta s -> EnvDelta s
simplifyDelta (EDNum d) = EDNum (simplifyNumDelta d)

-- | the type of the delta environment
type DeltaEnv = Ue.Env EnvDelta

-- | Embed (or more specifically the `exp` function) a delta into the AST
embedANumDelta :: (BindableNum n) => AtomicNumDelta n -> AST x env (SNum n) -> AST x env (SNum n)
embedANumDelta ANumDeltaId db = db
embedANumDelta (ANumDeltaAdd n) db = Add (Lit n) db
embedANumDelta (ANumDeltaMul n) db = Mul (Lit n) db
embedANumDelta (ANumDeltaReplace n) _ = Lit n

-- | Embed a 'NumDelta' into the AST
embedNumDelta :: (BindableNum n) => NumDelta n -> AST x env (SNum n) -> AST x env (SNum n)
embedNumDelta (AtomicNumDelta d) db = embedANumDelta d db
embedNumDelta (ComposeNumDeltas ds) db = foldr embedANumDelta db ds

deriving instance (Eq n) => Eq (AtomicNumDelta n)

deriving instance (Eq n) => Eq (NumDelta n)

deriving instance Eq CurveDelta

-- | the "^ suffix" operator
longestCommonSuffix :: EnvDelta s -> EnvDelta s -> (EnvDelta s, EnvDelta s, EnvDelta s)
longestCommonSuffix (EDNum d1) (EDNum d2) =
    let (s, p1, p2) = splitNumSuffix d1 d2
     in (EDNum s, EDNum p1, EDNum p2)

-- | split a pair of numeric deltas into their longest common suffix, and the remaining prefixes
splitNumSuffix ::
    (Eq n, Num n) =>
    NumDelta n ->
    NumDelta n ->
    ( NumDelta n
    , NumDelta n
    , NumDelta n
    )
splitNumSuffix d1 d2 =
    let l1 = reverse $ toList'' d1
        l2 = reverse $ toList'' d2
        commonReversed = takeWhileEqual l1 l2
        suffix = mk (reverse commonReversed)
        p1 = mk (reverse $ drop (length commonReversed) l1)
        p2 = mk (reverse $ drop (length commonReversed) l2)
     in (suffix, p1, p2)
  where
    toList'' (AtomicNumDelta d) = [d]
    toList'' (ComposeNumDeltas ds) = NE.toList ds
    takeWhileEqual (x : xs) (y : ys) | x == y = x : takeWhileEqual xs ys
    takeWhileEqual _ _ = []
    mk = maybe NumDeltaId ComposeNumDeltas . nonEmpty

applyDeltaEnv :: DeltaEnv env -> IEnv env -> IEnv env
applyDeltaEnv Ue.ENil Ue.ENil = Ue.ENil
applyDeltaEnv (Ue.ECons d restD) (Ue.ECons v restV) =
    let newV = case (d, v) of
            (EDNum numD, VNum val) -> VNum (applyNumDelta numD val)
        restV' = applyDeltaEnv restD restV
     in Ue.ECons newV restV'

{- | makes a 'DeltaEnv' which matches the shape of the given 'IEnv', but with all 'Delta's set to identity (i.e. no change)
essentially the "zero" delta environment for a given environment length
-}
zeroDeltas :: IEnv env -> DeltaEnv env
zeroDeltas Ue.ENil = Ue.ENil
zeroDeltas (Ue.ECons val rest) = Ue.ECons (toId val) (zeroDeltas rest)

-- | Convert a 'SortVal' to the corresponding identity 'EnvDelta' for that sort
toId :: SortVal s -> EnvDelta s
toId (VNum _) = EDNum NumDeltaId

-- | Count the operations in a numeric delta
sizeOfDelta :: EnvDelta s -> Int
sizeOfDelta (EDNum d) = sizeOfNumDelta d

{- | Count the updates in a numeric delta.
We only use this to provide more fine grained information about what the algorithm was doing
-}
sizeOfNumDelta :: NumDelta n -> Int
sizeOfNumDelta NumDeltaId = 0
sizeOfNumDelta (AtomicNumDelta _) = 1
sizeOfNumDelta (ComposeNumDeltas ds) =
    -- count only the non-identity operations in the composed list
    length $ NE.filter (\case ANumDeltaId -> False; _ -> True) ds
