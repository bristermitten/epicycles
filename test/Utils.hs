module Utils where

import AST
import ContextualEmbeddings
import Hedgehog (Gen)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Scene

emptyEnv :: IEnv Empty
emptyEnv = ENil

env1 :: Double -> IEnv (Empty :/: SNum Double)
env1 x = ECons (VNum x) ENil

env2 :: Double -> Double -> IEnv (Empty :/: SNum Double :/: SNum Double)
env2 x y = ECons (VNum x) (env1 y)

mkState :: (forall e env. (CurveExpr e) => e env SCurve) -> CurveState Empty
mkState term = CurveState (numberCurve term) ENil

litR :: (Expr e) => Double -> e env (SNum Rational)
litR = lit . toRational

-- | a generator for time values in the range [0, 2*pi]
genTime :: H.Gen Double
genTime = Gen.double (Range.linearFracFrom 1.0 0.01 (2 * pi))

-- | a generatoe for 'sensible' positive radius values
genPositiveRadius :: H.Gen Double
genPositiveRadius = Gen.double (Range.linearFracFrom 50 1.0 500.0)

-- | a generator for 'sensible' frequency values
genFreq :: H.Gen Int
genFreq = Gen.int (Range.linearFrom 1 (-200) 200)

-- | generate a non-zero finite double
genNonZero :: Gen Double
genNonZero = Gen.filter (/= 0) genFinite

{- | generate a finite double in a reasonable range
uses a scaled down integer so that the shrink tree is still finite, otherwise tests sometimes time out when trying to shrink forever
-}
genFinite :: Gen Double
genFinite = (/ 100) . fromIntegral Double <$> Gen.int (Range.linearFrom 0 (-100000) 100000)

firstEpiId :: CurveState Empty -> EpicycleId
firstEpiId = head . targetEpiIds

targetEpiIds :: CurveState Empty -> NonEmpty EpicycleId
targetEpiIds cs = vsEpicycleOrder (evalScene cs 0)
