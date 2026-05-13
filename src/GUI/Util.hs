module GUI.Util (clamp, showFixed, showRational, normaliseAngle, distToRingSq, distToSegmentSq) where

import Data.Fixed (mod')
import Vec

-- | clamp a value between a lower and upper bound
clamp :: (Ord a) => a -> a -> a -> a
clamp min' max' = max min' . min max'

{- | Show a 'Double' with a fixed number of decimal places, without trailing zeros.
>>> showFixed 2 1.2345
"1.23"
>>> showFixed 2 1.2
"1.2"
>>> showFixed 10 (1/3)
"0.3333333333"
>>> showFixed 3 1
"1.0"
-}
showFixed :: Int -> Double -> Text
showFixed digits value =
    let factor :: Integer = 10 ^ digits
        rounded =
            fromIntegral Double (round (value * fromIntegral Double factor) :: Int)
                / fromIntegral Double factor
     in show rounded

{- | Show a 'Rational' as a decimal approximation with the given number of digits.
>>> showRational 3 (1/3)
"0.333"
-}
showRational :: Int -> Rational -> Text
showRational digits = showFixed digits . fromRational

-- | Clamp the angle to the range [-pi, pi]
normaliseAngle :: Double -> Double
normaliseAngle a =
    let a' = mod' (a + pi) (2 * pi)
     in if a' < 0 then a' + 2 * pi - pi else a' - pi

-- | Compute the distance from a point to an epicycle ring, squared.
distToRingSq :: Vec -> Vec -> Double -> Double
distToRingSq p centre radius =
    let d = sqrt (Vec.distSquared p centre)
     in (d - abs radius) * (d - abs radius)

-- | compute the distance from a point to the end of an epicycle arm, squared
distToSegmentSq :: Vec -> Vec -> Vec -> Double
distToSegmentSq p a b =
    let ab = b - a
        ap = p - a
        ab2 = Vec.dot ab ab
        t =
            if ab2 == 0
                then 0
                else max 0 (min 1 (Vec.dot ap ab / ab2))
        proj = a + Vec.scale t ab
     in Vec.distSquared p proj
