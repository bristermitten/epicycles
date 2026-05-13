-- | A "compiler" from lists of points to terms in our language
module Compiler (fourierCurve, interpolate) where

import AST
import Data.Complex (Complex (..), magnitude, phase)
import Data.Complex qualified as Complex
import Data.List (foldl1', maximum, partition)

data FourierTerm = FourierTerm
  { ftCoeff :: Complex Double,
    ftFreq :: Int
  }

fourierCoefficient :: [(Double, Double)] -> Int -> Complex Double
fourierCoefficient points k =
  let n = length points
      term j (px, py) =
        let theta = -(2 * pi * fromIntegral Double k * j / fromIntegral Double n)
         in (px :+ py) * Complex.cis theta
   in sum (zipWith term [0 ..] points) / fromIntegral (Complex Double) n

allTerms :: Int -> [(Double, Double)] -> [FourierTerm]
allTerms maxFreq points =
  [FourierTerm (fourierCoefficient points k) k | k <- [-maxFreq .. maxFreq]]

-- | build a curve expression from a list of points using the Discrete Fourier Transformation
fourierCurve :: [(Double, Double)] -> Int -> (forall e. (CurveExpr e) => e SCurve)
fourierCurve points numTerms =
  let maxFreq = min (length points `div` 2) (numTerms * 2)
      ranked = take numTerms $ sortOn (Down . magnitude . ftCoeff) (allTerms maxFreq points)
      (dc, rest) = partition (\ft -> ftFreq ft == 0) ranked
      (shape, detail) = partition (\ft -> abs (ftFreq ft) <= 2) rest
   in case filter (not . null) [dc, shape, detail] of
        [] -> epicycle (lit 0) (lit 0) (lit 0)
        groups -> foldl1' cappend (map buildBand groups)

buildBand :: (CurveExpr e) => [FourierTerm] -> e SCurve
buildBand [] = epicycle (lit 0) (lit 0) (lit 0)
buildBand terms =
  let maxR = maximum (map (magnitude . ftCoeff) terms)

      toEpicycle s ft =
        epicycle
          (mul s (lit (toRational (magnitude (ftCoeff ft) / maxR))))
          (lit (ftFreq ft))
          (lit (toRational (phase (ftCoeff ft))))
   in let_ (lit (toRational maxR)) $ \s ->
        foldl1' cappend (map (toEpicycle s) terms)

-- | Interpolate a closed curve defined by a list of points
interpolate :: Int -> [(Double, Double)] -> [(Double, Double)]
interpolate _ [] = []
interpolate n corners@(firstPoint : _) =
  let closed = corners <> [firstPoint]
      edges = zip closed (drop 1 closed)
      lengths = map (\((x1, y1), (x2, y2)) -> sqrt ((x2 - x1) ^ (2 :: Int) + (y2 - y1) ^ (2 :: Int))) edges
      totalLen = sum lengths
      cumulativeDists = scanl (+) 0 lengths
      step = totalLen / fromIntegral Double n
      segments = zip3 cumulativeDists (drop 1 cumulativeDists) edges

      pointAt d =
        let d' = mod' d totalLen
         in case find (\(start, end, _) -> d' >= start && d' <= end) segments of
              Just (start, end, (p1, p2)) ->
                let alpha = if end `approxEq` start then 0 else (d' - start) / (end - start)
                 in lerpPt alpha p1 p2
              Nothing -> firstPoint
   in map (\i -> pointAt (fromIntegral Double i * step)) [0 .. n - 1]

lerpPt :: Double -> (Double, Double) -> (Double, Double) -> (Double, Double)
lerpPt t (x1, y1) (x2, y2) = (x1 + t * (x2 - x1), y1 + t * (y2 - y1))

mod' :: Double -> Double -> Double
mod' a b = a - b * fromIntegral Double (floor (a / b) :: Int)
