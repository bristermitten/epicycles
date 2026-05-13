{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

-- | basic 2d vector type and operations
module Vec (Vec (..), distSquared, dot, scale, angle, toComplex, fromComplex) where

import Data.Complex (Complex (..), imagPart, magnitude, realPart)
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import GHC.Num qualified

data Vec = Vec {x :: !Double, y :: !Double}
    deriving (Show, Eq)

derivingUnbox
    "Vec"
    [t|Vec -> (Double, Double)|]
    [|\(Vec x y) -> (x, y)|]
    [|(uncurry Vec)|]

instance Num Vec where
    (+) (Vec x1 y1) (Vec x2 y2) = Vec (x1 + x2) (y1 + y2)
    (-) a b = a + scale (-1) b
    (*) (Vec x1 y1) (Vec x2 y2) = Vec (x1 * x2 - y1 * y2) (x1 * y2 + y1 * x2)
    abs v = Vec (magnitude (toComplex v)) 0
    signum v = let m = magnitude (toComplex v) in Vec (x v / m) (y v / m)
    fromInteger i = Vec (GHC.Num.fromInteger i) 0

toComplex :: Vec -> Complex Double
toComplex (Vec rx iy) = rx :+ iy

fromComplex :: Complex Double -> Vec
fromComplex (rx :+ iy) = Vec rx iy

scale :: Double -> Vec -> Vec
scale k (Vec vx vy) = Vec (k * vx) (k * vy)

distSquared :: Vec -> Vec -> Double
distSquared a b = magnitude (toComplex (a - b)) ^ (2 :: Int)

-- | dot product
dot :: Vec -> Vec -> Double
dot (Vec x1 y1) (Vec x2 y2) = x1 * x2 + y1 * y2

{- | angle of a vector in radians, in the range (-pi, pi]
>>> angle (Vec 1 0)
0.0
>>> angle (Vec 0 1)
1.5707963267948966
-}
angle :: Vec -> Double
angle v = atan2 (imagPart c) (realPart c)
  where
    c = toComplex v
