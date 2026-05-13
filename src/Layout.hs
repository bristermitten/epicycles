{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

-- | simple layout system for arranging multiple curves on the screen.
-- we don't use this much, and it was mainly designed as a quick fix to help with designing the poster.
-- the only remaining use is in the Entrypoint.layoutWordScene function which uses it to space glyphs
-- it's also not that relevant to our thesis, as unlike everything else this is only unidirectional with no editing support
-- as such, we don't mention it in the dissertation, however it's left as a reference and example of where future work could go.
module Layout (
    Layout (..),
    beside,
    above,
    row,
    col,
    padded,
    scaled,
    solveLayout,
    layoutSize,
    LayoutResult (..),
)
where

import Curve (BoundingBox (..), CurveDisplay (..), positionCurve)
import Vec (Vec (..))

data Layout
    = Leaf CurveDisplay
    | Space Double Double
    | Beside Double Layout Layout
    | Above Double Layout Layout
    | Pad Double Layout
    | Scaled Double Layout

beside :: Layout -> Layout -> Layout
beside = Beside 20

above :: Layout -> Layout -> Layout
above = Above 20

row :: Double -> [Layout] -> Layout
row gap = \case
    [] -> Space 0 0
    x : xs -> foldl' (Beside gap) x xs

col :: Double -> [Layout] -> Layout
col gap = \case
    [] -> Space 0 0
    x : xs -> foldl' (Above gap) x xs

padded :: Double -> Layout -> Layout
padded = Pad

scaled :: Double -> Layout -> Layout
scaled = Scaled

data Measured
    = MLeaf {mWidth :: Double, mHeight :: Double, leafCurve :: CurveDisplay, leafCenter :: Vec}
    | MSpace {mWidth :: Double, mHeight :: Double}
    | MBeside {mWidth :: Double, mHeight :: Double, gap :: Double, left :: Measured, right :: Measured}
    | MAbove {mWidth :: Double, mHeight :: Double, gap :: Double, top :: Measured, bottom :: Measured}
    | MPad {mWidth :: Double, mHeight :: Double, padding :: Double, inner :: Measured}
    | MScale {mWidth :: Double, mHeight :: Double, scaleFactor :: Double, scaledInner :: Measured}

measure :: Layout -> Measured
measure = \case
    Leaf pc ->
        let BoundingBox w h center = pc.cdBBox
         in MLeaf w h pc center
    Space w h -> MSpace w h
    Beside gap l r ->
        let ml = measure l; mr = measure r
         in MBeside (mWidth ml + gap + mWidth mr) (max (mHeight ml) (mHeight mr)) gap ml mr
    Above gap t b ->
        let mt = measure t; mb = measure b
         in MAbove (max (mWidth mt) (mWidth mb)) (mHeight mt + gap + mHeight mb) gap mt mb
    Pad p inner ->
        let mi = measure inner
         in MPad (mWidth mi + 2 * p) (mHeight mi + 2 * p) p mi
    Scaled s inner ->
        let mi = measure inner
         in MScale (mWidth mi * s) (mHeight mi * s) s mi

newtype LayoutResult = LayoutResult
    { lrCurves :: [CurveDisplay]
    }

instance Semigroup LayoutResult where
    a <> b = LayoutResult (lrCurves a <> lrCurves b)

instance Monoid LayoutResult where
    mempty = LayoutResult []

layoutSize :: Layout -> (Double, Double)
layoutSize layout = let m = measure layout in (mWidth m, mHeight m)

solveLayout :: Layout -> LayoutResult
solveLayout layout =
    let m = measure layout
        origin = Vec (-(mWidth m / 2)) (mHeight m / 2)
     in go 1.0 origin m
  where
    go s origin = \case
        MLeaf{..} ->
            let cd' = leafCurve{cdScale = leafCurve.cdScale * s}
                sw = mWidth * s
                sh = mHeight * s
                offset = origin - leafCenter + Vec (sw / 2) (-(sh / 2))
             in LayoutResult [positionCurve offset cd']
        MSpace _ _ -> mempty
        MBeside{..} ->
            let oml = origin + Vec 0 (-((mHeight - left.mHeight) / 2))
                omr = origin + Vec (left.mWidth + gap) (-((mHeight - right.mHeight) / 2))
             in go s oml left <> go s omr right
        MAbove{..} ->
            let omt = origin + Vec ((mWidth - top.mWidth) / 2) 0
                omb = origin + Vec ((mWidth - bottom.mWidth) / 2) (-(top.mHeight + gap))
             in go s omt top <> go s omb bottom
        MPad{..} ->
            go s (origin + Vec padding (-padding)) inner
        MScale{..} ->
            let innerOff =
                    Vec
                        ((mWidth - scaledInner.mWidth) / 2)
                        (-((mHeight - scaledInner.mHeight) / 2))
             in go (s * scaleFactor) (origin + innerOff) scaledInner
