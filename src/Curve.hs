{-# LANGUAGE OverloadedRecordDot #-}

{- | Display-level curve representation: with details like positioning, scaling, and bounding boxes.
-}
module Curve (
    CurveDisplay (..),
    SomeCurveState (..),
    BoundingBox (..),
    placeCurve,
    placeCurveScaled,
    makeCurve,
    positionCurve,
    rebuildCurveDisplay,
)
where

import AST (CurveExpr, CurveState (..), numberCurve)
import AST qualified
import Data.List
import Data.Set qualified as Set
import Data.Vector.Unboxed as UV (toList)
import GUI.Colour
import Scene (evalScene)
import Scene qualified
import Unembedding.Env qualified as Ue
import Update.SnS.Common
import Vec (Vec (..))

data SomeCurveState = forall env. (DiffEnv env) => SomeCurveState (CurveState env)

data BoundingBox = BoundingBox
    { bbWidth :: Double
    , bbHeight :: Double
    , bbCenter :: Vec
    }

data CurveDisplay = CurveDisplay
    { cdOffset :: Vec
    , cdScale :: Double
    , cdColor :: Colour
    , cdShowConstruction :: Bool
    , cdHidden :: Set AST.EpicycleId
    , cdState :: SomeCurveState
    , cdBBox :: BoundingBox
    }

mkCurveDisplay :: Vec -> Double -> Colour -> Bool -> SomeCurveState -> CurveDisplay
mkCurveDisplay offset scale color showCon state@(SomeCurveState cs) =
    CurveDisplay offset scale color showCon Set.empty state (sceneBoundingBox (evalScene cs 0))

placeCurve :: Vec -> Colour -> Bool -> (forall e. (CurveExpr e) => e AST.SCurve) -> CurveDisplay
placeCurve = placeCurveScaled 1.0

placeCurveScaled :: Double -> Vec -> Colour -> Bool -> (forall e. (CurveExpr e) => e AST.SCurve) -> CurveDisplay
placeCurveScaled scale offset color showCon term =
    mkCurveDisplay offset scale color showCon (SomeCurveState (CurveState (numberCurve term) Ue.ENil))

-- | Build a curve at the origin, which can be positioned later by 'positionCurve'
makeCurve :: Colour -> Bool -> (forall e. (CurveExpr e) => e AST.SCurve) -> CurveDisplay
makeCurve = placeCurveScaled 1.0 (Vec 0 0)

positionCurve :: Vec -> CurveDisplay -> CurveDisplay
positionCurve offset cd = cd{cdOffset = offset}

rebuildCurveDisplay :: CurveDisplay -> CurveDisplay
rebuildCurveDisplay cd =
    case cd.cdState of
        SomeCurveState cs -> cd{cdBBox = sceneBoundingBox (evalScene cs 0)}

sceneBoundingBox :: Scene.VisualScene -> BoundingBox
sceneBoundingBox scene =
    let pts = UV.toList $ Scene.tracePoints scene (2 * pi / 128) (2 * pi)
        xs = map (.x) pts
        ys = map (.y) pts
        minX = minimum xs
        maxX = maximum xs
        minY = minimum ys
        maxY = maximum ys
     in BoundingBox
            { bbWidth = maxX - minX
            , bbHeight = maxY - minY
            , bbCenter = Vec ((minX + maxX) / 2) ((minY + maxY) / 2)
            }
