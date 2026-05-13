{-# LANGUAGE OverloadedRecordDot #-}

-- | Translates mouse movements into 'SceneEdit's
module GUI.ImguiInteraction
  ( DragState (..),
    DragParam (..),
    CurveId (..),
    initDrag,
    applyDragMotion,
    findHover,
    HoverLocation (..),
    DragAction (..),
    hoverParamOf,
  )
where

import AST (EpicycleId, EpicycleParam (..))
import Data.Foldable (minimumBy)
import Data.Map qualified as Map
import GUI.Config (clickThresholdSq, freqDragSensitivity, minRadius)
import GUI.Types
import GUI.Util (distToRingSq, distToSegmentSq, normaliseAngle)
import GUI.Viewport (CanvasRegion, ScreenPos (..), ViewTransform (..), localCoords)
import Scene (SceneEdit (..), VisualEpicycle (..), VisualScene (..))
import Vec (Vec (..))
import Vec qualified

-- | what part of the epicycle is the mouse hovering over?
data HoverLocation = HoverRing | HoverArm
  deriving (Show, Eq)

hoverParamOf :: HoverLocation -> EpicycleParam
hoverParamOf HoverArm = Phase
hoverParamOf HoverRing = Radius

data DragParam
  = DragRadius {radiusOffset :: Double, armAngle :: Double}
  | DragFreq {freqInitial :: Int, freqStartX :: Double}
  | DragPhase {phaseInitial :: Double, phaseStartAngle :: Double}

-- | information about an ongoing drag operation
data DragState = DragState
  { -- |  which curve is being dragged
    dsCurveId :: CurveId,
    -- | which epicycle is being dragged
    dsEpicycleId :: EpicycleId,
    -- | what parameter of the epicycle is being dragged, and where the drag started (for calculating deltas)
    dsParam :: DragParam,
    -- | the centre of the epicycle being dragged
    dsParentCentre :: Vec
  }

-- | Find the closest epicycle ID to a given point within a single visual scene, under some tolerance threshold.
findClosestInScene ::
  VisualScene ->
  -- | point to test
  Vec ->
  -- | threshold squared
  Double ->
  -- | the epicycle id, the distance to the circumference (squared), and the distance to the arm (squared)
  Maybe (EpicycleId, Double, Double)
findClosestInScene scene localMouse threshold =
  case filter (\(_, dR, dA) -> min dR dA < threshold) dists of
    [] -> Nothing
    xs -> Just $ minimumBy (comparing $ \(_, dR, dA) -> min dR dA) xs
  where
    dists = do
      eid <- toList scene.vsEpicycleOrder
      let ve = scene.vsEpicycles Map.! eid
      pure (eid, distToRingSq localMouse ve.veCentre (abs ve.veRadius), distToSegmentSq localMouse ve.veCentre ve.veEndpoint)

-- | Find the closest epicycle to a position across all curves
findHover ::
  CanvasRegion ->
  Map CurveId (ViewTransform, VisualScene) ->
  ScreenPos ->
  Maybe (CurveId, EpicycleId, HoverLocation)
findHover canvasRegion curveMap mouse = do
  (cid, eid, _, dR, dA) <- findHitCurve canvasRegion curveMap mouse
  pure (cid, eid, if dA < dR then HoverArm else HoverRing)

findHitCurve ::
  CanvasRegion ->
  Map CurveId (ViewTransform, VisualScene) ->
  ScreenPos ->
  Maybe (CurveId, EpicycleId, Double, Double, Double)
findHitCurve canvasRegion curveMap mouse =
  case mapMaybe calcHit (Map.toList curveMap) of
    [] -> Nothing
    xs -> Just $ minimumBy (comparing $ \(_, _, d, _, _) -> d) xs
  where
    calcHit (cid, (vt, scene)) = do
      let scaleSq = vt.vtScale * vt.vtScale
      (eid, dR, dA) <- findClosestInScene scene (localCoords canvasRegion vt mouse) (clickThresholdSq / scaleSq)
      pure (cid, eid, min dR dA * scaleSq, dR, dA)

-- | What part of the epicycle is being hovered or dragged
data DragAction
  = -- | dragging the radius or phase (left click)
    EditShape
  | -- | dragging the frequency (right click)
    EditFrequency
  deriving (Show, Eq)

-- | Build a 'DragState' from a click event, if an epicycle is under the mouse
initDrag ::
  CanvasRegion ->
  Map CurveId (ViewTransform, VisualScene) ->
  DragAction ->
  ScreenPos ->
  Maybe DragState
initDrag canvasRegion curveMap action mouse = do
  -- re-run picking to get the distances
  (cid, eid, _, dR, dA) <- findHitCurve canvasRegion curveMap mouse
  (vt, scene) <- Map.lookup cid curveMap
  ve <- Map.lookup eid scene.vsEpicycles

  let localMouse = localCoords canvasRegion vt mouse
      angle = ve.veArmAngle
      armDir = Vec (cos angle) (sin angle)
      param
        | action == EditShape && dA < dR =
            -- left click + close to arm = edit phase
            let mouseAngle = Vec.angle (localMouse - ve.veCentre)
             in DragPhase ve.vePhase mouseAngle
        | action == EditShape =
            -- left click + close to ring = edit radius
            let proj = Vec.dot (localMouse - ve.veCentre) armDir
             in DragRadius (ve.veRadius - proj) angle
        | otherwise =
            -- right click = edit frequency
            let ScreenPos (sx, _) = mouse
             in DragFreq ve.veFreq (realToFrac sx)

  pure DragState {dsCurveId = cid, dsEpicycleId = eid, dsParam = param, dsParentCentre = ve.veCentre}

-- | Apply a drag motion to produce a 'SceneEdit'
applyDragMotion ::
  CanvasRegion ->
  DragState ->
  -- | current mouse position
  ScreenPos ->
  ViewTransform ->
  SceneEdit
applyDragMotion canvasRegion ds mouse vt =
  let localMouse = localCoords canvasRegion vt mouse
   in case ds.dsParam of
        DragRadius offset angle ->
          let armDir = Vec (cos angle) (sin angle)
              proj = Vec.dot (localMouse - ds.dsParentCentre) armDir
              newRadius = max minRadius (proj + offset)
           in SetRadius ds.dsEpicycleId newRadius
        DragFreq initFreq startScreenX ->
          let ScreenPos (sx, _) = mouse
              displacement = realToFrac sx - startScreenX
              newFreq = round (fromIntegral Double initFreq + displacement / freqDragSensitivity)
           in SetFrequency ds.dsEpicycleId newFreq
        DragPhase initPhase startAngle ->
          let currentAngle = Vec.angle (localMouse - ds.dsParentCentre)
              rawDelta = currentAngle - startAngle
              delta = normaliseAngle rawDelta
           in SetPhase ds.dsEpicycleId (initPhase + delta)
