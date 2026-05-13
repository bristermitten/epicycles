{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedRecordDot #-}

-- | renders a 'VisualScene' to the ImGui canvas
module GUI.ImguiRender (renderScenes, renderDrawingPath) where

import AST (EpicycleId)
import Data.Fixed (mod')
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Vector.Unboxed as U (toList)
import DearImGui.Raw qualified as Raw
import DearImGui.Raw.DrawList qualified as DL
import GUI.Colour
import GUI.Config (traceStepLive)
import GUI.ImguiInteraction (CurveId (..), DragParam (..), DragState (..), HoverLocation (..))
import GUI.ImguiUtils
import GUI.Viewport (CanvasRegion (..), ViewTransform, curveToScreen, viewScale)
import Scene (VisualEpicycle (..), VisualScene (..), tracePoints)
import Vec (Vec)

-- | Draw all visual scenes to the ImGui background draw list.
renderScenes ::
  -- | for coordinate conversion
  CanvasRegion ->
  -- | scenes to draw, with their ids, transforms, and whether to show construction lines
  [(CurveId, ViewTransform, VisualScene, Colour, Bool)] ->
  -- | the hovered epicycle, if any
  Maybe (CurveId, EpicycleId, HoverLocation) ->
  -- | the currently dragged epicycle, if any
  Maybe DragState ->
  IO ()
renderScenes canvasRegion scenes hover mDrag = do
  drawList <- Raw.getBackgroundDrawList

  let (cw, ch) = canvasRegion.crSize
  addRectFilled drawList (0, 0) (cw, ch) canvasBackground

  forM_ scenes \(cid, vt, scene, colour, showCon) -> do
    let traceT = mod' scene.vsTime (2 * pi)
        toScreen = curveToScreen canvasRegion vt
        screenScale = viewScale vt

    let tracePts =
          [ toScreen pt
          | pt <- U.toList $ tracePoints scene traceStepLive traceT
          ]

    when (length tracePts >= 2) $
      addPolyLine drawList tracePts colour 1.5

    let mHoverState = case hover of
          Just (hcid, heid, ht) | hcid == cid -> Just (heid, ht)
          _ -> Nothing
    let mDragState = case mDrag of
          Just ds | ds.dsCurveId == cid -> Just (ds.dsEpicycleId, ds.dsParam)
          _ -> Nothing
    drawVisualEpicycles drawList toScreen screenScale scene mHoverState mDragState showCon

-- | draw the epicycle rings and arms
drawVisualEpicycles ::
  DL.DrawList ->
  (Vec -> (Float, Float)) ->
  Float ->
  VisualScene ->
  Maybe (EpicycleId, HoverLocation) ->
  Maybe (EpicycleId, DragParam) ->
  Bool ->
  IO ()
drawVisualEpicycles drawList toScreen screenScale scene mHover mDrag showCon = do
  forM_ scene.vsEpicycleOrder \eid -> do
    let ve = scene.vsEpicycles Map.! eid
        ctr = toScreen ve.veCentre
        endpt = toScreen ve.veEndpoint
        screenRadius = screenScale * realToFrac (abs ve.veRadius)

    when (showCon && ve.veVisible) do
      addCircle drawList ctr screenRadius blue 32 1.0
      addLine drawList ctr endpt red 1.0

    let highlightRing = case mDrag of
          Just (deid, DragRadius {}) | deid == eid -> True
          _ -> case mHover of
            Just (heid, HoverRing) | heid == eid -> True
            _ -> False
        highlightArm = case mDrag of
          Just (deid, DragPhase {}) | deid == eid -> True
          _ -> case mHover of
            Just (heid, HoverArm) | heid == eid -> True
            _ -> False

    when highlightRing $ addCircle drawList ctr screenRadius magenta 32 3.0
    when highlightArm $ addLine drawList ctr endpt magenta 3.0

  let tip = toScreen scene.vsPenTip
  addCircleFilled drawList tip 4.0 green 12

-- | Render the in-progress freehand drawing path.
renderDrawingPath :: Maybe (NonEmpty (Float, Float)) -> IO ()
renderDrawingPath Nothing = pass
renderDrawingPath (Just pts) | length pts < 2 = pass
renderDrawingPath (Just pts) = do
  drawList <- Raw.getBackgroundDrawList

  addPolyLine drawList (NE.toList $ NE.reverse pts) transparentBlack 2.0
