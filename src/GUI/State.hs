module GUI.State (
    Msg (..),
    AppState (..),
    CurveEntry (..),
    initialActiveStrategy,
    ActiveStrategy (..),
    mkCurveEntry,
    updateAppState,
    translateSDLEvent,
    fullCanvasRegion,
    canvasAdjustedView,
    initialCurveMap,
)
where

import AST
import Compiler (fourierCurve, interpolate)
import Curve
import Data.List ((!!))
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import GUI.Colour
import GUI.Config (codePanelWidth, controlsPanelWidth, maxCanvasZoom, minCanvasZoom, uiMargin)
import GUI.ImguiInteraction
import GUI.Types
import GUI.Util
import GUI.Viewport
import SDL qualified
import Scene
import Vec

data AppState = AppState
    { appCurves :: Map CurveId CurveEntry
    , appTime :: Double
    , appPaused :: Bool
    , appSpeed :: Double
    , appWindowSize :: (Int, Int)
    , appCanvasRegion :: CanvasRegion
    , appCanvasPan :: (Float, Float)
    , appCanvasZoom :: Double
    , appShiftHeld :: Bool
    , appDrag :: Maybe DragState
    , appHover :: Maybe (CurveId, EpicycleId, HoverLocation)
    , appMousePos :: (Float, Float)
    , appScenes :: Map Text [CurveDisplay]
    , appScene :: Text
    , appCtrlHeld :: Bool
    , appDrawing :: Maybe (NonEmpty (Float, Float))
    , appStrategy :: ActiveStrategy
    , appLastSimplifyInfo :: Maybe (CurveId, Int, Int, Int)
    , quitRequested :: Bool
    }

data ActiveStrategy where
    ActiveStrategy ::
        UpdateStrategy strat ->
        Maybe (EditInfo strat) ->
        ActiveStrategy

initialActiveStrategy :: ActiveStrategy
initialActiveStrategy = ActiveStrategy Scene.heuristicStrategy Nothing

data Msg
    = UITogglePaused
    | UIResetTime
    | UISetSpeed Double
    | UISetTime Double
    | UIToggleCurveConstruction CurveId Bool
    | UILoadScene Text
    | UISetStrategy ActiveStrategy
    | WindowResized Int Int
    | KeyPressed
        -- | key code
        SDL.Keycode
        -- | is Shift held
        Bool
    | KeyReleased
        -- | key code
        SDL.Keycode
        -- | is Shift held
        Bool
    | MouseMoved
        -- | Pos
        (Float, Float)
        -- | RelMotion
        (Float, Float)
        -- | Buttons held
        [SDL.MouseButton]
    | MouseScrolled Double
    | MousePressed
        -- | button
        SDL.MouseButton
        -- | position
        (Float, Float)
    | MouseReleased
    | Tick Double
    | Quit

-- | Evaluate a 'CurveDisplay' to a 'VisualScene' at the given time.
sceneAt :: CurveDisplay -> Double -> VisualScene
sceneAt pc t = case pc.cdState of
    SomeCurveState cs -> evalScene cs t

-- | Build a 'CurveEntry' from a 'CurveDisplay' at a given time.
mkCurveEntry :: CurveDisplay -> Double -> CurveEntry
mkCurveEntry pc t = CurveEntry pc (sceneAt pc t) Nothing 12

-- | Build the curve map from a list of placed curves at a given time.
initialCurveMap :: [CurveDisplay] -> Double -> Map CurveId CurveEntry
initialCurveMap pcs t = Map.fromList [(CurveId i, mkCurveEntry pc t) | (i, pc) <- zip [0 ..] pcs]

-- | Refresh the cached 'VisualScene' for an entry at the given time.
rebuildEntry :: CurveEntry -> Double -> CurveEntry
rebuildEntry ce t = ce{ceScene = sceneAt ce.cePlaced t}

-- | Extract the 'ViewTransform' from a 'CurveEntry'.
viewTransform :: CurveEntry -> ViewTransform
viewTransform ce = ViewTransform ce.cePlaced.cdOffset ce.cePlaced.cdScale

canvasAdjustedView :: AppState -> CurveEntry -> ViewTransform
canvasAdjustedView state ce =
    let base = viewTransform ce
        (panX, panY) = state.appCanvasPan
     in ViewTransform
            (base.vtOffset + Vec (realToFrac panX) (realToFrac panY))
            (base.vtScale * state.appCanvasZoom)

{- | construct the scene map, associating curve ids with their scenes and transforms
-}
pickableScenes :: AppState -> Map CurveId (ViewTransform, VisualScene)
pickableScenes state =
    Map.mapMaybe
        ( \ce ->
            if ce.cePlaced.cdShowConstruction
                then Just (canvasAdjustedView state ce, ce.ceScene)
                else Nothing
        )
        state.appCurves

pointInCanvas :: CanvasRegion -> (Float, Float) -> Bool
pointInCanvas region (mx, my) =
    let (originX, originY) = region.crOrigin
        (canvasW, canvasH) = region.crSize
     in mx >= originX
            && mx <= originX + canvasW
            && my >= originY
            && my <= originY + canvasH

mouseInPanel :: AppState -> Bool
mouseInPanel state =
    let (mx, _my) = state.appMousePos
        winW = case state.appWindowSize of (w, _) -> fromIntegral Float w :: Float
        m = uiMargin
        inLeftPanel = mx >= m && mx <= m + codePanelWidth
        inRightPanel = mx >= winW - m - controlsPanelWidth && mx <= winW - m
     in inLeftPanel || inRightPanel

-- | Turn an SDL event into a 'Msg', if it's relevant
translateSDLEvent :: SDL.Event -> Maybe Msg
translateSDLEvent (SDL.Event _ payload) = case payload of
    SDL.WindowResizedEvent (SDL.WindowResizedEventData _ (SDL.V2 w h)) ->
        Just $ WindowResized (fromIntegral Int w) (fromIntegral Int h)
    SDL.KeyboardEvent dat ->
        let isShift = dat.keyboardEventKeysym.keysymKeycode `elem` [SDL.KeycodeLShift, SDL.KeycodeRShift]
            key = dat.keyboardEventKeysym.keysymKeycode
         in case dat.keyboardEventKeyMotion of
                SDL.Pressed -> Just $ KeyPressed key isShift
                SDL.Released ->
                    Just $ case key of
                        SDL.KeycodeEscape -> Quit
                        _ -> KeyReleased key isShift
    SDL.MouseMotionEvent dat ->
        Just $
            MouseMoved
                (fromSdlPoint dat.mouseMotionEventPos)
                (fromSDLV2 dat.mouseMotionEventRelMotion)
                dat.mouseMotionEventState
    SDL.MouseWheelEvent dat ->
        let SDL.V2 _ scrollY = dat.mouseWheelEventPos
         in Just $ MouseScrolled (if scrollY > 0 then 1.1 else 0.9)
    SDL.MouseButtonEvent dat ->
        let pos = fromSdlPoint dat.mouseButtonEventPos
         in case dat.mouseButtonEventMotion of
                SDL.Pressed -> Just $ MousePressed dat.mouseButtonEventButton pos
                SDL.Released -> Just MouseReleased
    _ -> Nothing

-- | Convert an SDL point to a normal tuple.
fromSdlPoint :: (Integral a) => SDL.Point SDL.V2 a -> (Float, Float)
fromSdlPoint (SDL.P v2) = fromSDLV2 v2

fromSDLV2 :: (Integral a) => SDL.V2 a -> (Float, Float)
fromSDLV2 (SDL.V2 x y) = (fromIntegral Float x, fromIntegral Float y)

updateAppState :: AppState -> Msg -> AppState
updateAppState = update

update :: AppState -> Msg -> AppState
update state UITogglePaused = togglePaused state
update state UIResetTime =
    state
        { appTime = 0
        , appCurves = fmap (`rebuildEntry` 0) state.appCurves
        }
update state (UISetSpeed s) = state{appSpeed = s}
update state (UISetTime t) = state{appTime = t, appCurves = fmap (`rebuildEntry` t) state.appCurves}
update state (UILoadScene i) =
    case state.appScenes Map.!? i of
        Nothing -> state
        Just curves ->
            let t0 = 0
             in state
                    { appCurves = initialCurveMap curves t0
                    , appScene = i
                    , appTime = t0
                    , appPaused = True
                    , appCanvasPan = (0, 0)
                    , appCanvasZoom = 1.0
                    , appDrag = Nothing
                    , appHover = Nothing
                    , appDrawing = Nothing
                    }
update state (UIToggleCurveConstruction cid visible) =
    state
        { appCurves =
            Map.adjust
                ( \entry ->
                    let placed' = entry.cePlaced{cdShowConstruction = visible}
                     in entry{cePlaced = placed'}
                )
                cid
                state.appCurves
        }
update state (UISetStrategy strat) = state{appStrategy = strat}
update state (WindowResized w h) =
    state
        { appWindowSize = (w, h)
        , appCanvasRegion = fullCanvasRegion (w, h)
        }
-- keyboard events

update state (KeyPressed key isShift) =
    let state' = if isShift then state{appShiftHeld = True} else state
        state'' = if isCtrlKey key then state'{appCtrlHeld = True} else state'
     in handleKeypress state'' key
update state (KeyReleased key isShift) =
    let state' = if isShift then state{appShiftHeld = False} else state
     in if isCtrlKey key then state'{appCtrlHeld = False} else state'
-- mouse events

update state (MouseMoved mousePos (dx, dy) buttons) =
    case state.appDrawing of
        Just pts ->
            let (lx, ly) = head pts
                dist2 = (fst mousePos - lx) ^ (2 :: Int) + (snd mousePos - ly) ^ (2 :: Int)
             in if dist2 >= 16 -- at least 4px apart
                    then state{appDrawing = Just (mousePos NE.<| pts), appMousePos = mousePos}
                    else state{appMousePos = mousePos}
        Nothing ->
            let isPanning = SDL.ButtonMiddle `elem` buttons || (SDL.ButtonLeft `elem` buttons && state.appShiftHeld)
                pannedState =
                    if isPanning && pointInCanvas state.appCanvasRegion mousePos
                        then state{appCanvasPan = (fst state.appCanvasPan + dx, snd state.appCanvasPan - dy)}
                        else state

                hovered =
                    if pointInCanvas pannedState.appCanvasRegion mousePos
                        then findHover pannedState.appCanvasRegion (pickableScenes pannedState) (ScreenPos mousePos)
                        else Nothing

                state' = pannedState{appMousePos = mousePos, appHover = hovered}
             in case state'.appDrag of
                    Nothing -> state'
                    Just ds -> applyDrag state' ds mousePos
update state (MouseScrolled zoomFactor)
    | pointInCanvas state.appCanvasRegion state.appMousePos
        && not (mouseInPanel state) =
        state{appCanvasZoom = clamp minCanvasZoom maxCanvasZoom (state.appCanvasZoom * zoomFactor)}
    | otherwise = state
update state (MousePressed button mousePos)
    -- ctrl+click on canvas: start freehand drawing
    | button == SDL.ButtonLeft
    , state.appCtrlHeld
    , pointInCanvas state.appCanvasRegion mousePos =
        state{appDrawing = Just (mousePos :| [])}
    | otherwise =
        let mDrag
                | state.appShiftHeld = Nothing
                | pointInCanvas state.appCanvasRegion mousePos =
                    let dragAction = if button == SDL.ButtonLeft then EditShape else EditFrequency
                     in initDrag state.appCanvasRegion (pickableScenes state) dragAction (ScreenPos mousePos)
                | otherwise = Nothing
         in state{appDrag = mDrag}
update state MouseReleased =
    case state.appDrawing of
        Just pts | length pts >= 3 -> finishDrawing state (NE.reverse pts)
        _ -> state{appDrag = Nothing, appDrawing = Nothing}
-- time tick
update state (Tick dt)
    | state.appPaused || isJust state.appDrag = state
    | otherwise =
        let t' = state.appTime + dt * state.appSpeed
            pannedState = state{appTime = t', appCurves = fmap (`rebuildEntry` t') state.appCurves}

            -- recalculate hover every single frame as the arms rotate
            hovered =
                if pointInCanvas pannedState.appCanvasRegion pannedState.appMousePos
                    then findHover pannedState.appCanvasRegion (pickableScenes pannedState) (ScreenPos pannedState.appMousePos)
                    else Nothing
         in pannedState{appHover = hovered}
update state Quit = state{quitRequested = True}

handleKeypress :: AppState -> SDL.Keycode -> AppState
handleKeypress state key = case key of
    SDL.KeycodeSpace -> togglePaused state
    SDL.KeycodeP -> togglePaused state
    SDL.KeycodeComma -> adjustSpeed (* 0.8) state
    SDL.KeycodeLess -> adjustSpeed (* 0.8) state
    SDL.KeycodePeriod -> adjustSpeed (* 1.25) state
    SDL.KeycodeGreater -> adjustSpeed (* 1.25) state
    SDL.KeycodeMinus -> adjustSpeed (subtract 0.05) state
    SDL.KeycodeEquals -> adjustSpeed (+ 0.05) state
    _ -> state

togglePaused :: AppState -> AppState
togglePaused state = state{appPaused = not state.appPaused}

adjustSpeed :: (Double -> Double) -> AppState -> AppState
adjustSpeed f state =
    state{appSpeed = clamp 0.01 3.0 (f state.appSpeed)}

isCtrlKey :: SDL.Keycode -> Bool
isCtrlKey k = k == SDL.KeycodeLCtrl || k == SDL.KeycodeRCtrl

-- | compile the drawing into an actual curve and add it to the state
finishDrawing :: AppState -> NonEmpty (Float, Float) -> AppState
finishDrawing state screenPts =
    let canvasVT = ViewTransform (Vec (realToFrac panX) (realToFrac panY)) state.appCanvasZoom
        (panX, panY) = state.appCanvasPan
        worldPts =
            [ let v = localCoords state.appCanvasRegion canvasVT (ScreenPos pt)
               in (v.x, v.y)
            | pt <- NE.toList screenPts
            ]
        n = fromIntegral Double (length worldPts)
        cx = sum (map fst worldPts) / n
        cy = sum (map snd worldPts) / n
        centered = [(x - cx, y - cy) | (x, y) <- worldPts]
        smoothed = interpolate 128 centered
        colourIndex = Map.size state.appCurves `mod` length palette
        colour = palette !! colourIndex -- obviously safe
        numTerms = 32
        newCurve = placeCurve (Vec cx cy) colour True (fourierCurve smoothed numTerms)
        nextId =
            if Map.null state.appCurves
                then CurveId 0
                else let CurveId k = fst (Map.findMax state.appCurves) in CurveId (k + 1)
        entry =
            (mkCurveEntry newCurve state.appTime)
                { ceSourcePoints = Just smoothed
                , ceNumTerms = numTerms
                }
     in state
            { appCurves = Map.insert nextId entry state.appCurves
            , appDrawing = Nothing
            }



fullCanvasRegion :: (Int, Int) -> CanvasRegion
fullCanvasRegion (winW, winH) =
    CanvasRegion
        { crOrigin = (0, 0)
        , crSize = (fromIntegral Float winW, fromIntegral Float winH)
        }

-- | apply a drag motion, generating a SceneEdit and editing the curve
applyDrag :: AppState -> DragState -> (Float, Float) -> AppState
applyDrag state ds mouse =
    case Map.lookup ds.dsCurveId state.appCurves of
        Nothing -> state
        Just ce ->
            let vt = canvasAdjustedView state ce
                edit = applyDragMotion state.appCanvasRegion ds (ScreenPos mouse) vt
             in case applyEditToEntry state ce edit of
                    Nothing -> state
                    Just (ce', strategy) ->
                        state
                            { appCurves = Map.insert ds.dsCurveId ce' state.appCurves
                            , appStrategy = strategy
                            }

-- | apply a SceneEdit to a CurveEntry, returning the updated entry and any info from the edit
applyEditToEntry :: AppState -> CurveEntry -> Scene.SceneEdit -> Maybe (CurveEntry, ActiveStrategy)
applyEditToEntry state ce edit =
    case (ce.cePlaced.cdState, state.appStrategy) of
        (SomeCurveState cs, ActiveStrategy strat _oldInfo) -> do
            (cs', info) <- Scene.applyEditWithInfo strat edit cs
            let pc' = rebuildCurveDisplay ce.cePlaced{cdState = SomeCurveState cs'}
                ce' = rebuildEntry ce{cePlaced = pc'} state.appTime
            pure (ce', ActiveStrategy strat (Just info))
