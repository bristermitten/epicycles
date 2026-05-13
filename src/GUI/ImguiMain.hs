{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedRecordDot #-}

module GUI.ImguiMain (runGUI) where

import AST (EpicycleId, EpicycleParam (..))
import Control.Exception (bracket, bracket_)
import Control.Monad.Managed (managed, managed_, runManaged)
import Curve (CurveDisplay (..))
import Data.Map qualified as Map
import DearImGui hiding (separator)
import DearImGui.OpenGL3
import DearImGui.Raw qualified as Raw
import DearImGui.Raw.Font qualified as Font
import DearImGui.Raw.Font.Config qualified as FontConfig
import DearImGui.Raw.Font.GlyphRanges qualified as GlyphRanges
import DearImGui.SDL
import DearImGui.SDL.OpenGL (sdl2InitForOpenGL)
import Foreign.C (CInt)
import Foreign.C.String (withCString)
import Foreign.Marshal.Utils (fromBool, with)
import GUI.Config (codePanelWidth, controlsPanelWidth, uiMargin)
import GUI.ImguiCodePanel (renderCodePanel)
import GUI.ImguiInteraction (CurveId (..), DragParam (..), DragState (..), hoverParamOf)
import GUI.ImguiRender (renderDrawingPath, renderScenes)
import GUI.ImguiUtils
import GUI.State
import GUI.Util
import Graphics.GL
import Pretty (prettyToText)
import PrettyAST (CodeFocus (..))
import SDL qualified
import SDL.Video.OpenGL (Mode (Normal), Profile (Core))
import Scene (StrategyMetrics (..), VisualEpicycle (..), VisualScene (..))
import Scene qualified
import System.Directory (doesFileExist)
import Update.Delta (Conflict (..), ResolutionType (..))
import Update.SnS

codeFontPixels :: Float
codeFontPixels = 18

codeFontCandidates :: [FilePath]
codeFontCandidates =
  [ "/System/Library/Fonts/Menlo.ttc",
    "/System/Library/Fonts/Monaco.ttf",
    "/System/Library/Fonts/SFNSMono.ttf"
  ]

initCodeFont :: IO Font.Font
initCodeFont = do
  config <- FontConfig.new
  FontConfig.setOversampleH config 2
  FontConfig.setOversampleV config 2
  FontConfig.setPixelSnapH config (fromBool True)
  let ranges = GlyphRanges.getBuiltin GlyphRanges.Latin
  mPath <- findFirstExisting codeFontCandidates
  font <- case mPath of
    Just path ->
      withCString path $ \cpath ->
        Font.addFontFromFileTTF cpath (realToFrac codeFontPixels) config ranges
    Nothing -> Font.addFontDefault
  Font.buildFontAtlas
  FontConfig.destroy config
  pure font

findFirstExisting :: [FilePath] -> IO (Maybe FilePath)
findFirstExisting [] = pure Nothing
findFirstExisting (p : ps) = do
  exists <- doesFileExist p
  if exists then pure (Just p) else findFirstExisting ps

runGUI :: (Int, Int) -> Map Text [CurveDisplay] -> IO ()
runGUI (winW, winH) scenes = do
  SDL.initializeAll

  let t0 = 2 * pi - 0.5
      (actualW, actualH) = (max 1680 winW, max 1040 winH)

      -- render the first scene by default
      (initialCurves, initialSceneName) = case Map.toList scenes of
        ((name, pcs) : _) -> (pcs, name)
        [] -> ([], "")

  stateRef <-
    newIORef
      AppState
        { appCurves = initialCurveMap initialCurves t0,
          appTime = t0,
          appPaused = True,
          appSpeed = 1,
          appWindowSize = (actualW, actualH),
          appCanvasRegion = fullCanvasRegion (actualW, actualH),
          appCanvasPan = (0, 0),
          appCanvasZoom = 1.0,
          appShiftHeld = False,
          appDrag = Nothing,
          appHover = Nothing,
          appMousePos = (0, 0),
          appScenes = scenes,
          appScene = initialSceneName,
          appCtrlHeld = False,
          appDrawing = Nothing,
          appStrategy = initialActiveStrategy,
          appLastSimplifyInfo = Nothing,
          quitRequested = False
        }

  runManaged do
    let glConfig = SDL.defaultOpenGL {SDL.glProfile = Core Normal 3 2}
        config =
          SDL.defaultWindow
            { SDL.windowGraphicsContext = SDL.OpenGLContext glConfig,
              SDL.windowInitialSize = SDL.V2 (fromIntegral CInt actualW) (fromIntegral CInt actualH),
              SDL.windowResizable = True,
              SDL.windowHighDPI = True
            }
    window <- managed $ bracket (SDL.createWindow "Epicycles" config) SDL.destroyWindow
    glContext <- managed $ bracket (SDL.glCreateContext window) SDL.glDeleteContext

    _ <- managed $ bracket createContext destroyContext
    managed_ $ bracket_ (sdl2InitForOpenGL window glContext) sdl2Shutdown
    managed_ $ bracket_ openGL3Init openGL3Shutdown
    codeFont <- liftIO initCodeFont

    liftIO do
      SDL.V2 rw rh <- SDL.get (SDL.windowSize window)
      modifyIORef' stateRef \s ->
        s
          { appWindowSize = (fromIntegral Int rw, fromIntegral Int rh),
            appCanvasRegion = fullCanvasRegion (fromIntegral Int rw, fromIntegral Int rh)
          }
      mainLoop window codeFont stateRef

mainLoop :: SDL.Window -> Font.Font -> IORef AppState -> IO ()
mainLoop window codeFont stateRef = loop
  where
    loop = do
      events <- pollEventsWithImGui
      state <- readIORef stateRef

      let shouldQuit = any ((== SDL.QuitEvent) . SDL.eventPayload) events || state.quitRequested
          sdlMessages = mapMaybe translateSDLEvent events

      unless shouldQuit do
        beforeFrame <- SDL.time

        openGL3NewFrame
        sdl2NewFrame
        newFrame
        styleColorsLight

        imguiMessages <- buildUI codeFont state

        afterFrame <- SDL.time
        let dt = afterFrame - beforeFrame
            tickMessage = Tick dt
            allMsgs = sdlMessages <> imguiMessages <> [tickMessage]

        modifyIORef' stateRef \s -> foldl' updateAppState s allMsgs

        glClear GL_COLOR_BUFFER_BIT
        render
        openGL3RenderDrawData =<< getDrawData
        SDL.glSwapWindow window
        loop

-- | compute the code panel focus based on the current hover and drag state.
computeCodeFocus ::
  AppState ->
  -- | the currently focused curve and parameter, if any
  Maybe (CurveId, CodeFocus)
computeCodeFocus state = case state.appDrag of
  Just ds ->
    Just
      ( ds.dsCurveId,
        CFDrag ds.dsEpicycleId $ case ds.dsParam of
          DragRadius {} -> Radius
          DragFreq {} -> Frequency
          DragPhase {} -> Phase
      )
  Nothing -> case state.appHover of
    Just (cid, eid, ht) -> Just (cid, CFHover eid (Just (hoverParamOf ht)))
    Nothing -> Nothing

buildUI :: Font.Font -> AppState -> IO [Msg]
buildUI codeFont state = do
  let (winW, winH) = bimap (fromIntegral Float) (fromIntegral Float) state.appWindowSize
      canvasRegion = fullCanvasRegion state.appWindowSize
      scenesWithOffsets =
        Map.elems $
          Map.mapWithKey
            (\cid ce -> (cid, canvasAdjustedView state ce, ce.ceScene, ce.cePlaced.cdColor, ce.cePlaced.cdShowConstruction))
            state.appCurves

  renderScenes canvasRegion scenesWithOffsets state.appHover state.appDrag
  renderDrawingPath state.appDrawing

  withPanel "Code" (uiMargin, uiMargin) (codePanelWidth, winH - 2 * uiMargin) $
    withFont codeFont $
      renderCodePanel (computeCodeFocus state) (map cePlaced (Map.elems state.appCurves))

  let ctrlX = winW - uiMargin - controlsPanelWidth
      ctrlH = winH - 2 * uiMargin

  actionsRef <- newIORef []
  withPanel "Controls" (ctrlX, uiMargin) (controlsPanelWidth, ctrlH) $ do
    acts <- renderControls state
    modifyIORef' actionsRef (++ acts)

  readIORef actionsRef

renderControls :: AppState -> IO [Msg]
renderControls state = do
  sceneActs <- renderSceneSelector state
  playActs <- renderPlayback state
  visActs <- renderVisibility state
  stratActs <- renderStrategySelector state
  renderUpdateInfo state
  renderHoverInfo state
  renderShortcuts
  pure $ mconcat [sceneActs, playActs, visActs, stratActs]

renderSceneSelector :: AppState -> IO [Msg]
renderSceneSelector state = do
  text "Scene"
  separator
  acts <- concat <$> mapM renderSceneButton (Map.toList state.appScenes)
  separator
  pure acts
  where
    renderSceneButton (name, _) = do
      clicked <- withActiveButtonStyles (name == state.appScene) (button name)
      pure [UILoadScene name | clicked]

renderPlayback :: AppState -> IO [Msg]
renderPlayback state = do
  text "Playback"
  separator

  toggled <- button $ if state.appPaused then "Play  [Space]" else "Pause [Space]"
  sameLine
  resetClicked <- button "Reset"

  speedChanged <- dragSpeedControl "Speed" state.appSpeed 0.01 0.1 3.0
  text $ "time  " <> showFixed 3 state.appTime
  text $ "speed " <> showFixed 2 state.appSpeed <> "x"
  text $ "zoom  " <> showFixed 2 state.appCanvasZoom <> "x"
  scrubbedTime <- dragSpeedControl "Timeline" state.appTime 0.01 0 (2 * pi)

  pure $
    mconcat
      [ [UITogglePaused | toggled],
        [UIResetTime | resetClicked],
        [UISetSpeed s | Just s <- [speedChanged]],
        [UISetTime t | Just t <- [scrubbedTime]]
      ]

renderVisibility :: AppState -> IO [Msg]
renderVisibility state = do
  separator
  text "Visibility"
  concat <$> mapM (renderCurveToggle state) (Map.toList state.appCurves)

renderShortcuts :: IO ()
renderShortcuts = do
  separator
  text "Shortcuts"
  text "Space/P  Play/Pause"
  text "Esc      Quit\nWheel    Zoom\nShift+drag  Pan"
  separator
  text "Editing"
  text "Left drag   Radius / Phase\nRight drag  Frequency\nCtrl+drag   Draw new curve"

renderCurveToggle :: AppState -> (CurveId, CurveEntry) -> IO [Msg]
renderCurveToggle _state (cid, ce) = do
  visibleRef <- newIORef ce.cePlaced.cdShowConstruction
  changed <- checkbox ("Curve " <> showCurveId cid <> " construction") visibleRef
  if changed
    then pure . UIToggleCurveConstruction cid <$> readIORef visibleRef
    else pure []

dragSpeedControl :: Text -> Double -> Double -> Double -> Double -> IO (Maybe Double)
dragSpeedControl label value initialValue minV maxV = do
  ref <- newIORef (realToFrac value :: Float)
  changed <- dragFloat label ref (realToFrac initialValue) (realToFrac minV) (realToFrac maxV)
  if changed then Just . realToFrac <$> readIORef ref else pure Nothing

renderStrategySelector :: AppState -> IO [Msg]
renderStrategySelector state = do
  separator
  text "Strategy"
  acts1 <- stratButton Scene.heuristicStrategy
  acts2 <- stratButton Scene.naiveStrategy
  acts3 <- stratButton Scene.fuseDMStrategy
  pure $ acts1 ++ acts2 ++ acts3
  where
    stratButton :: Scene.UpdateStrategy strat -> IO [Msg]
    stratButton strat = do
      let name = strat.usName
          isActive = case state.appStrategy of
            ActiveStrategy activeStrat _ ->
              activeStrat.usName == name
      when isActive do
        with (ImVec4 0.2 0.5 0.8 0.5) (Raw.pushStyleColor Raw.ImGuiCol_Button)
        with (ImVec4 0.3 0.6 0.9 0.8) (Raw.pushStyleColor Raw.ImGuiCol_ButtonHovered)
      clicked <- button name
      when isActive do
        Raw.popStyleColor 2
      pure [UISetStrategy (ActiveStrategy strat Nothing) | clicked]

prettyDepth :: EditDepth -> Text
prettyDepth d = case d of
  NoEdit -> "no change (already correct)"
  LitEdit -> "literal value changed"
  LocalParam -> "local variable changed"
  OuterParam n -> "shared variable changed (depth " <> show n <> ")"
  ImpossibleEdit -> "impossible"

renderUpdateInfo :: AppState -> IO ()
renderUpdateInfo state = do
  separator
  text "Last Edit"
  case state.appStrategy of
    ActiveStrategy _strat editInfo ->
      case editInfo of
        Nothing -> text "  (drag to edit)"
        Just (info :: Scene.EditInfo strat) -> do
          text $ "  " <> info.eiStrategy
          case info.eiMetrics of
            SearchMetrics depth alts -> do
              text $ "  What changed: " <> prettyDepth depth
              text $ "  Alternatives: " <> unlines (show <$> alts)
            FuseDMMetrics conflicts -> do
              let numConflicts = length conflicts
              text $ "  Conflicts Detected: " <> show numConflicts
              unless (null conflicts) $ do
                let suffixSaved = length $ filter (\c -> c.clResolution == CleanSuffixSplit) conflicts
                    embedCount = length $ filter (\c -> c.clResolution == TotalDisagreement) conflicts

                text $ "  Resolved via Suffix Split: " <> show suffixSaved
                text $ "  AST Embeddings: " <> show embedCount

renderHoverInfo :: AppState -> IO ()
renderHoverInfo state = do
  separator
  case state.appDrag of
    Just ds -> do
      let param = case ds.dsParam of
            DragRadius {} -> Radius
            DragFreq {} -> Frequency
            DragPhase {} -> Phase
      text $
        "Editing: "
          <> prettyToText ds.dsEpicycleId
          <> " "
          <> show param
      renderEpicycleStats state ds.dsCurveId ds.dsEpicycleId
    Nothing -> case state.appHover of
      Nothing -> text "Hovering: (nothing)"
      Just (cid, eid, ht) -> do
        let param = hoverParamOf ht
        text $
          "Hovering: "
            <> prettyToText eid
            <> " "
            <> show param
        renderEpicycleStats state cid eid

-- | Show numeric parameter values for the given epicycle, if it can be located
renderEpicycleStats :: AppState -> CurveId -> EpicycleId -> IO ()
renderEpicycleStats state cid eid =
  case Map.lookup cid state.appCurves of
    Nothing -> pass
    Just ce -> case Map.lookup eid ce.ceScene.vsEpicycles of
      Nothing -> pass
      Just ve ->
        text $
          "  r="
            <> showFixed 2 ve.veRadius
            <> "  f="
            <> show ve.veFreq
            <> "  phase="
            <> showFixed 2 ve.vePhase

withPanel :: Text -> (Float, Float) -> (Float, Float) -> IO () -> IO ()
withPanel title (x, y) (w, h) act = do
  with (ImVec2 x y) $ \pos -> Raw.setNextWindowPos pos Raw.ImGuiCond_Always Nothing
  with (ImVec2 w h) $ \size -> Raw.setNextWindowSize size Raw.ImGuiCond_Always
  setNextWindowBgAlpha 0.88
  withWindowOpen title act

showCurveId :: CurveId -> Text
showCurveId (CurveId n) = show n

separator :: IO ()
separator = Raw.separator
