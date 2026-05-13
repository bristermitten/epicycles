-- | Configuration parameters for the GUI
module GUI.Config (
    clickThresholdSq,
    freqDragSensitivity,
    minRadius,
    traceStepLive,
    uiMargin,
    controlsPanelHeight,
    codePanelWidth,
    controlsPanelWidth,
    minCanvasWidth,
    minCanvasHeight,
    minCanvasZoom,
    maxCanvasZoom,
) where

clickThresholdSq :: Double
clickThresholdSq = 2500

freqDragSensitivity :: Double
freqDragSensitivity = 30.0

minRadius :: Double
minRadius = 1.0

traceStepLive :: Double
traceStepLive = 0.001

uiMargin :: Float
uiMargin = 20

controlsPanelHeight :: Float
controlsPanelHeight = 400

codePanelWidth :: Float
codePanelWidth = 360

controlsPanelWidth :: Float
controlsPanelWidth = 310

minCanvasWidth :: Float
minCanvasWidth = 280

minCanvasHeight :: Float
minCanvasHeight = 220

minCanvasZoom :: Double
minCanvasZoom = 0.2

maxCanvasZoom :: Double
maxCanvasZoom = 5.0
