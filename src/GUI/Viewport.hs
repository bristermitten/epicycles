-- | The gui view logic
module GUI.Viewport (
    CanvasRegion (..),
    ViewTransform (..),
    viewScale,
    curveToScreen,
    screenToLocal,
    localCoords,
    ScreenPos (..),
    WorldPos (..),
    worldPosDistSquared,
)
where

import Vec (Vec (..), distSquared)

-- | the region of the screen allocated to the canvas, in pixels
data CanvasRegion = CanvasRegion
    { crOrigin :: (Float, Float)
    , crSize :: (Float, Float)
    }

-- | the current view transform of the canvas, encoding panning and zooming
data ViewTransform = ViewTransform
    { vtOffset :: Vec
    , vtScale :: Double
    }

-- | scale factor of the view transform
viewScale :: ViewTransform -> Float
viewScale = realToFrac . vtScale

curveToScreen ::
    CanvasRegion ->
    ViewTransform ->
    Vec ->
    (Float, Float)
curveToScreen region vt pt =
    let (originX, originY) = region.crOrigin
        (canvasW, canvasH) = region.crSize
     in ( originX + canvasW / 2 + realToFrac (vt.vtOffset.x + pt.x * vt.vtScale)
        , originY + canvasH / 2 - realToFrac (vt.vtOffset.y + pt.y * vt.vtScale)
        )

-- | a position, in screen coordinates (pixels)
newtype ScreenPos = ScreenPos (Float, Float) deriving (Show)

-- | a position, in world coordinates (canvas units)
newtype WorldPos = WorldPos Vec deriving (Show, Eq)

worldPosDistSquared :: WorldPos -> WorldPos -> Double
worldPosDistSquared (WorldPos v1) (WorldPos v2) =
    Vec.distSquared v1 v2

{- | Convert a screen position to world coordinates
-}
localCoords :: CanvasRegion -> ViewTransform -> ScreenPos -> Vec
localCoords region vt pos =
    let WorldPos v = screenToLocal region vt pos in v

screenToLocal :: CanvasRegion -> ViewTransform -> ScreenPos -> WorldPos
screenToLocal region vt (ScreenPos (mx, my)) =
    let (originX, originY) = region.crOrigin
        (canvasW, canvasH) = region.crSize
     in WorldPos
            ( Vec
                ((realToFrac mx - realToFrac originX - realToFrac (canvasW / 2) - vt.vtOffset.x) / vt.vtScale)
                ((realToFrac originY + realToFrac (canvasH / 2) - realToFrac my - vt.vtOffset.y) / vt.vtScale)
            )
