module GUI.Colour (
    Colour,
    toImGuiColour,
    toImGuiVec,
    rgbColour,
    red,
    blue,
    grey,
    transparentBlack,
    white,
    magenta,
    green,
    paleYellow,
    cyan,
    orange,
    purple,
    yellow,
    warmWhite,
    lightGrey,
    darkGrey,
    lightBlue,
    canvasBackground,
    buttonActive,
    buttonActiveHover,
    palette,
)
where

import Data.Bits (Bits (shiftL), (.|.))
import DearImGui (ImVec4 (..))

data Colour = RGBA !Float !Float !Float !Float

-- | converts to the imgui packed word32 format
toImGuiColour :: Colour -> Word32
toImGuiColour (RGBA r g b a) =
    let rI :: Int = round (r * 255)
        gI = round (g * 255)
        bI = round (b * 255)
        aI = round (a * 255)
     in fromIntegral Word32 (rI .|. (gI `shiftL` 8) .|. (bI `shiftL` 16) .|. (aI `shiftL` 24))

toImGuiVec :: Colour -> ImVec4
toImGuiVec (RGBA r g b a) = ImVec4 (realToFrac r) (realToFrac g) (realToFrac b) (realToFrac a)

rgbColour :: Int -> Int -> Int -> Int -> Colour
rgbColour r g b a =
    RGBA
        (fromIntegral Float r / 255)
        (fromIntegral Float g / 255)
        (fromIntegral Float b / 255)
        (fromIntegral Float a / 255)

red :: Colour
red = rgbColour 220 60 60 255

blue :: Colour
blue = rgbColour 115 160 225 100

grey :: Colour
grey = rgbColour 80 80 100 255

transparentBlack :: Colour
transparentBlack = rgbColour 255 255 255 200

white :: Colour
white = rgbColour 220 225 235 255

magenta :: Colour
magenta = rgbColour 255 120 220 255

green :: Colour
green = rgbColour 58 240 46 255

paleYellow :: Colour
paleYellow = rgbColour 255 205 120 210

cyan :: Colour
cyan = rgbColour 40 190 200 255

orange :: Colour
orange = rgbColour 220 140 30 255

purple :: Colour
purple = rgbColour 170 80 220 255

yellow :: Colour
yellow = rgbColour 220 200 40 255

warmWhite :: Colour
warmWhite = rgbColour 255 240 220 255

lightGrey :: Colour
lightGrey = rgbColour 220 225 235 255

darkGrey :: Colour
darkGrey = rgbColour 80 80 100 255

lightBlue :: Colour
lightBlue = rgbColour 80 200 255 255

-- | light background for the canvas
canvasBackground :: Colour
canvasBackground = rgbColour 232 231 231 255
-- canvasBackground = rgbColour 18 24 31 250

buttonActive :: Colour
buttonActive = RGBA 0.2 0.5 0.8 0.5

buttonActiveHover :: Colour
buttonActiveHover = RGBA 0.3 0.6 0.9 0.8

-- | a collection of nice colours for curves
palette :: [Colour]
palette =
    [ red
    , blue
    , cyan
    , orange
    , purple
    , yellow
    ]
