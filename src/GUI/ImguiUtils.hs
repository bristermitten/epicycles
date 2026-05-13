module GUI.ImguiUtils where

import Control.Exception (bracket_)
import DearImGui (ImVec2 (..), text)
import DearImGui.Raw qualified as Raw
import DearImGui.Raw.DrawList qualified as DL
import Foreign (Ptr)
import Foreign.C.Types (CInt)
import Foreign.Marshal.Array (withArrayLen)
import Foreign.Marshal.Utils (with)
import GUI.Colour

withVec :: (Float, Float) -> (Ptr ImVec2 -> IO a) -> IO a
withVec (x, y) = with (ImVec2 (realToFrac x) (realToFrac y))

addPolyLine :: DL.DrawList -> [(Float, Float)] -> Colour -> Float -> IO ()
addPolyLine drawList pts colour thickness =
    withArrayLen (map (uncurry ImVec2) pts) $ \n ptr ->
        DL.addPolyLine drawList ptr (fromIntegral CInt n) (toImGuiColour colour) Raw.ImDrawFlags_None (realToFrac thickness)

addCircle :: DL.DrawList -> (Float, Float) -> Float -> Colour -> Int -> Float -> IO ()
addCircle drawList ctr radius colour segments thickness =
    withVec ctr $ \ctrPtr ->
        DL.addCircle drawList ctrPtr (realToFrac radius) (toImGuiColour colour) (fromIntegral CInt segments) (realToFrac thickness)

addCircleFilled :: DL.DrawList -> (Float, Float) -> Float -> Colour -> Int -> IO ()
addCircleFilled drawList ctr radius colour segments =
    withVec ctr $ \ctrPtr ->
        DL.addCircleFilled drawList ctrPtr (realToFrac radius) (toImGuiColour colour) (fromIntegral CInt segments)

addLine :: DL.DrawList -> (Float, Float) -> (Float, Float) -> Colour -> Float -> IO ()
addLine drawList p1 p2 colour thickness =
    withVec p1 $ \ptr1 ->
        withVec p2 $ \ptr2 ->
            DL.addLine drawList ptr1 ptr2 (toImGuiColour colour) (realToFrac thickness)

addRectFilled :: DL.DrawList -> (Float, Float) -> (Float, Float) -> Colour -> IO ()
addRectFilled drawList pMin pMax colour =
    withVec pMin $ \ptrMin ->
        withVec pMax $ \ptrMax ->
            DL.addRectFilled drawList ptrMin ptrMax (toImGuiColour colour) 0 Raw.ImDrawFlags_None

addColouredText :: Colour -> Text -> IO ()
addColouredText colour txt =
    withTextColour colour (text txt)

withTextColour :: Colour -> IO a -> IO a
withTextColour colour action =
    with (toImGuiVec colour) $ \colorPtr ->
        bracket_
            (Raw.pushStyleColor Raw.ImGuiCol_Text colorPtr)
            (Raw.popStyleColor 1)
            action

-- | applies horizontal or vectical spacing
withItemSpacing :: Int -> Int -> IO a -> IO a
withItemSpacing horizontal vertical action =
    with (ImVec2 (fromIntegral Float horizontal) (fromIntegral Float vertical)) $ \spacingPtr ->
        bracket_
            (Raw.pushStyleVar Raw.ImGuiStyleVar_ItemSpacing spacingPtr)
            (Raw.popStyleVar 1)
            action

withVerticalSpacing :: Int -> IO a -> IO a
withVerticalSpacing = withItemSpacing 0

withHorizontalSpacing :: Int -> IO a -> IO a
withHorizontalSpacing horizontal = withItemSpacing horizontal 0

withActiveButtonStyles :: Bool -> IO a -> IO a
withActiveButtonStyles False action = action
withActiveButtonStyles True action =
    with (toImGuiVec buttonActive) $ \activePtr ->
        with (toImGuiVec buttonActiveHover) $ \hoveredPtr ->
            bracket_
                ( Raw.pushStyleColor Raw.ImGuiCol_Button activePtr
                    *> Raw.pushStyleColor Raw.ImGuiCol_ButtonHovered hoveredPtr
                )
                (Raw.popStyleColor 2)
                action
