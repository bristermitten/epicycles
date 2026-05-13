{-# LANGUAGE BlockArguments #-}

-- | the code panel that displays in the gui
module GUI.ImguiCodePanel (renderCodePanel) where

import Curve (CurveDisplay (..), SomeCurveState (..))
import Data.Text qualified as Text
import DearImGui (text)
import DearImGui.Raw qualified as Raw
import GUI.ImguiInteraction (CurveId (..))
import GUI.ImguiUtils (addColouredText, withVerticalSpacing)
import Pretty (SyntaxHighlight (..), syntaxColour)
import PrettyAST (CodeFocus (..), prettyCurveState)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Util.SimpleDocTree (SimpleDocTree (..), treeForm)

renderCodePanel :: Maybe (CurveId, CodeFocus) -> [CurveDisplay] -> IO ()
renderCodePanel _ [] = text "No curves"
renderCodePanel maybeFocus curves = do
    withVerticalSpacing 4 do
        for_ (zip [0 ..] curves) renderOne
  where
    renderOne (i, pc) = case pc.cdState of
        SomeCurveState cs -> do
            let curveFocus = case maybeFocus of
                    Just (CurveId cid, focus) | cid == i -> focus
                    _ -> CFNone
                doc = prettyCurveState curveFocus cs
                opts = PP.LayoutOptions (PP.AvailablePerLine 60 1.0)
                tree = treeForm (PP.layoutPretty opts doc)
            addColouredText pc.cdColor ("-- curve " <> show i)
            for_ (treeToLines tree) renderSpans

type TextSpan = (SyntaxHighlight, Text.Text)

type TextLine = [TextSpan]

-- | Convert a 'SimpleDocTree' of syntax-highlighted text into lines of coloured spans.
treeToLines :: SimpleDocTree SyntaxHighlight -> [TextLine]
treeToLines tree =
    let (cur, acc) = go False False False HLNone ([], []) tree
     in reverse (reverse cur : acc)
  where
    go dragged hoverParam hovered hl (cur, acc) node =
        case node of
            STEmpty ->
                (cur, acc)
            STChar c ->
                ((effectiveHighlight, one c) : cur, acc)
            STText _ t ->
                ((effectiveHighlight, t) : cur, acc)
            STLine n ->
                let indent = [(HLNone, Text.replicate n " ") | n > 0]
                 in (indent, reverse cur : acc)
            STAnn ann t ->
                go
                    (dragged || ann == HLDragged)
                    (hoverParam || ann == HLHoverParam)
                    (hovered || ann == HLHover)
                    ann
                    (cur, acc)
                    t
            STConcat ts ->
                foldl' (go dragged hoverParam hovered hl) (cur, acc) ts
      where
        -- resolve the effective syntax highlight based on the priorities
        effectiveHighlight
            | dragged = HLDragged
            | hoverParam = HLHoverParam
            | hovered = HLHover
            | otherwise = hl

-- | Render a list of coloured spans as one ImGui line
renderSpans :: [(SyntaxHighlight, Text.Text)] -> IO ()
renderSpans [] = text ""
renderSpans spans = go True spans
  where
    go _ [] = pass
    go firstText ((hl, t) : rest) = do
        unless firstText Raw.sameLine
        addColouredText (syntaxColour hl) t
        go False rest
