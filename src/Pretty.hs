{-# LANGUAGE UndecidableInstances #-}

module Pretty (
    PrettyCurve (..),
    SyntaxHighlight (..),
    syntaxColour,
    module Prettyprinter,
    docToString,
    prettyToString,
    prettyToText,
)
where

import GUI.Colour
import Prettyprinter (Doc, annotate, defaultLayoutOptions, layoutPretty, (<+>))
import Prettyprinter qualified as PP
import Prettyprinter.Render.String

data SyntaxHighlight
    = HLKeyword
    | HLLiteral
    | HLVariable
    | HLOperator
    | HLParam
    | -- | the parameter actively being edited
      HLDragged
    | -- | the whole epicycle expression being hovered
      HLHover
    | -- | the parameter being hovered
      HLHoverParam
    | HLNone
    deriving (Eq)

syntaxColour :: SyntaxHighlight -> Colour
syntaxColour HLKeyword = purple
syntaxColour HLLiteral = orange
syntaxColour HLVariable = green
syntaxColour HLOperator = darkGrey
syntaxColour HLParam = red
syntaxColour HLDragged = warmWhite
syntaxColour HLNone = darkGrey
syntaxColour HLHover = lightBlue
syntaxColour HLHoverParam = magenta

docToString :: Doc SyntaxHighlight -> String
docToString doc =
    let opts = PP.LayoutOptions (PP.AvailablePerLine 70 1.0)
        tree = layoutPretty opts doc
     in renderString tree

prettyToString :: (PrettyCurve a) => a -> String
prettyToString = docToString . pretty

prettyToText :: (PrettyCurve a) => a -> Text
prettyToText = toText . prettyToString

class PrettyCurve a where
    prettyPrec :: Int -> a -> Doc SyntaxHighlight

    pretty :: a -> Doc SyntaxHighlight
    pretty = prettyPrec 0

instance {-# OVERLAPPABLE #-} (PP.Pretty a) => PrettyCurve a where
    prettyPrec _ = annotate HLNone . PP.pretty
