{-# LANGUAGE LexicalNegation #-}

module Entrypoint (main) where

import AST
import AST.Instances ()
import Alphabet (glyphPoints)
import Compiler (fourierCurve)
import Curve (CurveDisplay (..), makeCurve, placeCurve)
import Data.List ((!!))
import GUI.Colour
import GUI.ImguiMain (runGUI)
import Layout (Layout (..), LayoutResult (..), row, solveLayout)
import Vec (Vec (..))
import Prelude hiding (recip)

main :: IO ()
main = runGUI (989, 1400) scenes

-- | a few example scenes
scenes :: Map Text [CurveDisplay]
scenes =
  fromList
    [ ("Simple", [placeCurve (Vec 0 0) cyan True curveSimple]),
      ("Guilloche", [placeCurve (Vec 0 0) purple True curveGuilloche]),
      ("Snowflake", [placeCurve (Vec 0 0) lightBlue True curveSnowflake]),
      ("Decay", [placeCurve (Vec 0 0) orange True curveSharedParameters]),
      ("Asymmetric", [placeCurve (Vec 0 0) red True asymmetric]),
      ("Hello", layoutText 20 "Hello PLRG")
    ]

curveSimple :: (CurveExpr e) => e SCurve
curveSimple =
  let_ 60 $ \a ->
    epicycle a 1 0
      <> epicycle (a * recip 3) 5 0

curveSnowflake :: (CurveExpr e) => e SCurve
curveSnowflake =
  let_ 60 $ \r ->
    epicycle r 1 0
      <> epicycle (r / 3) (-3) 0
      <> epicycle (r / 9) 9 0
      <> epicycle (r / 27) (-27) 0

curveGuilloche :: (CurveExpr e, Expr e) => e SCurve
curveGuilloche =
  let_ 150 $ \r ->
    epicycle r 1 0
      <> epicycle (r * 0.15) (-4) 0
      <> epicycle (r * 0.12) 201 0
      <> epicycle (r * 0.12) (-196) 0
      <> epicycle (r * 0.04) 400 0

curveSharedParameters :: (CurveExpr e) => e SCurve
curveSharedParameters = 
  let_ 60 $ \a ->
    epicycle a 1 0
      <> epicycle (a * recip 3) 3 0
      <> epicycle (a * recip 5) 5 0
      <> epicycle (a * recip 7) 7 0

asymmetric :: (CurveExpr e) => e SCurve
asymmetric = 
  let_ 0.5 $ \p ->
    epicycle 60 3 p
      <> epicycle 30 (-2) (p * 2)
      <> epicycle 12 7 (p * 3)

-- | create a curve for a single character using a Fourier series with the given number of terms.
fourierAlphabet :: Char -> Int -> (forall e. (CurveExpr e) => e SCurve)
fourierAlphabet c nTerms =
  case glyphPoints c of
    Nothing -> epicycle 0 0 0
    Just pts -> fourierCurve pts nTerms

-- | create a Layout of curves for each character in the word with a reasonable amount of spacing
layoutText :: Int -> String -> [CurveDisplay]
layoutText glyphTerms word =
  let leaves =
        [ Leaf
            ( makeCurve
                (palette !! (i `mod` length palette))
                (i == 0)
                (fourierAlphabet c glyphTerms)
            )
        | (i, c) <- zip [0 ..] word
        ]
      layout = row 10 leaves
   in lrCurves (solveLayout layout)
