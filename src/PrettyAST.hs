{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PrettyAST (
    prettyExpr,
    prettyCurveState,
    prettyClosedCurve,
    CodeFocus (..),
)
where

import AST (AST (..), ASTSort (..), BindableNum (prettyLit), CurveExpr, CurveState (..), EpicycleId, EpicycleParam (..), IEnv, Numbered, SortVal (..), evalExpr, numberCurve)
import Pretty (PrettyCurve (..), SyntaxHighlight (..), annotate, (<+>))
import Prettyprinter qualified as PP
import Unembedding.Env qualified as Ue

-- | What part of the code is being hovered or dragged, for syntax highlighting purposes
data CodeFocus
    = -- | nothing is focused
      CFNone
    | -- | hovering over an epicycle, maybe a specific parameter of it
      CFHover EpicycleId (Maybe EpicycleParam)
    | -- | dragging an epicycle parameter
      CFDrag EpicycleId EpicycleParam
    deriving (Eq)

prettyExpr :: Int -> IEnv env -> AST phase env (SNum v) -> PP.Doc SyntaxHighlight
prettyExpr depth env = ppExprPrec depth env precTop

prettyNumbered :: CodeFocus -> Int -> IEnv env -> AST Numbered env SCurve -> PP.Doc SyntaxHighlight
prettyNumbered focus depth env = ppNumberedPrec focus depth env precTop

prettyCurveState :: CodeFocus -> CurveState env -> PP.Doc SyntaxHighlight
prettyCurveState focus cs = prettyNumbered focus 0 cs.envParams cs.curveAST

prettyClosedCurve :: (forall e. (CurveExpr e) => e SCurve) -> PP.Doc SyntaxHighlight
prettyClosedCurve term = prettyCurveState CFNone (CurveState (numberCurve term) Ue.ENil)

ppExprPrec :: Int -> IEnv env -> Int -> AST phase env (SNum v) -> PP.Doc SyntaxHighlight
ppExprPrec _depth _env _p (Lit d) =
    annotate HLLiteral (prettyLit d)
ppExprPrec depth _env _p (Param_ _ idx) =
    annotate HLParam ("x" <> PP.pretty (depth - 1 - Ue.ixToInt idx))
ppExprPrec depth env p (Add a b) =
    parensIf (p > precAdd) $
        ppExprPrec depth env precAddL a
            <+> annotate HLOperator "+"
            <+> ppExprPrec depth env precAddR b
ppExprPrec depth env p (Mul a b) =
    parensIf (p > precMul) $
        ppExprPrec depth env precMulL a
            <+> annotate HLOperator "*"
            <+> ppExprPrec depth env precMulR b
ppExprPrec depth env p (Recip a) =
    parensIf (p > precRecip) $
        annotate HLLiteral "1"
            <+> annotate HLOperator "/"
            <+> ppExprPrec depth env precRecipArg a
ppExprPrec depth env p (Let val body) =
    let varName = annotate HLVariable ("x" <> PP.pretty depth)
     in parensIf (p > precLet) $
            annotate HLKeyword "let"
                <+> varName
                <+> annotate HLOperator "="
                <+> ppExprPrec depth env precTop val
                <+> annotate HLKeyword "in"
                <> PP.hardline
                <> ppExprPrec
                    (depth + 1)
                    (Ue.ECons (VNum (evalExpr env val)) env)
                    precTop
                    body

-- Numbered AST precedence pretty-printer
ppNumberedPrec :: CodeFocus -> Int -> IEnv env -> Int -> AST Numbered env SCurve -> PP.Doc SyntaxHighlight
ppNumberedPrec focus depth env p (Let valExpr body) =
    let varName = annotate HLVariable ("x" <> PP.pretty depth)
        val = evalExpr env valExpr
        bodyEnv = Ue.ECons (VNum val) env
     in parensIf (p > precLet) $
            annotate HLKeyword "let"
                <+> varName
                <+> annotate HLOperator "="
                <+> ppExprPrec depth env precTop valExpr
                <+> annotate HLKeyword "in"
                <> PP.hardline
                <> ppNumberedPrec focus (depth + 1) bodyEnv precTop body
ppNumberedPrec focus depth env _p (Epicycle eid r f ph) =
    let rDoc = ppExprPrec depth env precTop r
        fDoc = ppExprPrec depth env precTop f
        phDoc = ppExprPrec depth env precTop ph
        hlParam p doc = case focus of
            CFDrag fid fp | fid == eid && fp == p -> annotate HLDragged doc
            CFHover hid (Just hp) | hid == eid && hp == p -> annotate HLHoverParam doc
            _ -> doc
        inner =
            annotate HLKeyword "epicycle"
                -- <+> pretty eid
                <+> PP.parens
                    ( hlParam Radius rDoc
                        <> annotate HLOperator ","
                            <+> hlParam Frequency fDoc
                        <> annotate HLOperator ","
                            <+> hlParam Phase phDoc
                    )
     in case focus of
            CFHover hid _ | hid == eid -> annotate HLHover inner
            CFDrag fid _ | fid == eid -> annotate HLHover inner
            _ -> inner
ppNumberedPrec focus depth env p (Append a b) =
    parensIf (p > precAppend) $
        ppNumberedPrec focus depth env precAppendL a
            <> PP.hardline
            <> annotate HLOperator "<>"
                <+> ppNumberedPrec focus depth env precAppendR b


precTop :: Int
precTop = -1

precLet :: Int
precLet = 0

precAppend :: Int
precAppend = 0

precAppendL :: Int
precAppendL = 0

precAppendR :: Int
precAppendR = 1

precAdd :: Int
precAdd = 2

precAddL :: Int
precAddL = 2

precAddR :: Int
precAddR = 3

precMul :: Int
precMul = 4

precMulL :: Int
precMulL = 4

precMulR :: Int
precMulR = 5

precRecip :: Int
precRecip = 6

precRecipArg :: Int
precRecipArg = 7

-- Helpers
parensIf :: Bool -> PP.Doc a -> PP.Doc a
parensIf True = PP.parens
parensIf False = id


-- we have to use an orphan here because otherwise we have cyclic dependency between this and AST
instance PrettyCurve (CurveState env) where
    prettyPrec _ = prettyCurveState CFNone
