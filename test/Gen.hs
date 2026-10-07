-- | hedgehog generators for AST terms
module Gen where

import AST
import Hedgehog (Gen)
import Hedgehog.Gen qualified as Gen

import ContextualEmbeddings
import Utils

genClosedExpr :: Gen (AST Numbered Empty (SNum Double))
genClosedExpr = genClosedExpr' 3

genClosedExpr' :: Int -> Gen (AST Numbered Empty (SNum Double))
genClosedExpr' 0 = Lit <$> genNonZero
genClosedExpr' n =
    Gen.choice
        [ Lit <$> genNonZero
        , Add <$> genClosedExpr' (n - 1) <*> genClosedExpr' (n - 1)
        , Mul <$> genClosedExpr' (n - 1) <*> genClosedExpr' (n - 1)
        , Recip <$> genClosedExpr' (n - 1)
        , Let <$> genClosedExpr' (n - 1) <*> genOneParamExpr' (n - 1)
        ]

-- | Generate an expression with one free variable
genOneParamExpr :: Gen (AST Numbered (Empty :/: SNum Double) (SNum Double))
genOneParamExpr = genOneParamExpr' 1

genOneParamExpr' :: Int -> Gen (AST Numbered (Empty :/: SNum Double) (SNum Double))
genOneParamExpr' 0 = Gen.choice [Lit <$> genNonZero, pure (Param IxZ)]
genOneParamExpr' n =
    Gen.choice
        [ Lit <$> genNonZero
        , pure (Param IxZ)
        , Add <$> genOneParamExpr' (n - 1) <*> genOneParamExpr' (n - 1)
        , Mul <$> genOneParamExpr' (n - 1) <*> genOneParamExpr' (n - 1)
        , Recip <$> genOneParamExpr' (n - 1)
        , Let <$> genOneParamExpr' (n - 1) <*> genTwoParamExpr' (n - 1)
        ]

-- | Generate an expression with two free variables.
genTwoParamExpr :: Gen (AST Numbered (Empty :/: SNum Double :/: SNum Double) (SNum Double))
genTwoParamExpr = genTwoParamExpr' 1

genTwoParamExpr' :: Int -> Gen (AST Numbered (Empty :/: SNum Double :/: SNum Double) (SNum Double))
genTwoParamExpr' 0 = Gen.choice [Lit <$> genNonZero, pure (Param IxZ), pure (Param (IxS IxZ))]
genTwoParamExpr' n =
    Gen.choice
        [ Lit <$> genNonZero
        , pure (Param IxZ)
        , pure (Param (IxS IxZ))
        , Add <$> genTwoParamExpr' (n - 1) <*> genTwoParamExpr' (n - 1)
        , Mul <$> genTwoParamExpr' (n - 1) <*> genTwoParamExpr' (n - 1)
        , Recip <$> genTwoParamExpr' (n - 1)
        ]
