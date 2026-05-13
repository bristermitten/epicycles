-- | hedgehog generators for AST terms
module Gen where

import AST
import Hedgehog (Gen, Property, discover, forAll, property)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Unembedding.Env qualified as Ue
import Utils

genClosedExpr :: Gen (AST Numbered '[] (SNum Double))
genClosedExpr = genClosedExpr' 3

genClosedExpr' :: Int -> Gen (AST Numbered '[] (SNum Double))
genClosedExpr' 0 = Lit <$> genNonZero
genClosedExpr' n =
  Gen.choice
    [ Lit <$> genNonZero,
      Add <$> genClosedExpr' (n - 1) <*> genClosedExpr' (n - 1),
      Mul <$> genClosedExpr' (n - 1) <*> genClosedExpr' (n - 1),
      Recip <$> genClosedExpr' (n - 1),
      Let <$> genClosedExpr' (n - 1) <*> genOneParamExpr' (n - 1)
    ]

-- | Generate an expression with one free variable
genOneParamExpr :: Gen (AST Numbered '[SNum Double] (SNum Double))
genOneParamExpr = genOneParamExpr' 1

genOneParamExpr' :: Int -> Gen (AST Numbered '[SNum Double] (SNum Double))
genOneParamExpr' 0 = Gen.choice [Lit <$> genNonZero, pure (Param Ue.IxZ)]
genOneParamExpr' n =
  Gen.choice
    [ Lit <$> genNonZero,
      pure (Param Ue.IxZ),
      Add <$> genOneParamExpr' (n - 1) <*> genOneParamExpr' (n - 1),
      Mul <$> genOneParamExpr' (n - 1) <*> genOneParamExpr' (n - 1),
      Recip <$> genOneParamExpr' (n - 1),
      Let <$> genOneParamExpr' (n - 1) <*> genTwoParamExpr' (n - 1)
    ]

-- | Generate an expression with two free variables. 
genTwoParamExpr :: Gen (AST Numbered '[SNum Double, SNum Double] (SNum Double))
genTwoParamExpr = genTwoParamExpr' 1

genTwoParamExpr' :: Int -> Gen (AST Numbered '[SNum Double, SNum Double] (SNum Double))
genTwoParamExpr' 0 = Gen.choice [Lit <$> genNonZero, pure (Param Ue.IxZ), pure (Param (Ue.IxS Ue.IxZ))]
genTwoParamExpr' n =
  Gen.choice
    [ Lit <$> genNonZero,
      pure (Param Ue.IxZ),
      pure (Param (Ue.IxS Ue.IxZ)),
      Add <$> genTwoParamExpr' (n - 1) <*> genTwoParamExpr' (n - 1),
      Mul <$> genTwoParamExpr' (n - 1) <*> genTwoParamExpr' (n - 1),
      Recip <$> genTwoParamExpr' (n - 1)
    ]
