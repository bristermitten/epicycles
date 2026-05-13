{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- for testing only
{-# OPTIONS_GHC -Wno-orphans #-}

-- | More general property tests for the sns update semantics
module ExprUpdateSpec (spec) where

import AST
import Gen
import Hedgehog (Property, discover, forAll, property)
import Hedgehog qualified as H
import Test.Syd
import Test.Syd.Hedgehog (fromHedgehogGroup)
import Unembedding.Env qualified as Ue
import Update.SnS
import Utils
import Prelude

instance forall phase env t. (ApproxEq t) => Eq (UpdateResult phase env (SNum t)) where
  r1 == r2 =
    approxEq
      (evalExpr r1.updatedEnv r1.updatedExpr)
      (evalExpr r2.updatedEnv r2.updatedExpr)

-- | Check that all results from 'exprUpdate' obey the GetPut law
checkAllResultsGetPut ::
  (DiffEnv env) =>
  -- | environment to use for evaluating the expression
  IEnv env ->
  -- | expression to update
  AST Numbered env (SNum Double) ->
  -- | target value to update to
  Double ->
  H.PropertyT IO ()
checkAllResultsGetPut env expr target = do
  let results = exprUpdate env expr target
  for_
    results
    ( \result -> do
        let actual = evalExpr result.updatedEnv result.updatedExpr
        H.diff actual approxEq target
    )

-- | Check that 'exprUpdate' produces at least one result for the given input.
checkHasResults :: (DiffEnv env) => IEnv env -> AST Numbered env (SNum Double) -> Double -> H.PropertyT IO ()
checkHasResults env expr target = do
  let results = exprUpdate env expr target
  results H./== []

-- | Check that 'exprUpdate' produces no results for the given input.
checkHasNoResults :: (DiffEnv env) => IEnv env -> AST Numbered env (SNum Double) -> Double -> H.PropertyT IO ()
checkHasNoResults env expr target = do
  let results = exprUpdate env expr target
  results H.=== []

spec :: Spec
spec = do
  describe "exprUpdate" $ do
    fromHedgehogGroup propertyTests

propertyTests :: H.Group
propertyTests = $$discover

-- | checks GetPut for any closed expr
prop_getPutClosed :: Property
prop_getPutClosed = property $ do
  expr <- forAll genClosedExpr
  let env = Ue.ENil
  let current = evalExpr env expr
  checkHasResults env expr current
  checkAllResultsGetPut env expr current

-- | checks GetPut for any 1 term expr
prop_getPut1Term :: Property
prop_getPut1Term = property $ do
  v <- forAll genFinite
  expr <- forAll genOneParamExpr
  let env = env1 v
  let current = evalExpr env expr
  checkHasResults env expr current
  checkAllResultsGetPut env expr current

-- | checks GetPut for any 2 term expr
prop_getPut2Term :: Property
prop_getPut2Term = property $ do
  v <- forAll genFinite
  k <- forAll genNonZero
  expr <- forAll genTwoParamExpr
  let env = env2 v k
  let current = evalExpr env expr
  checkHasResults env expr current
  checkAllResultsGetPut env expr current

-- | checks PutGet for any closed expression and finite target
prop_putGet :: Property
prop_putGet = property $ do
  v <- forAll genFinite
  target <- forAll genFinite
  expr <- forAll genClosedExpr
  checkAllResultsGetPut Ue.ENil expr target

-- negative tests for unsolvable cases

-- | 1/x can never equal 0, so Recip with target 0 has no solutions.
prop_recipTargetZeroEmpty :: Property
prop_recipTargetZeroEmpty = property $ do
  v <- forAll genNonZero
  let expr = Recip (Lit v) :: AST Numbered '[] (SNum Double)
  checkHasNoResults Ue.ENil expr 0

-- | 0 * 0 = target has no solutions when target /= 0.
prop_mulZeroZeroEmpty :: Property
prop_mulZeroZeroEmpty = property $ do
  target <- forAll genNonZero
  let expr = Mul (Lit 0) (Lit 0) :: AST Numbered '[] (SNum Double)
  checkHasNoResults Ue.ENil expr target

prop_recipRoundTrip :: Property
prop_recipRoundTrip = property $ do
  v <- forAll genNonZero
  target <- forAll genNonZero
  let expr = Recip (Lit v) :: AST Numbered '[] (SNum Double)
  checkHasResults Ue.ENil expr target
  checkAllResultsGetPut Ue.ENil expr target

-- | exprUpdate on arbitrary one-param expressions terminates and all results are finite
-- -- we deliberately do not check putget for expressions with variables due to the failure cases
-- -- that we reason about separately in the Lean proofs
prop_arbitraryParamTerminates :: Property
prop_arbitraryParamTerminates = property $ do
  expr <- forAll genOneParamExpr
  v <- forAll genNonZero
  let env = env1 v
      current = evalExpr env expr
  if not (isFinite current)
    then H.success
    else do
      target <- forAll genFinite
      let results = exprUpdate env expr target
      for_ results $ \result -> do
        let actual = evalExpr result.updatedEnv result.updatedExpr
        H.assert (isFinite actual)

prop_arbitraryTwoParamTerminates :: Property
prop_arbitraryTwoParamTerminates = property $ do
  expr <- forAll genTwoParamExpr
  v <- forAll genNonZero
  k <- forAll genNonZero
  let env = env2 v k
      current = evalExpr env expr
  if not (isFinite current)
    then H.success
    else do
      target <- forAll genFinite
      let results = exprUpdate env expr target
      for_ results $ \result -> do
        let actual = evalExpr result.updatedEnv result.updatedExpr
        H.assert (isFinite actual)