{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

-- | Stress tests for the SnS algorithm's ambiguity behaviour.
-- we construct deliberately ambiguous (or unambiguous) expressions and make assertations about the
-- number of candidates returned, and that all candidates round-trip correctly
module AmbiguityStressSpec (spec) where

import AST
import Data.List (foldl1')
import Hedgehog (Property, discover, forAll, property, (===))
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Scene (evalScene, vsEpicycleOrder)
import Test.Syd
import Test.Syd.Hedgehog (fromHedgehogGroup)
import Unembedding.Env qualified as Ue
import Update.SnS
import Update.SnS.Heuristic (curveUpdateWithInfo)
import Update.Types qualified as Update (EpicycleParam (..))
import Utils

-- | assert the exact number of update candidates returned with hspec
requireCandidates :: (HasCallStack) => Maybe (UpdateInfo env) -> Int -> Expectation
requireCandidates Nothing _ = expectationFailure "update returned Nothing"
requireCandidates (Just (UpdateInfo _ _ l)) n = length l `shouldBe` n

-- | assert the exact number of update candidates returned with Hedgehog
requireCandidatesProp :: (HasCallStack) => Maybe (UpdateInfo env) -> Int -> H.PropertyT IO ()
requireCandidatesProp Nothing _ = H.annotate "update returned Nothing" *> H.failure
requireCandidatesProp (Just (UpdateInfo _ _ l)) n = length l === n

-- | Build a left-leaning Add tree
addTree :: (BindableNum n) => [AST phase env (SNum n)] -> AST phase env (SNum n)
addTree = foldl1' Add

spec :: Spec
spec = describe "Ambiguity stress" $ do
  constructedAmbiguous
  constructedUnambiguous
  fromHedgehogGroup propertyTests

-- | hand-constructed expressions where we can predict the exact number of candidates returned by the update algorithm
constructedAmbiguous :: Spec
constructedAmbiguous = describe "Constructed ambiguous expressions" $ do
  it "Add(Lit, Lit) yields exactly 2 candidates" $ do
    let e = Add (Lit (1 :: Double)) (Lit 2)
    length (exprUpdate emptyEnv e 10) `shouldBe` 2

  it "Mul(Lit, Lit) yields exactly 2 candidates" $ do
    let e = Mul (Lit (3 :: Double)) (Lit 4)
    length (exprUpdate emptyEnv e 24) `shouldBe` 2

  it "Mul with a zero branch loses that candidate" $ do
    let e = Mul (Lit (0 :: Double)) (Lit 5)
    length (exprUpdate emptyEnv e 10) `shouldBe` 1

  it "Recip(Add(Lit,Lit)) yields 2 candidates" $ do
    let e = Recip (Add (Lit (1 :: Double)) (Lit 2))
    length (exprUpdate emptyEnv e 0.1) `shouldBe` 2

  it "Add(Add(Lit,Lit), Lit) yields exactly 3 candidates" $ do
    let e = Add (Add (Lit (1 :: Double)) (Lit 2)) (Lit 3)
    length (exprUpdate emptyEnv e 100) `shouldBe` 3

  it "Add(Add(Lit,Lit), Add(Lit,Lit)) yields exactly 4 candidates" $ do
    let e = Add (Add (Lit (1 :: Double)) (Lit 2)) (Add (Lit 3) (Lit 4))
    length (exprUpdate emptyEnv e 100) `shouldBe` 4

  it "Balanced Add tree of 8 lits yields 8 candidates" $ do
    let e = addTree (map Lit [1, 2, 3, 4, 5, 6, 7, 8 :: Double])
    length (exprUpdate emptyEnv e 999) `shouldBe` 8

  it "Let with non-linear body is rejected by all candidates" $ do
    let e = Let (Lit (5 :: Double)) (Add (Param Ue.IxZ) (Param Ue.IxZ))
    length (exprUpdate emptyEnv e 100) `shouldBe` 0

  it "Let with linear body produces exactly 2 candidates" $ do
    let e = Let (Lit (5 :: Double)) (Mul (Param Ue.IxZ) (Lit 2))
    -- we can either update the binding, or the 2, so 2 candidates
    length (exprUpdate emptyEnv e 20) `shouldSatisfy` (== 2)

-- | hand-constructed unambiguous expression
constructedUnambiguous :: Spec
constructedUnambiguous = describe "Constructed unambiguous expressions" $ do
  it "Lit alone yields exactly 1 candidate" $ do
    length (exprUpdate emptyEnv (Lit (3 :: Double)) 7) `shouldBe` 1

  it "Param alone yields exactly 1 candidate" $ do
    length (exprUpdate (env1 3) (Param Ue.IxZ) 7) `shouldBe` 1

  it "Recip(Lit) yields exactly 1 candidate" $ do
    length (exprUpdate emptyEnv (Recip (Lit (2 :: Double))) 0.25) `shouldBe` 1

  it "Curve update on epicycle yields exactly 1 candidate (radius)" $ do
    let cs = mkState (epicycle (lit 100) (lit 1) (lit 0))
    requireCandidates (curveUpdateWithInfo @Update.Radius (firstEpiId cs) 200 cs) 1

  it "Curve update on epicycle yields exactly 1 candidate (frequency)" $ do
    let cs = mkState (epicycle (lit 100) (lit 1) (lit 0))
    requireCandidates (curveUpdateWithInfo @Update.Frequency (firstEpiId cs) 5 cs) 1

  it "Curve update on epicycle yields exactly 1 candidate (phase)" $ do
    let cs = mkState (epicycle (lit 100) (lit 1) (lit 0))
    requireCandidates (curveUpdateWithInfo @Update.Phase (firstEpiId cs) 1.5 cs) 1

propertyTests :: H.Group
propertyTests = $$discover


-- | updating a parameter of an epicycle whose parameters are only literals should yield exactly 1 candidate
prop_realisticCurveRadius_oneCandidate :: Property
prop_realisticCurveRadius_oneCandidate = property $ do
  r <- forAll genPositiveRadius
  f <- forAll genFreq
  p <- forAll genFinite
  targetR <- forAll genPositiveRadius
  let cs = mkState (epicycle (litR r) (lit f) (litR p))
  requireCandidatesProp (curveUpdateWithInfo @Update.Radius (firstEpiId cs) (toRational targetR) cs) 1

  targetF <- forAll genFreq
  requireCandidatesProp (curveUpdateWithInfo @Update.Frequency (firstEpiId cs) targetF cs) 1

  targetP <- forAll genFinite
  requireCandidatesProp (curveUpdateWithInfo @Update.Phase (firstEpiId cs) (toRational targetP) cs) 1


-- | the best update of updating the radius of an epicycle whose radius is a shared parameter
-- should be to update that parameter, and should have a 'LocalParam' depth
prop_sharedRadiusCurve_classifiedAsLocalParam :: Property
prop_sharedRadiusCurve_classifiedAsLocalParam = property $ do
  r <- forAll genPositiveRadius
  target <- forAll genPositiveRadius
  let cs =
        mkState
          ( let_ (litR r) $ \x ->
              epicycle x (lit 1) (lit 0)
                <> epicycle x (lit 3) (lit 0)
          )

  case curveUpdateWithInfo @Update.Radius (firstEpiId cs) (toRational target) cs of
    Nothing -> H.annotate "update returned Nothing" *> H.failure
    Just (UpdateInfo _ depth _) -> depth === if target == r then NoEdit else LocalParam

-- | if we generate some tree of Adds with n distinct literals, 
-- then updating the overall expression to some target should have n candidates
prop_addTree_candidatesEqualsLeafCount :: Property
prop_addTree_candidatesEqualsLeafCount = property $ do
  n <- forAll (Gen.int (Range.linear 2 6))
  leaves <- forAll (Gen.list (Range.singleton n) genFinite)
  delta <- forAll (Gen.filter (/= 0) genFinite)

  let current = sum leaves
      target = current + delta
      e = addTree (map Lit leaves)

  H.annotate $ "leaves=" <> show leaves <> " target=" <> show target
  length (exprUpdate emptyEnv e target) === n

-- | and all candidates should round-trip correctly to the target value (i.e. GetPut)
prop_allCandidatesGetPut_addTree :: Property
prop_allCandidatesGetPut_addTree = property $ do
  n <- forAll (Gen.int (Range.linear 2 5))
  leaves <- forAll (Gen.list (Range.singleton n) genFinite)
  target <- forAll genFinite

  let e = addTree (map Lit leaves)
      rs = exprUpdate emptyEnv e target

  H.annotate $ "candidates: " <> show (length rs)
  for_ rs $ \r -> H.diff (evalExpr r.updatedEnv r.updatedExpr) approxEq target

-- | the same should hold for Mul trees
prop_allCandidatesGetPut_mulPair :: Property
prop_allCandidatesGetPut_mulPair = property $ do
  a <- forAll (Gen.filter (/= 0) genFinite)
  b <- forAll (Gen.filter (/= 0) genFinite)
  target <- forAll genFinite

  let e = Mul (Lit a) (Lit b)
      rs = exprUpdate emptyEnv e target

  for_ rs $ \r -> H.diff (evalExpr r.updatedEnv r.updatedExpr) approxEq target