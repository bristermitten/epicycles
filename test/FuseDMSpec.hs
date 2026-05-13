{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- for testing only
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module FuseDMSpec (spec) where

import AST
import AST.Instances ()
import Control.Monad.Writer (runWriter)
import Data.List qualified as List
import Data.Map qualified as Map
import Delta
import Hedgehog (Property, discover, forAll, property)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Scene
import Test.Syd
import Test.Syd.Hedgehog (fromHedgehogGroup)
import Unembedding.Env qualified as Ue
import Update.Delta (Conflict (..), backwardEvalCurve)
import Utils
import Prelude

epiRadius :: CurveState '[] -> EpicycleId -> Double
epiRadius cs eid = veRadius (vsEpicycles (evalScene cs 0) Map.! eid)

epiFreq :: CurveState '[] -> EpicycleId -> Int
epiFreq cs eid = veFreq (vsEpicycles (evalScene cs 0) Map.! eid)

epiPhase :: CurveState '[] -> EpicycleId -> Double
epiPhase cs eid = vePhase (vsEpicycles (evalScene cs 0) Map.! eid)

runFuseDM :: SceneEdit -> CurveState '[] -> (CurveState '[], [Conflict])
runFuseDM edit cs@(CurveState ast env) =
  let scene = evalScene cs 0
      (eid, curveDelta) = case edit of
        SetRadius id newR ->
          let curR = veRadius (vsEpicycles scene Map.! id)
           in (id, CurveDeltaEpi id (NumDeltaAdd (toRational newR - toRational curR)) NumDeltaId NumDeltaId)
        SetFrequency id newF ->
          let curF = veFreq (vsEpicycles scene Map.! id)
           in (id, CurveDeltaEpi id NumDeltaId (NumDeltaAdd (newF - curF)) NumDeltaId)
        SetPhase id newP ->
          let curP = vePhase (vsEpicycles scene Map.! id)
           in (id, CurveDeltaEpi id NumDeltaId NumDeltaId (NumDeltaAdd (toRational newP - toRational curP)))

      ((finalDeltaEnv, modifiedAST), conflicts) = runWriter $ backwardEvalCurve curveDelta env (zeroDeltas env) ast
      newEnv = applyDeltaEnv finalDeltaEnv env
   in (CurveState modifiedAST newEnv, conflicts)

flattenNumberedList :: IEnv env -> AST Numbered env SCurve -> [(EpicycleId, Rational, Int, Rational)]
flattenNumberedList env (Epicycle eid r f p) = [(eid, evalExpr env r, evalExpr env f, evalExpr env p)]
flattenNumberedList env (Append a b) = flattenNumberedList env a <> flattenNumberedList env b
flattenNumberedList env (Let val body) =
  let v = evalExpr env val
   in flattenNumberedList (Ue.ECons (VNum v) env) body

getEpiParams :: [(EpicycleId, Rational, Int, Rational)] -> EpicycleId -> (Rational, Int, Rational)
getEpiParams epis eid = case List.find (\(i, _, _, _) -> i == eid) epis of
  Just (_, r, f, p) -> (r, f, p)
  Nothing -> error "Epicycle not found"

spec :: Spec
spec = do
  describe "FuseDM" $ do
    fromHedgehogGroup propertyTests

propertyTests :: H.Group
propertyTests = $$discover

prop_putGetLitRadius :: Property
prop_putGetLitRadius = property $ do
  r <- forAll genPositiveRadius
  target <- forAll genPositiveRadius
  let cs = mkState (epicycle (litR r) (lit 1) (lit 0))
      eid :| [] = targetEpiIds cs
      (cs', conflicts) = runFuseDM (SetRadius eid target) cs

  H.assert (null conflicts)
  H.diff (epiRadius cs' eid) approxEq target

prop_putGetLitFreq :: Property
prop_putGetLitFreq = property $ do
  r <- forAll genPositiveRadius
  f <- forAll genFreq
  target <- forAll genFreq
  let cs = mkState (epicycle (litR r) (lit f) (lit 0))
      eid = firstEpiId cs
      (cs', conflicts) = runFuseDM (SetFrequency eid target) cs

  H.assert (null conflicts)
  epiFreq cs' eid H.=== target

prop_putGetLitPhase :: Property
prop_putGetLitPhase = property $ do
  r <- forAll genPositiveRadius
  p <- forAll genFinite
  target <- forAll genFinite
  let cs = mkState (epicycle (litR r) (lit 1) (litR p))
      eid :| [] = targetEpiIds cs
      (cs', conflicts) = runFuseDM (SetPhase eid target) cs

  H.assert (null conflicts)
  H.diff (epiPhase cs' eid) approxEq target

prop_putGetParamRadius :: Property
prop_putGetParamRadius = property $ do
  r <- forAll genPositiveRadius
  target <- forAll genPositiveRadius
  let cs = mkState (let_ (litR r) $ \x -> epicycle x (lit 1) (lit 0))
      eid :| [] = targetEpiIds cs
      (cs', conflicts) = runFuseDM (SetRadius eid target) cs

  H.assert (null conflicts)
  H.diff (epiRadius cs' eid) approxEq target

prop_putGetScaledRadius :: Property
prop_putGetScaledRadius = property $ do
  r <- forAll genPositiveRadius
  k <- forAll genNonZero
  target <- forAll genPositiveRadius
  let cs = mkState (let_ (litR r) $ \x -> epicycle (x * litR k) (lit 1) (lit 0))
      eid :| [] = targetEpiIds cs
      (cs', _) = runFuseDM (SetRadius eid target) cs

  H.diff (epiRadius cs' eid) approxEq target

prop_putGetAdditiveRadius :: Property
prop_putGetAdditiveRadius = property $ do
  r <- forAll genPositiveRadius
  k <- forAll genFinite
  target <- forAll genPositiveRadius
  let cs = mkState (let_ (litR r) $ \x -> epicycle (x + litR k) (lit 1) (lit 0))
      eid :| [] = targetEpiIds cs
      (cs', _) = runFuseDM (SetRadius eid target) cs

  H.diff (epiRadius cs' eid) approxEq target

-- | if two epicycles share a radius, and we update one of them, the other should produce a conflict
prop_sharedRadiusConflictDetected :: Property
prop_sharedRadiusConflictDetected = property $ do
  r <- forAll genPositiveRadius
  target <- forAll (Gen.filter (not . approxEq r) genPositiveRadius)
  let cs = mkState (let_ (litR r) $ \x -> epicycle x (lit 1) (lit 0) <> epicycle x (lit 2) (lit 0))
      (eid0 :| _) = targetEpiIds cs
      (_cs', conflicts) = runFuseDM (SetRadius eid0 target) cs

  H.assert (not (null conflicts))

-- | if two epicycles share a radius, and we update one of them, only that one should change, and the other should stay the same
prop_sharedRadiusOnlyOneChanges :: Property
prop_sharedRadiusOnlyOneChanges = property $ do
  r <- forAll genPositiveRadius
  target <- forAll (Gen.filter (not . approxEq r) genPositiveRadius)
  let cs = mkState (let_ (litR r) $ \x -> epicycle x (lit 1) (lit 0) <> epicycle x (lit 2) (lit 0))
      (eid0 :| eid1 : _) = targetEpiIds cs
      (cs', _) = runFuseDM (SetRadius eid0 target) cs

  H.diff (epiRadius cs' eid0) approxEq target
  H.diff (epiRadius cs' eid1) approxEq r

-- | if a let is independent (i.e. only used once), it should never produce a conflict
prop_independentLetsNoConflict :: Property
prop_independentLetsNoConflict = property $ do
  r <- forAll genPositiveRadius
  target <- forAll genPositiveRadius
  let cs = mkState (let_ (litR r) $ \x -> epicycle x (lit 1) (lit 0) <> epicycle (lit 20) (lit 2) (lit 0))
      (eid0 :| _) = targetEpiIds cs
      (_cs', conflicts) = runFuseDM (SetRadius eid0 target) cs

  H.assert (null conflicts)

-- Getput
prop_stabilityLit :: Property
prop_stabilityLit = property $ do
  r <- forAll genPositiveRadius
  fVal <- forAll genFreq
  p <- forAll genFinite
  let cs = mkState (epicycle (litR r) (lit fVal) (litR p))
      eid = firstEpiId cs
      (cs', _) = runFuseDM (SetRadius eid r) cs
  H.diff (epiRadius cs' eid) approxEq r
  H.diff (epiFreq cs' eid) approxEq fVal
  H.diff (epiPhase cs' eid) approxEq p
