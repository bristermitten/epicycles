{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}

-- | tests for the Scene module
module SceneSpec (spec) where

import AST
import Data.Map qualified as Map
import Hedgehog (Property, discover, forAll, property, (===))
import Hedgehog qualified as H
import Scene
import Test.Syd
import Test.Syd.Hedgehog (fromHedgehogGroup)
import Utils
import Vec (Vec (..))

spec :: Spec
spec = describe "Scene" $ fromHedgehogGroup propertyTests

propertyTests :: H.Group
propertyTests = $$discover

-- | evalScene at two different times produces
-- the same epicycle IDs, radius, and frequency, i.e. only positions and the phase changes
prop_evalPreservesStructure :: Property
prop_evalPreservesStructure = property $ do
  t1 <- forAll genTime
  t2 <- forAll genTime
  let cs = mkState (epicycle (lit 100) (lit 1) (lit 0) <> epicycle (lit 50) (lit 3) (lit 0))
      s1 = evalScene cs t1
      s2 = evalScene cs t2

  -- epicycles should not change
  Map.keys (vsEpicycles s1) === Map.keys (vsEpicycles s2)

  -- same radii and frequencies
  for_ (Map.keys (vsEpicycles s1)) $ \eid -> do
    let ve1 = vsEpicycles s1 Map.! eid
        ve2 = vsEpicycles s2 Map.! eid
    H.diff (veRadius ve1) approxEq (veRadius ve2)
    H.diff (veFreq ve1) approxEq (veFreq ve2)

-- | The evaluated scene at t=0 with zero phase should have
-- each epicycle's endpoint at (centre.x + radius, centre.y).
prop_evalGeometryAtZero :: Property
prop_evalGeometryAtZero = property $ do
  r1 <- forAll genPositiveRadius
  r2 <- forAll genPositiveRadius
  let cs = mkState (epicycle (litR r1) (lit 1) (lit 0) <> epicycle (litR r2) (lit 2) (lit 0))
      scene = evalScene cs 0
      [eid0, eid1] = toList scene.vsEpicycleOrder
      ve0 = vsEpicycles scene Map.! eid0
      ve1 = vsEpicycles scene Map.! eid1
      Vec e0x e0y = veEndpoint ve0
      Vec c0x c0y = veCentre ve0
      Vec c1x c1y = veCentre ve1
      Vec e1x _e1y = veEndpoint ve1

  -- At t=0, phase=0, so endpoint.x = centre.x + radius
  H.diff e0x approxEq (c0x + r1)
  H.diff e0y approxEq c0y

  -- the second epicycle should be centred at the endpoint of the first
  H.diff c1x approxEq e0x
  H.diff c1y approxEq e0y
  H.diff e1x approxEq (c1x + r2)

-- | applySceneEdit modifies the evaluated visual scene struct correctly
prop_applySceneEdit :: Property
prop_applySceneEdit = property $ do
  r <- forAll genPositiveRadius
  newR <- forAll genPositiveRadius
  f <- forAll genFreq
  newF <- forAll genFreq
  t <- forAll genTime
  let cs = mkState (epicycle (litR r) (lit f) (lit 0))
      scene = evalScene cs t
      eid = head (vsEpicycleOrder scene)

      sceneR = applySceneEdit (SetRadius eid newR) scene
      sceneF = applySceneEdit (SetFrequency eid newF) scene

  veRadius (vsEpicycles sceneR Map.! eid) === newR
  veFreq (vsEpicycles sceneF Map.! eid) === newF

-- | GetPut but on Scenes
prop_getPut :: Property
prop_getPut = property $ do
  r <- forAll genPositiveRadius
  f <- forAll genFreq
  t <- forAll genTime
  let cs = mkState (epicycle (litR r) (lit f) (lit 0))
      scene = evalScene cs t
      eid = head (vsEpicycleOrder scene)
      ve = vsEpicycles scene Map.! eid
      edit = SetRadius eid (veRadius ve)

  case  applyEdit heuristicStrategy edit cs of
    Nothing -> H.failure
    Just cs' -> do
      let scene' = evalScene cs' t
          ve' = vsEpicycles scene' Map.! eid
      H.diff (veRadius ve') approxEq (veRadius ve)
      H.diff (veFreq ve') approxEq (veFreq ve)
      H.diff (vePhase ve') approxEq (vePhase ve)

-- | PutGet for Radius
prop_putGetRadius :: Property
prop_putGetRadius = property $ do
  r <- forAll genPositiveRadius
  f <- forAll genFreq
  newR <- forAll genPositiveRadius
  t <- forAll genTime
  let cs = mkState (epicycle (litR r) (lit f) (lit 0))
      scene = evalScene cs t
      eid = head (vsEpicycleOrder scene)
      edit = SetRadius eid newR

  case  applyEdit heuristicStrategy edit cs of
    Nothing -> H.annotate "backwardEdit failed" *> H.failure
    Just cs' -> do
      let scene' = evalScene cs' t
          ve' = vsEpicycles scene' Map.! eid
      H.diff (veRadius ve') approxEq newR

-- | PutGet for frequency
prop_putGetFrequency :: Property
prop_putGetFrequency = property $ do
  r <- forAll genPositiveRadius
  f <- forAll genFreq
  newF <- forAll genFreq
  t <- forAll genTime
  let cs = mkState (epicycle (litR r) (lit f) (lit 0))
      scene = evalScene cs t
      eid = head (vsEpicycleOrder scene)
      edit = SetFrequency eid newF

  case  applyEdit heuristicStrategy edit cs of
    Nothing -> H.annotate "backwardEdit failed" *> H.failure
    Just cs' -> do
      let scene' = evalScene cs' t
          ve' = vsEpicycles scene' Map.! eid
      H.diff (veFreq ve') approxEq newF

-- | PutGet for radius with shared parameters (let-bound).
prop_putGetRadiusShared :: Property
prop_putGetRadiusShared = property $ do
  r <- forAll genPositiveRadius
  newR <- forAll genPositiveRadius
  t <- forAll genTime
  let cs = mkState (let_ (litR r) $ \x -> epicycle x (lit 1) (lit 0) <> epicycle x (lit 3) (lit 0))
      scene = evalScene cs t
      eid0 = head (vsEpicycleOrder scene)
      edit = SetRadius eid0 newR

  case  applyEdit heuristicStrategy edit cs of
    Nothing -> H.annotate "backwardEdit failed" *> H.failure
    Just cs' -> do
      let scene' = evalScene cs' t
          ve0 = vsEpicycles scene' Map.! eid0
      H.diff (veRadius ve0) approxEq newR

-- | backward edit should not change the number of epicycles or their IDs.
prop_backwardPreservesStructure :: Property
prop_backwardPreservesStructure = property $ do
  r <- forAll genPositiveRadius
  f <- forAll genFreq
  newR <- forAll genPositiveRadius
  t <- forAll genTime
  let cs = mkState (epicycle (litR r) (lit f) (lit 0) <> epicycle (lit 50) (lit 2) (lit 0))
      scene = evalScene cs t
      eid = head (vsEpicycleOrder scene)
      edit = SetRadius eid newR

  case applyEdit heuristicStrategy edit cs of
    Nothing -> H.annotate "backwardEdit failed" *> H.failure
    Just cs' -> do
      let scene' = evalScene cs' t
      Map.keys (vsEpicycles scene') === Map.keys (vsEpicycles scene)
      vsEpicycleOrder scene' === vsEpicycleOrder scene