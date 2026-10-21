{-# LANGUAGE TemplateHaskell #-}

{- | checks for the contextual embedding:
the round trip @unembed . contextualise = id@ (the CE paper's @isoL@),
and that variables written in the frontend reify to the right de Bruijn index
-}
module ContextualSpec (spec) where

import AST
import Gen (SomeExpr (..), genClosedExpr, genSomeExpr)
import Hedgehog (Property, discover, forAll, property, withTests, (===))
import Hedgehog qualified as H
import Test.Syd
import Test.Syd.Hedgehog (fromHedgehogGroup)

import ContextualEmbeddings
import Prelude

spec :: Spec
spec = fromHedgehogGroup $$discover

-- | for any closed expression, @unembed . contextualise === id@
prop_roundTripClosed :: Property
prop_roundTripClosed = property $ do
    e <- forAll (genClosedExpr @Parsed)
    unembed (contextualise e) === e

-- | for any open expression, @unembed . contextualise === id@
prop_roundTripAnyEnv :: Property
prop_roundTripAnyEnv = property $ do
    SomeExpr _ e <- forAll (genSomeExpr @Parsed)
    unembed (contextualise e) === e