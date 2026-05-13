{-# LANGUAGE TemplateHaskell #-}


-- | this proves the structural invariance of the SnS update algorithm:
-- that is, the shape of the AST is preserved by updates, and only the literal values change.
-- this is sort of an obvious property - the construction of the semantics literally cannot do this.
-- however there is no proof of this in the type system, and so this serves as an extra sanity check / bug catcher
module ExprShapeSpec (spec) where

import AST
import Gen (genClosedExpr)
import Hedgehog (Property, discover, forAll, property, (===))
import Hedgehog qualified as H
import Test.Syd
import Test.Syd.Hedgehog (fromHedgehogGroup)
import Unembedding.Env qualified as Ue
import Update.SnS
import Update.SnS.Heuristic
import Prelude
import Utils

spec :: Spec
spec = fromHedgehogGroup $$discover

-- | a "shape" of an expression, ignoring specific values and just comparing structure
data ExprShape
    = SLit
    | SParam
    | SAdd ExprShape ExprShape
    | SMul ExprShape ExprShape
    | SRecip ExprShape
    | SLet ExprShape ExprShape
    deriving (Show, Eq)

exprShape :: AST phase env (SNum n) -> ExprShape
exprShape (Lit _) = SLit
exprShape (Param_ _ _) = SParam
exprShape (Add e1 e2) = SAdd (exprShape e1) (exprShape e2)
exprShape (Mul e1 e2) = SMul (exprShape e1) (exprShape e2)
exprShape (Recip e) = SRecip (exprShape e)
exprShape (Let val body) = SLet (exprShape val) (exprShape body)

-- | updating an expression must preserve the shape / structure of the expression
prop_updatePreservesShape :: Property
prop_updatePreservesShape = property $ do
    expr <- forAll genClosedExpr
    target <- forAll genFinite

    case bestUpdate Ue.ENil expr target of
        Nothing -> H.discard -- assuming the update actually exists
        Just updated ->
            exprShape expr === exprShape updated.updatedExpr
