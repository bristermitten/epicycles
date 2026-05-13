{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | shared code for SnS update mechanisms
module Update.SnS.Common where

import AST
import Data.Typeable
import Pretty (PrettyCurve (..))
import PrettyAST
import Unembedding.Env qualified as Ue
import Update.Types

-- | information about a backwards update under this algorithm
data UpdateInfo env = UpdateInfo
    { updateState :: CurveState env
    -- ^ the resulting curve state after applying the update, i.e. the actual result
    , updateDepth :: EditDepth
    -- ^ a measure of how "deep" the edit is, used for ranking updates
    , updateCandidateDetails :: [(Text, EditDepth)]
    {- ^ details about the ALTERNATIVE candidates that were considered.
    the text should be some sort of human readable description of the candidate
    -}
    }

-- | the ordering of an update
data EditDepth
    = -- | the expression was already approximately equal to the target, so no edit is needed
      NoEdit
    | -- | the edit only involved changing a literal
      LitEdit
    | -- | a parameter in the innermost scope was changed
      LocalParam
    | -- | a parameter at depth @n@ was changed (from the innermost scope, so @'OuterParam' 0@  would be the same as 'LocalParam')
      OuterParam Int
    | -- | the edit is would change the structure of the expression. in well formed code this shouldn't be possible, but kept for completeness
      ImpossibleEdit
    deriving (Eq, Show)

editDepthCost :: EditDepth -> Int
editDepthCost NoEdit = 0
editDepthCost LitEdit = 1
editDepthCost LocalParam = 2
editDepthCost (OuterParam n) = 2 + n
editDepthCost ImpossibleEdit = maxBound

instance Ord EditDepth where
    compare d1 d2 = compare (editDepthCost d1) (editDepthCost d2)

-- | class for environments that can be compared for differences
class DiffEnv (env :: [ASTSort]) where
    diffEnv :: Int -> Ue.Env SortVal env -> Ue.Env SortVal env -> EditDepth

instance DiffEnv '[] where
    diffEnv _ Ue.ENil Ue.ENil = NoEdit

instance (DiffEnv rest, ApproxEq n) => DiffEnv (SNum n ': rest) where
    diffEnv d (Ue.ECons (VNum v1) rest1) (Ue.ECons (VNum v2) rest2)
        | approxEq v1 v2 = diffEnv (d + 1) rest1 rest2
        | otherwise =
            max
                (if d == 0 then LocalParam else OuterParam d)
                (diffEnv (d + 1) rest1 rest2)

-- | Compare two expressions structurally and determine the "edit depth" of their differences
diffExpr ::
    (ApproxEq n) =>
    AST phase env (SNum n) ->
    AST phase env (SNum n) ->
    EditDepth
diffExpr (Lit a) (Lit b)
    | approxEq a b = NoEdit
    | otherwise = LitEdit
diffExpr (Param_ _p _) (Param_ _p2 _) = NoEdit -- Param edits are detected in the Env, not the AST
diffExpr (Add a b) (Add c d) = max (diffExpr a c) (diffExpr b d)
diffExpr (Mul a b) (Mul c d) = max (diffExpr a c) (diffExpr b d)
diffExpr (Recip a) (Recip b) = diffExpr a b
diffExpr (Let (v1 :: AST phase env n1) b1) (Let (v2 :: AST phase env n2) b2) =
    case eqT @n1 @n2 of
        Just Refl -> max (diffExpr v1 v2) (diffExpr b1 b2)
        Nothing -> ImpossibleEdit -- cannot be compared if the types of the let bindings are different which should never happen
diffExpr _ _ = ImpossibleEdit

-- | the result of a backwards update
data UpdateResult phase env n
    = UpdateResult
    { updatedExpr :: AST phase env n
    -- ^ the updated expression after applying the backwards update
    , updatedEnv :: IEnv env
    -- ^ the updated environment after applying the backwards update
    }

deriving instance (Show (XEpicycle phase), Show (AST phase env n)) => Show (UpdateResult phase env n)

instance PrettyCurve (UpdateResult phase env (SNum n)) where
    prettyPrec _ (UpdateResult expr env) = prettyExpr 0 env expr

rankResult ::
    (ApproxEq n, DiffEnv env) =>
    AST phase env (SNum n) ->
    Ue.Env SortVal env ->
    UpdateResult phase env (SNum n) ->
    EditDepth
rankResult oldExpr oldEnv (UpdateResult newExpr newEnv) =
    max (diffExpr oldExpr newExpr) (diffEnv 0 oldEnv newEnv)

{- | generic traversal over a curve expression to apply a backwards update strategy to a specific epicycle parameter.
we recursively descend over the curve AST
-}
genericCurveUpdate ::
    forall param env info.
    (DiffEnv env, SelectParam param, InternalUpdateInfo info) =>
    -- | The strategy to update the target Epicycle
    ( forall innerEnv n.
      (DiffEnv innerEnv, BindableNum n) =>
      IEnv innerEnv ->
      AST Numbered innerEnv (SNum n) ->
      n ->
      Maybe (UpdateResult Numbered innerEnv (SNum n), info)
    ) ->
    EpicycleId ->
    EpicycleParamType param ->
    CurveState env ->
    Maybe (CurveState env, info)
genericCurveUpdate strategy epicycleId target state = do
    (resultAST, resultEnv, info) <- go state.curveAST state.envParams
    pure (CurveState resultAST resultEnv, info)
  where
    go ::
        forall innerEnv.
        (DiffEnv innerEnv) =>
        AST Numbered innerEnv SCurve ->
        IEnv innerEnv ->
        Maybe (AST Numbered innerEnv SCurve, IEnv innerEnv, info)
    go (Epicycle eid r f p) env
        | eid == epicycleId =
            let EpicycleParamLens expr rebuild = selectParam @param r f p
             in case strategy env expr target of
                    Nothing -> Nothing
                    Just (UpdateResult expr' env', info) ->
                        Just (rebuild eid expr', env', info)
        | otherwise = Nothing
    go (Append a b) env =
        case go a env of
            Just (a', env', info) -> Just (Append a' b, env', info)
            Nothing -> case go b env of
                Just (b', env', info) -> Just (Append a b', env', info)
                Nothing -> Nothing
    go (Let (val :: AST Numbered innerEnv (SNum n)) body) env = do
        let v = evalExpr env val -- eval v
            extendedEnv = Ue.ECons (VNum v) env -- bind to env
        (body', Ue.ECons (VNum wantedV) outerFromBody, info) <- go body extendedEnv -- update body
        case strategy outerFromBody val wantedV of
            Nothing -> Just (Let (Lit wantedV) body', outerFromBody, info)
            Just (UpdateResult val' outerFinal, info') -> do
                -- we have to combine info and info' here otherwise information might get lost
                -- info is the info from the updating the body, and info' is the info from updating the val,
                -- we want to combine them to get a more complete picture of the total edit
                let combinedInfo = combineInfo info info'
                guard (approxEq (evalExpr outerFinal val') wantedV) -- another consistency guard
                Just (Let val' body', outerFinal, combinedInfo)

{- | information about an update that can be combined.
slightly hacky solution to the above problem of let bindings having 2 sources of edit info.
we just provide instances for the specific info types we actually use
-}
class InternalUpdateInfo info where
    combineInfo :: info -> info -> info

-- trivial instance for when we dont have any info to combine
instance InternalUpdateInfo () where
    combineInfo _ _ = ()

instance InternalUpdateInfo (EditDepth, Int) where
    combineInfo (d1, n1) (d2, n2) = (combineInfo d1 d2, n1 + n2)

instance InternalUpdateInfo (EditDepth, [(Text, EditDepth)]) where
    combineInfo (d1, n1) (d2, n2) = (combineInfo d1 d2, n1 <> n2)

instance InternalUpdateInfo EditDepth where
    combineInfo = max
