{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}

-- | The main implementation of the delta based update semantics (FuseDM)
module Update.Delta (
    backwardEvalNum,
    backwardEvalCurve,
    Conflict (..),
    ResolutionType (..),
    fuseDMBackward,
)
where

import AST (AST (..), ASTSort (..), BindableNum (safeDiv), CurveState (..), IEnv, ShowAST, SortVal (VNum), Stage (Numbered), evalExpr)
import Control.Monad.Writer
import Delta
import Unembedding.Env qualified as Ue

-- | Information about a conflict that was encountered during the merge process, for logging and debugging purposes
data Conflict = ConflictLog
    { clVariableIndex :: Int
    -- ^ Which De Bruijn index caused the clash?
    , clLeftDelta :: Text -- Stringified mathematical intent of the left branch
    , clRightDelta :: Text -- Stringified mathematical intent of the right branch
    , clSuffixLength :: Int -- Did the suffix split actually save anything?
    , clASTNode :: String -- e.g., "Add", "Let" (where the merge happened)
    , clResolution :: ResolutionType
    }
    deriving (Show, Eq)

data ResolutionType
    = CleanSuffixSplit -- The prefix was small, suffix took the brunt
    | TotalDisagreement -- Suffix was Id, the algorithm was forced to embed everything
    deriving (Show, Eq)

type DeltaM = Writer [Conflict]

-- | everything apart from 'backwardEval' can run in this monad, which also gives it access to the current node name for logging purposes
type InnerDeltaM a = ReaderT String DeltaM a

runInnerDeltaM :: String -> InnerDeltaM a -> DeltaM a
runInnerDeltaM = usingReaderT

{- | backwards evaluation
roughly the  Δ ⊢ dv ◁ e ⇝ (Δ', e') rule from the paper
-}
backwardEvalNum ::
    (ShowAST (SNum n), BindableNum n) =>
    NumDelta n -> -- delta dv
    IEnv env -> -- current values of parameters
    DeltaEnv env -> -- current deltas environment (E)
    AST Numbered env (SNum n) -> -- expression e
    DeltaM (DeltaEnv env, AST Numbered env (SNum n)) -- updated environment E' and updated expression e'
backwardEvalNum NumDeltaId _vals deltaEnv e = pure (deltaEnv, e)
-- applying a delta to a literal just updates the literal
-- D-Lit (which subsumes A-Add and A-Mul from the original paper)
backwardEvalNum d _env deltaEnv (Lit n) =
    pure (deltaEnv, Lit (applyNumDelta d n))
-- applying a delta to a parameter creates a new parameter with the updated value
-- i.e. P-Var
backwardEvalNum d _varEnv deltaEnv (Param_ p ix) =
    let EDNum existingDelta = Ue.lookEnv deltaEnv ix
        composedDelta = d <> existingDelta
        env' = Ue.setIx ix (EDNum composedDelta) deltaEnv
     in pure (env', Param_ p ix)
-- A-Repl
backwardEvalNum ((NumDeltaReplace n)) vals _E _e =
    pure (zeroDeltas vals, Lit n)
-- D-ADD-ADD rule
backwardEvalNum dplus@(((NumDeltaAdd _))) vals _E e@(Add e1 e2) = do
    -- +𝑛 ⊲ 𝐸 ⊢ 𝑒1 ~> 𝐸1 ⊢ 𝑒′1
    (_E1, e1') <- backwardEvalNum dplus vals _E e1
    (_E', e_1'', e_2') <- runInnerDeltaM (show e) $ optimisedMerge _E1 _E e1' e2
    pure (_E', Add e_1'' e_2')

-- D-Add-Mul / D-Add-Embed
backwardEvalNum (((NumDeltaAdd n))) sigma _Delta e@(Mul e1 e2) = do
    let sigma' = applyDeltaEnv _Delta sigma -- (∆ ▷ σ)
    let n2 = evalExpr sigma' e2
    case n `safeDiv` n2 of -- D-Add-Mul
        Just deltaForX -> do
            (_E1, e1') <- backwardEvalNum (NumDeltaAdd deltaForX) sigma' _Delta e1
            (_DeltaM, e_1'', e_2') <- runInnerDeltaM (show e) $ optimisedMerge _E1 _Delta e1' e2
            pure (_DeltaM, Mul e_1'' e_2')
        Nothing ->
            -- D-Add-Embed
            pure (_Delta, embedANumDelta (ANumDeltaAdd n) e)

-- D-Add-Recip / D-Add-Recip-Embed
-- Linearise around the current user-visible value (∆ ▷ σ), but recurse with
-- the original `sigma`; the env-update mechanism already accumulates `_Delta`
-- correctly, and passing `sigma'` would double-apply pending deltas.
backwardEvalNum (((NumDeltaAdd d))) sigma _Delta (Recip x) = do
    let sigma' = applyDeltaEnv _Delta sigma -- (∆ ▷ σ)
    let valX = evalExpr sigma' x
        mDx = do
            recipX <- safeDiv 1 valX
            newRecip <- safeDiv 1 (recipX + d)
            pure (newRecip - valX)
    case mDx of
        Just dx -> do
            (env', x') <- backwardEvalNum (AtomicNumDelta (ANumDeltaAdd dx)) sigma _Delta x
            pure (env', Recip x')
        Nothing ->
            -- inverse undefined, so embed
            pure (_Delta, embedANumDelta (ANumDeltaAdd d) (Recip x))

-- essentially the A-Com rule, but generalised to work over lists of deltas rather than
-- a single inductive pair
backwardEvalNum ((ComposeNumDeltas (d :| ds))) vals _E e =
    case ds of
        [] -> backwardEvalNum (AtomicNumDelta d) vals _E e
        next : rest -> do
            let intermediateDelta = ComposeNumDeltas (next :| rest)
            (deltaEnv', e') <- backwardEvalNum intermediateDelta vals _E e
            backwardEvalNum (AtomicNumDelta d) vals deltaEnv' e'

-- D-Add-Mul
backwardEvalNum dv@((NumDeltaMul _)) vals deltas e@(Add x y) = do
    (env1, x') <- backwardEvalNum dv vals deltas x
    (env2, y') <- backwardEvalNum dv vals deltas y
    (eM, x'', y'') <- runInnerDeltaM (show e) $ optimisedMerge env1 env2 x' y'
    pure (eM, Add x'' y'')
-- D-Let
backwardEvalNum dv vals deltas e@(Let e1 o) = do
    let v1 = evalExpr vals e1 -- sigma |- e1 ⇓ v1
        valsBody = Ue.ECons (VNum v1) vals -- sigma, v1 |- body (not in the official rule)
        paddedDelta = Ue.ECons (EDNum NumDeltaId) deltas -- Delta[x ↦ id]
    (envBody', o') <- backwardEvalNum dv valsBody paddedDelta o -- Delta[x ↦ id] |- dv <| o ~> ((Delta_body, dv_x), o')
    let Ue.ECons (EDNum dv_x) _DeltaBody = envBody' -- (Delta_body, dv_x)
    (_DeltaVal, e1') <- backwardEvalNum dv_x vals deltas e1 -- Delta |- dv_x <| e_1 ~> (Delta_val, e1')

    -- <Delta_val, e1'> ▷◁ <Delta_body, o'> ~> (Delta^M, e1'', o'')
    (eM, e1'', o'') <-
        runInnerDeltaM (show e) $
            optimisedMergeLet _DeltaVal _DeltaBody e1' o'

    pure (eM, Let e1'' o'')

-- D-Mul-Add
backwardEvalNum (((NumDeltaMul m))) vals deltas e@(Mul x y) = do
    (env', x') <- backwardEvalNum (NumDeltaMul m) vals deltas x
    -- Right branch is unmodified, but we must merge the environments
    (eM, x'', y') <- runInnerDeltaM (show e) $ optimisedMerge env' deltas x' y
    pure (eM, Mul x'' y')
-- D-Mul-Recip & D-Mul-Recip-Embed
backwardEvalNum (((NumDeltaMul m))) vals deltas (Recip x) = case 1 `safeDiv` m of
    Just invM -> do
        (env', x') <- backwardEvalNum (NumDeltaMul invM) vals deltas x
        pure (env', Recip x')
    Nothing ->
        pure (deltas, embedANumDelta (ANumDeltaMul m) (Recip x))

backwardEvalCurve ::
    (ShowAST SCurve) =>
    CurveDelta ->
    IEnv env ->
    DeltaEnv env ->
    AST Numbered env SCurve ->
    DeltaM (DeltaEnv env, AST Numbered env SCurve)
-- D-Epi-Id
backwardEvalCurve CurveDeltaId _ deltas e = pure (deltas, e)
-- D-Epi-Match
backwardEvalCurve ((CurveDeltaEpi targetId dR dW dP)) vals deltas e@(Epicycle eid r w p)
    | targetId == eid = do
        (envR, r') <- backwardEvalNum dR vals deltas r
        (envW, w') <- backwardEvalNum dW vals deltas w
        (envP, p') <- backwardEvalNum dP vals deltas p

        -- merge r and w
        (envRW, envRI, envWI) <-
            runInnerDeltaM (show e) $
                compareOperator envR envW (`isFreeIn` r') (`isFreeIn` w')

        let r'' = embeddingOperator envRI r'
            w'' = embeddingOperator envWI w'

        -- merge RW and p
        -- left branch is updated r _and_ w, so it's free if it's free in either
        (eM, envRWI, envPI) <-
            runInnerDeltaM (show e) $
                compareOperator envRW envP (\ix -> isFreeIn ix r'' || isFreeIn ix w'') (`isFreeIn` p')

        let r''' = embeddingOperator envRWI r''
            w''' = embeddingOperator envRWI w''
            p'' = embeddingOperator envPI p'

        pure (eM, Epicycle eid r''' w''' p'')
    | otherwise = pure (deltas, Epicycle eid r w p)
-- D-Epi-Skip
backwardEvalCurve tgt@(CurveDeltaEpi{}) vals _E e@(Append c1 c2) = do
    (_E1, c1') <- backwardEvalCurve tgt vals _E c1
    (_E2, c2') <- backwardEvalCurve tgt vals _E c2
    (eM, c1I, c2I) <- runInnerDeltaM (show e) $ compareOperator _E1 _E2 (`isFreeIn` c1') (`isFreeIn` c2')
    let c1'' = embeddingOperator c1I c1'
        c2'' = embeddingOperator c2I c2'

    pure (eM, Append c1'' c2'')
-- D-Append-Target.
-- Both halves start from `deltas` independently and the resulting envs are
-- merged.  (Threading `env1` into `c2`'s call would be unsound when c1 and c2
-- share free variables.)
backwardEvalCurve ((CurveDeltaAppend dL dR)) vals deltas e@(Append c1 c2) = do
    (env1, c1') <- backwardEvalCurve dL vals deltas c1
    (env2, c2') <- backwardEvalCurve dR vals deltas c2
    (eM, c1I, c2I) <- runInnerDeltaM (show e) $ compareOperator env1 env2 (`isFreeIn` c1') (`isFreeIn` c2')
    let c1'' = embeddingOperator c1I c1'
        c2'' = embeddingOperator c2I c2'
    pure (eM, Append c1'' c2'')

-- D-Let (again)
backwardEvalCurve dv vals deltas e@(Let e1 o) = do
    let v1 = evalExpr vals e1 -- sigma |- e1 ⇓ v1
        valsBody = Ue.ECons (VNum v1) vals -- sigma, v1 |- body
        paddedDelta = Ue.ECons (EDNum NumDeltaId) deltas -- Delta[x ↦ id]
    (envBody', o') <- backwardEvalCurve dv valsBody paddedDelta o -- Delta[x ↦ id] |- dv <| o ~> ((Delta_body, dv_x), o')
    let Ue.ECons (EDNum dv_x) _DeltaBody = envBody' -- (Delta_body, dv_x)
    (_DeltaVal, e1') <- backwardEvalNum dv_x vals deltas e1 -- Delta |- dv_x <| e_1 ~> (Delta_val, e1')

    -- <Delta_val, e1'> ▷◁ <Delta_body, o'> ~> (Delta^M, e1'', o'')
    (eM, e1'', o'') <-
        runInnerDeltaM (show e) $
            optimisedMergeLet _DeltaVal _DeltaBody e1' o'

    pure (eM, Let e1'' o'')

-- not really a named rule, just for pattern match exhaustiveness
backwardEvalCurve ((CurveDeltaAppend _ _)) _ deltas e@(Epicycle{}) =
    pure (deltas, e)

-- implementation of the operation 𝐸1 𝑒1⊗𝑒2 𝐸2 from the paper
-- also known as the "optimized merge operator"
-- this is defined as:
-- (E^M, e_1', e_2') = E1 𝑒1⊗𝑒2 𝐸2 iff
-- (E^M, E_1^I, E_2^I) = E_1 e1Xe2 E_2,
-- e_1' = E_1^I ⊙ e1, e_2' = E_2^I ⊙ e2
-- where e1Xe2 is the "comparing operator", and ⊙ is the "embedding operator"
optimisedMerge ::
    -- | E_1
    DeltaEnv env ->
    -- | E_2
    DeltaEnv env ->
    -- | e1
    AST Numbered env s ->
    -- | e2
    AST Numbered env s ->
    -- | merged env, left conflicts, right conflicts
    InnerDeltaM (DeltaEnv env, AST Numbered env s, AST Numbered env s)
optimisedMerge env1 env2 e1 e2 = do
    (eM, e1I, e2I) <- compareOperator env1 env2 (`isFreeIn` e1) (`isFreeIn` e2)
    let e1' = embeddingOperator e1I e1
        e2' = embeddingOperator e2I e2

    pure (eM, e1', e2')

{- | 'optimisedMerge' but for let bindings, which require a slightly different handling due to the change in environment
-- <Delta_val, e1'> ▷◁ <Delta_body, o'> ~> (Delta^M, e1'', o'')
-}
optimisedMergeLet ::
    (BindableNum n) =>
    DeltaEnv as1 -> -- Delta_val
    DeltaEnv as1 -> -- Delta_body
    AST Numbered as1 s1 -> -- e1'
    AST Numbered (SNum n : as1) s2 -> -- o'
    InnerDeltaM (DeltaEnv as1, AST Numbered as1 s1, AST Numbered (SNum n : as1) s2)
optimisedMergeLet _Delta_val _Delta_body e1 e2 = do
    (eM, e1I, e2I) <- compareOperator _Delta_val _Delta_body (`isFreeIn` e1) (\ix -> isFreeIn (Ue.IxS ix) e2)
    let e1' = embeddingOperator e1I e1
        paddedEnv = Ue.ECons (EDNum NumDeltaId) e2I
        e2' = embeddingOperator paddedEnv e2

    pure (eM, e1', e2')

compareOperator ::
    forall env.
    DeltaEnv env -> -- E_1
    DeltaEnv env -> -- E_2
    (forall val. Ue.Ix env val -> Bool) -> -- isFreeIn left branch
    (forall val. Ue.Ix env val -> Bool) -> -- isFreeIn right branch

    -- | (ConflictInfo, MergedEnv, LeftConflicts, RightConflicts)
    InnerDeltaM (DeltaEnv env, DeltaEnv env, DeltaEnv env)
compareOperator env1 env2 isFree1 isFree2 =
    go env1 env2 id
  where
    -- recurse over the two environments inductively
    go ::
        forall sub.
        DeltaEnv sub ->
        DeltaEnv sub ->
        (forall val. Ue.Ix sub val -> Ue.Ix env val) ->
        InnerDeltaM (DeltaEnv sub, DeltaEnv sub, DeltaEnv sub)
    go Ue.ENil Ue.ENil _ = pure (Ue.ENil, Ue.ENil, Ue.ENil) -- base case: both environments empty
    go (Ue.ECons d1 rest1) (Ue.ECons d2 rest2) liftIx = do
        let ix = liftIx Ue.IxZ
        (eM, e1I, e2I) <- go rest1 rest2 (liftIx . Ue.IxS)
        let
            -- cases 1 and 2 have the same result
            -- if dv1 = dv2 and if 𝑥 ∉ fv(𝑒2)
            case1Or2 = simplifyDelta d1 == simplifyDelta d2 || not (isFree2 ix)
         in
            if case1Or2
                then
                    pure
                        ( d1 `Ue.ECons` eM
                        , idDelta d1 `Ue.ECons` e1I
                        , idDelta d2 `Ue.ECons` e2I
                        )
                -- if 𝑥 ∉ fv(𝑒1)
                else
                    if not (isFree1 ix)
                        then
                            pure
                                ( d2 `Ue.ECons` eM
                                , idDelta d1 `Ue.ECons` e1I
                                , idDelta d2 `Ue.ECons` e2I
                                )
                        else do
                            -- conflict case
                            nodeName <- ask
                            let (dv', dv1', dv2') = longestCommonSuffix d1 d2
                                suffixLen = sizeOfDelta dv'
                                resType = if suffixLen > 0 then CleanSuffixSplit else TotalDisagreement
                                newLog = ConflictLog (Ue.ixToInt ix) (show d1) (show d2) suffixLen nodeName resType
                            tell [newLog]
                            pure
                                ( dv' `Ue.ECons` eM
                                , dv1' `Ue.ECons` e1I
                                , dv2' `Ue.ECons` e2I
                                )

{- | e' = E^I ⊙ e
traverses the AST, if it hits a Param with a delta in E^I,
it wraps the parameter in the appropriate NumDelta application to produce the updated parameter
-}
embeddingOperator ::
    -- | E^I
    DeltaEnv env ->
    -- | e
    AST Numbered env s ->
    -- | e'
    AST Numbered env s
embeddingOperator _ (Lit n) = Lit n
embeddingOperator env (Param_ p ix) =
    let delta = Ue.lookEnv env ix
     in case delta of
            EDNum numDelta ->
                embedNumDelta numDelta (Param_ p ix)
embeddingOperator env (Add e1 e2) = Add (embeddingOperator env e1) (embeddingOperator env e2)
embeddingOperator env (Mul e1 e2) = Mul (embeddingOperator env e1) (embeddingOperator env e2)
embeddingOperator env (Recip e) = Recip (embeddingOperator env e)
embeddingOperator env (Append c1 c2) = Append (embeddingOperator env c1) (embeddingOperator env c2)
embeddingOperator env (Epicycle eid r w p) = Epicycle eid (embeddingOperator env r) (embeddingOperator env w) (embeddingOperator env p)
embeddingOperator env (Let e1 o) =
    let e1' = embeddingOperator env e1
        envForBody = Ue.ECons (EDNum NumDeltaId) env
        o' = embeddingOperator envForBody o
     in Let e1' o'

{- | checks if a parameter is free in an expression
since we only allow closed terms, this means _locally_ free
-}
isFreeIn :: Ue.Ix env s -> AST Numbered env s2 -> Bool
isFreeIn _ix (Lit _) = False
isFreeIn ix (Param_ _ ix') = Ue.ixToWord ix == Ue.ixToWord ix'
isFreeIn ix (Add e1 e2) = isFreeIn ix e1 || isFreeIn ix e2
isFreeIn ix (Mul e1 e2) = isFreeIn ix e1 || isFreeIn ix e2
isFreeIn ix (Recip e) = isFreeIn ix e
isFreeIn ix (Append c1 c2) = isFreeIn ix c1 || isFreeIn ix c2
isFreeIn ix (Epicycle _eid r w p) = isFreeIn ix r || isFreeIn ix w || isFreeIn ix p
isFreeIn ix (Let e1 o) = isFreeIn ix e1 || isFreeIn (Ue.IxS ix) o

fuseDMBackward ::
    (ShowAST SCurve) =>
    CurveDelta -> CurveState env -> (CurveState env, [Conflict])
fuseDMBackward curveDelta (CurveState ast env) =
    let ((finalDeltaEnv, modifiedAST), conflicts) = runWriter $ backwardEvalCurve curveDelta env (zeroDeltas env) ast
        newEnv = applyDeltaEnv finalDeltaEnv env
     in (CurveState modifiedAST newEnv, conflicts)

-- | sends a delta to its corresponding identity delta with the same 'ASTSort'
idDelta :: EnvDelta s -> EnvDelta s
idDelta (EDNum{}) = EDNum NumDeltaId
