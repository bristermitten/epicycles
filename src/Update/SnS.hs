{-# LANGUAGE UndecidableInstances #-}

{- | the main implementation of the sketch-n-sketch based non-deterministic
backwards update semantics
-}
module Update.SnS (module Update.SnS.Common, exprUpdate) where

import AST
import Unembedding.Env qualified as Ue
import Update.SnS.Common

{- | apply the backwards update semantics to update the environment to try and reach a target value for an expression

This is fully polymorphic over the numeric type via 'BindableNum'.  After the
move from 'Double' to 'Rational' for radius/phase, several edge cases fall away
automatically:

  * The stability check uses 'approxEq', which for 'Rational' is exact '=='
    — no more spurious failures from accumulated floating-point drift.

  * 'safeDiv' for 'Rational' fails iff the divisor is zero, so 'U-Mul' and
    'U-Recip' admit far more candidates than under 'Int' (which required
    exact integer division).

  * The 'isFinite' guards are no-ops for 'Rational' / 'Int' but kept for
    'Double' to reject NaN / Infinity targets.
-}
exprUpdate ::
    (DiffEnv env, BindableNum x) =>
    -- | the environment σ
    IEnv env ->
    -- | the expression e
    AST Numbered env (SNum x) ->
    -- | the target value v'
    x ->
    -- | a list of possible updates
    [UpdateResult Numbered env (SNum x)]
-- U-CONST
exprUpdate env (Lit _) target
    | isFinite target = [UpdateResult{updatedExpr = Lit target, updatedEnv = env}]
    | otherwise = []
-- U-Var
exprUpdate env (Param_ p ix) target
    | isFinite target =
        [ UpdateResult
            (Param_ p ix)
            (Ue.setIx ix (VNum target) env)
        ]
    | otherwise = []
-- U-Add[1/2]
exprUpdate env (Add e1 e2) target =
    let v1 = evalExpr env e1
        v2 = evalExpr env e2 -- evalutate both params
        lhsResults =
            -- try updating left side
            [ UpdateResult (Add r.updatedExpr e2) r.updatedEnv
            | r <- exprUpdate env e1 (target - v2)
            ]
        rhsResults =
            -- try updating right side
            [ UpdateResult (Add e1 r.updatedExpr) r.updatedEnv
            | r <- exprUpdate env e2 (target - v1)
            ]
     in lhsResults <> rhsResults
-- U-Mul[1/2]
exprUpdate env (Mul e1 e2) target =
    let v1 = evalExpr env e1
        v2 = evalExpr env e2 -- evalutate both params
        lhsResults =
            -- try updating left side
            [ UpdateResult (Mul r.updatedExpr e2) r.updatedEnv
            | div' <- maybeToList (safeDiv target v2)
            , r <- exprUpdate env e1 div'
            ]
        rhsResults =
            -- try updating right side
            [ UpdateResult (Mul e1 r.updatedExpr) r.updatedEnv
            | div' <- maybeToList (safeDiv target v1)
            , r <- exprUpdate env e2 div'
            ]
     in lhsResults <> rhsResults
-- U-Recip
exprUpdate env (Recip e) target =
    [ UpdateResult (Recip (updatedExpr r)) (updatedEnv r)
    | t <- maybeToList (safeDiv 1 target)
    , r <- exprUpdate env e t
    ]
-- U-Let, which differs a bit from the paper
exprUpdate sigma (Let e1 o) v' =
    let v1 = evalExpr sigma e1 -- sigma |- e_1 ⇓ v_1
        extendedEnv = Ue.ECons (VNum v1) sigma -- sigma[x ↦ v_1]
     in do
            -- sigma[x ↦ v_1] |- o : τ ⇑ v' ↝ (sigma_outer[x ↦ v_1'], o')
            UpdateResult o' sigma_outer_ext <- exprUpdate extendedEnv o v'
            -- decompose sigma_outer to get v_1', the updated value for the bound variable
            let Ue.ECons (VNum v_1') sigma_outer = sigma_outer_ext

            -- sigma_outer |- e_1 : η ⇑ v_1' ↝ (sigma', e_1')
            UpdateResult e_1' sigma' <- exprUpdate sigma_outer e1 v_1'

            -- make sure the candidate update is valid by re-evaluating it
            let candidate = Let e_1' o'
            guard (approxEq (evalExpr sigma' candidate) v')

            pure (UpdateResult candidate sigma')
