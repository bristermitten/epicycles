{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

-- | the naive SnS update algorithm which just picks the first candidate no matter what
module Update.SnS.Naive (
    curveUpdateNaive,
)
where

import AST
import Update.SnS (exprUpdate)
import Update.SnS.Common
import Update.Types

curveUpdateNaive ::
    forall param env.
    (DiffEnv env, SelectParam param) =>
    EpicycleId ->
    EpicycleParamType param ->
    CurveState env ->
    Maybe (UpdateInfo env)
curveUpdateNaive epicycleId target state = do
    (cs, depth) <- genericCurveUpdate @param strategy epicycleId target state
    pure (UpdateInfo cs depth [])
  where
    strategy env expr tgt =
        case exprUpdate env expr tgt of
            [] -> Nothing
            (res@(UpdateResult _ _) : _) ->
                let depth = rankResult expr env res
                 in Just (res, depth)
