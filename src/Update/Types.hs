{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}

module Update.Types (
    EpicycleParam (..),
    EpicycleParamType,
    EpicycleParamLens (..),
    SelectParam (..),
)
where

import AST (AST (..), ASTSort (SCurve, SNum), BindableNum, EpicycleId, EpicycleParam (..), EpicycleParamType, Stage (Numbered))


-- | a lens-like structure that lets us focus on a specific parameter of a specific epicycle in the curve's AST,
-- and rebuild the whole curve AST after updating that parameter
data EpicycleParamLens param env = EpicycleParamLens
    { currentValue :: AST Numbered env (SNum (EpicycleParamType param))
    , rebuild :: EpicycleId -> AST Numbered env (SNum (EpicycleParamType param)) -> AST Numbered env SCurve
    }

class (BindableNum (EpicycleParamType param)) => SelectParam (param :: EpicycleParam) where
    selectParam ::
        AST Numbered env (SNum Rational) ->
        AST Numbered env (SNum Int) ->
        AST Numbered env (SNum Rational) ->
        EpicycleParamLens param env

instance SelectParam Radius where
    selectParam r f p =
        EpicycleParamLens r $ \eid r' -> Epicycle eid r' f p

instance SelectParam Frequency where
    selectParam r f p =
        EpicycleParamLens f $ \eid f' -> Epicycle eid r f' p

instance SelectParam Phase where
    selectParam r f p =
        EpicycleParamLens p $ \eid p' -> Epicycle eid r f p'
