{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}

{- | we mostly use Relude, but we override the 'fromInteger' and 'fromIntegral' functions
to require an explicit type annotation for some extra safety (since these functions are a bit unsafe)
-}
module Prelude (
    module P,
    fromInteger,
    fromIntegral,
)
where

import Relude as P hiding (
    fromInteger,
    fromIntegral,
    state, -- we never use this and it causes name clashes
 )
import Relude qualified as PAll

-- | overriden 'fromInteger' to require more explicit typing
fromInteger :: forall a -> (Num a) => Integer -> a
fromInteger a = PAll.fromInteger @a

fromIntegral :: forall a -> (Integral b, Num a) => b -> a
fromIntegral a = PAll.fromIntegral @_ @a
