{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE UndecidableInstances #-}

-- A fairly simple implementation of the embedding approach described in
-- "Contextual Embeddings: Implementing Bound Variables through Instance Resolution"
module ContextualEmbeddings (
    Ctx (..),
    Env (..),
    Ix (..),
    lookEnv,
    setIx,
    ixToInt,
    safeProxyTop,
    ReifyIndex,
) where

type data Ctx k = Empty | Ctx k :/: k
infixl 3 :/:

data Env (f :: k -> Type) (ctx :: Ctx k) where
    ENil :: Env f Empty
    ECons :: f s -> Env f ctx -> Env f (ctx :/: s)

deriving instance (forall s. Show (f s)) => Show (Env f ctx)

data Ix (ctx :: Ctx k) (s :: k) where
    IxZ :: Ix (ctx :/: s) s
    IxS :: Ix ctx s -> Ix (ctx :/: s') s

deriving instance Show (Ix ctx s)

data ProxyTop (ctx :: Ctx k) (s :: k) where
    ProxyTop :: ProxyTop (ctx :/: s) s

{- | the index of the variable bound at @ctx :/: s@, as seen from the use-site context @use@
slightly sneaky workaround to avoid needing to export 'ProxyTop', which is disallowed in the CE paper
-}
safeProxyTop :: forall ctx s use. (ReifyIndex (ctx :/: s) use) => Ix use s
safeProxyTop = reify (ProxyTop :: ProxyTop (ctx :/: s) s)

class ReifyIndex bind use where reify :: ProxyTop bind s -> Ix use s

instance {-# OVERLAPPING #-} ReifyIndex ctx ctx where reify ProxyTop = IxZ
instance {-# OVERLAPPABLE #-} (ReifyIndex bind use, use' ~ (use :/: x)) => ReifyIndex bind use' where
    reify p = IxS (reify p)

lookEnv :: Env f ctx -> Ix ctx s -> f s
{- HLINT ignore "Redundant irrefutable pattern" -}
-- incorrect! we are using -XStrict
lookEnv ENil ~ix = case ix of {}
lookEnv (ECons v _) IxZ = v
lookEnv (ECons _ env) (IxS n) = lookEnv env n

setIx :: Ix ctx s -> f s -> Env f ctx -> Env f ctx
setIx IxZ f (ECons _ vs) = ECons f vs
setIx (IxS n) f (ECons v vs) = ECons v (setIx n f vs)

ixToInt :: Ix ctx x -> Int
ixToInt IxZ = 0
ixToInt (IxS n) = 1 + ixToInt n
