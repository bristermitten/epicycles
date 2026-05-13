{-# OPTIONS_GHC -Wno-orphans #-}

{- | dirty, slightly evil orphan instances for AST types.
none of these are required for any functionality
but they make writing DSL terms a little nicer, especially for demos
-}
module AST.Instances () where

import AST
import GHC.Num (fromInteger)
import GHC.Real qualified
import Numeric (log)

instance {-# INCOHERENT #-} (Expr e) => Num (e (SNum Double)) where
    (+) = add
    (*) = mul
    negate = mul (lit (-1))
    abs _ = error "abs is not implemented for Expr"
    signum _ = error "signum is not implemented for Expr"
    fromInteger n = lit (GHC.Num.fromInteger n)

instance {-# INCOHERENT #-} (Expr e) => Num (e (SNum Int)) where
    (+) = add
    (*) = mul
    negate = mul (lit (-1))
    abs _ = error "abs is not implemented for Expr"
    signum _ = error "signum is not implemented for Expr"
    fromInteger n = lit (GHC.Num.fromInteger n)

instance {-# INCOHERENT #-} (Expr e) => Num (e (SNum Rational)) where
    (+) = add
    (*) = mul
    negate = mul (lit (-1))
    abs _ = error "abs is not implemented for Expr"
    signum _ = error "signum is not implemented for Expr"
    fromInteger n = lit (GHC.Num.fromInteger n)

instance {-# INCOHERENT #-} (Expr e) => Fractional (e (SNum Double)) where
    recip = AST.recip
    fromRational r = lit (GHC.Real.fromRational r)

instance {-# INCOHERENT #-} (Expr e) => Fractional (e (SNum Rational)) where
    recip = AST.recip
    fromRational = lit

instance {-# INCOHERENT #-} (Expr e) => Floating (e (SNum Rational)) where
    pi = lit (toRational (pi :: Double))
    exp = error "exp is not implemented for Expr"
    log = error "log is not implemented for Expr"
    sin = error "sin is not implemented for Expr"
    cos = error "cos is not implemented for Expr"
    asin = error "asin is not implemented for Expr"
    acos = error "acos is not implemented for Expr"
    atan = error "atan is not implemented for Expr"
    sinh = error "sinh is not implemented for Expr"
    cosh = error "cosh is not implemented for Expr"
    asinh = error "asinh is not implemented for Expr"
    acosh = error "acosh is not implemented for Expr"
    atanh = error "atanh is not implemented for Expr"
