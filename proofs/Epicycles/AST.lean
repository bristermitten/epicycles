/-! Lean implementation of the AST.
Generated WITHOUT the assistance of AI
-/

/-- Our numeric expression language -/
inductive Expr : Nat → Type where
  | lit   : {n : Nat} → Rat → Expr n
  | var   : {n : Nat} → Fin n → Expr n
  | add   : {n : Nat} → Expr n → Expr n → Expr n
  | mul   : {n : Nat} → Expr n → Expr n → Expr n
  | recip : {n : Nat} → Expr n → Expr n
  | let_  : {n : Nat} → Expr n → Expr (n + 1) → Expr n
  deriving Repr

abbrev EpicycleId := Nat

inductive CurveExpr (n : Nat) : Type
  | epicycle : Expr n → Expr n → Expr n → CurveExpr n
  | append   : CurveExpr n → CurveExpr n → CurveExpr n
  deriving Repr

/-- Environment type. Rather than using an explicit list, we use a function of naturals <= n to values -/
abbrev Env (n : Nat) := Fin n → Rat

/-- pretty output for environments -/
instance {n : Nat} : Repr (Env n) where
  reprPrec env prec := reprPrec (List.ofFn env) prec
