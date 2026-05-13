import Epicycles.AST

/-!
# Let-Normal Form AST

This code was generated with the assistance of AI

The DSL is bipartite: only numeric values can be bound in `let`s, and
curves cannot be nested inside numeric expressions.  Consequently the
language separates into three **non-mutually-recursive** layers:

  1. `NumExpr n`  — purely numeric expressions, no `let` bindings
  2. `Curve n`    — curve compositions; epicycle parameters are `NumExpr`s
  3. `Program n`  — variable binders: a stack of `let`s binding
                    `NumExpr`s, eventually ending in a `Curve`.

A program in **Let-Normal Form** is exactly a `Program n`:

  let x₁ = e₁ in let x₂ = e₂ in … let xₙ = eₙ in C

where every `eᵢ` is a `NumExpr` (no nested `let`s) and `C` is a `Curve`.

This is *not* a refactor of `Epicycles.AST` — `Epicycles.AST.Expr` is
left untouched.  The types here are an alternative representation that
is convenient for the delta-based backwards semantics because it makes
every recursion structural in its own type, with no mutual recursion
required.
-/

/-- The let-free **numeric** fragment. -/
inductive NumExpr : Nat → Type where
  | lit   : {n : Nat} → Rat → NumExpr n
  | var   : {n : Nat} → Fin n → NumExpr n
  | add   : {n : Nat} → NumExpr n → NumExpr n → NumExpr n
  | mul   : {n : Nat} → NumExpr n → NumExpr n → NumExpr n
  | recip : {n : Nat} → NumExpr n → NumExpr n
  deriving Repr

/-- A **curve** composition: an epicycle (with three `NumExpr`
parameters) or an `append` of two curves.  Curves themselves contain
no `let` bindings — those have been floated to the surrounding
`Program`. -/
inductive Curve : Nat → Type where
  | epicycle : {n : Nat} → EpicycleId → NumExpr n → NumExpr n → NumExpr n → Curve n
  | append   : {n : Nat} → Curve n → Curve n → Curve n
  deriving Repr

/-- A **program** in let-normal form: a stack of `let` bindings (each
binding a `NumExpr`) ending in a `Curve`. -/
inductive Program : Nat → Type where
  | done    : {n : Nat} → Curve n → Program n
  | letBind : {n : Nat} → NumExpr n → Program (n + 1) → Program n
  deriving Repr
