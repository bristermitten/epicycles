import Epicycles.Delta
import Epicycles.FuseDM.AST
import Epicycles.FuseDM.Eval
import Epicycles.FuseDM.Delta

/-!
# Delta-based backwards semantics on let-normal-form programs

This code was generated with the assistance of AI

The numeric language is bipartite: by the **T-Let** typing rule only
numeric values can be bound in `let`s, so curves cannot live inside a
numeric expression.  Consequently every well-typed program normalises
to the form

  let x₁ = e₁ in let x₂ = e₂ in … let xₙ = eₙ in C

— a stack of `let` bindings (each binding a let-free `NumExpr`) ending
in a `Curve`.  This is exactly the `Program` type defined in
[`Epicycles.Normal.AST`](file:///Epicycles/Normal/AST.lean).

The bipartite structure splits the backwards semantics into three
independent, **non-mutually-recursive** layers:

* `backwardEvalAtomic`: structural recursion on `NumExpr`.
* `backwardEvalNum`: a `List.foldr` over `backwardEvalAtomic`.
* `backwardEvalCurve`: structural recursion on `Curve`; calls the
  numeric layer only.
* `backwardEvalProgram`: structural recursion on the let-block layer
  of `Program`; calls `backwardEvalCurve` and `backwardEvalNum`, never
  itself.

There is no mutual recursion and no fuel parameter anywhere.

## D-Let, faithfully implemented

The dissertation's D-Let rule (in let-normal form) is

  Δ ⊢ dv ◁ (let x = e₁ in body) ⤳ (Δᴹ, let x = e₁'' in body'')

with premises

  σ ⊢ e₁ ⇓ v₁
  σ[x↦v₁], Δ[x↦id] ⊢ dv ◁ body ⤳ (Δ_body[x↦dv_x], body')
  Δ ⊢ dv_x ◁ e₁ ⤳ (Δ_val, e₁')
  ⟨Δ_val, e₁'⟩ ⋈ ⟨Δ_body, body'⟩ ⤳ (Δᴹ, e₁'', body'')

Premise 3 — `Δ ⊢ dv_x ◁ e₁` — applies a `NumDelta` to the let-free
`NumExpr` value `e₁`.  In the bipartite setting that is exactly
`backwardEvalNum dv_x e₁`, which is a plain `foldr`.  No recursion
back into `backwardEvalProgram` is needed.
-/


-- ============================================================================
-- Numeric layer: backwardEvalAtomic on `NumExpr` — structurally recursive
-- ============================================================================

/--
Apply a single atomic delta backwards over a let-free `NumExpr`.
Structurally recursive on the expression.
-/
def backwardEvalAtomic {n : Nat} (d : AtomicNumDelta) (vals : Env n)
    (deltas : DeltaEnv n) (e : NumExpr n) : DeltaEnv n × NumExpr n :=
  match e, d with
  | _, .replace v => (DeltaEnv.id n, .lit v)

  | .lit v, .add _ => (deltas, .lit (d.apply v))
  | .lit v, .mul _ => (deltas, .lit (d.apply v))
  | .var i, .add _ => (deltas.update i (d :: deltas i), .var i)
  | .var i, .mul _ => (deltas.update i (d :: deltas i), .var i)

  | .add e1 e2, .add _ =>
      let (env1, e1') := backwardEvalAtomic d vals deltas e1
      let (eM, e1'', e2'') := optMergeNum env1 deltas e1' e2
      (eM, .add e1'' e2'')
  -- D-Add-Mul: distribute m * (e1 + e2) = m*e1 + m*e2.
  -- Both branches need the delta; descend into both starting from `deltas`,
  -- then merge.  (Threading would be unsound when e1 and e2 share variables.)
  | .add e1 e2, .mul _ =>
      let (env1, e1') := backwardEvalAtomic d vals deltas e1
      let (env2, e2') := backwardEvalAtomic d vals deltas e2
      let (eM, e1'', e2'') := optMergeNum env1 env2 e1' e2'
      (eM, .add e1'' e2'')

  -- D-Add-Mul / D-Add-Embed.
  -- Evaluate `e2` under the user-visible env `(Δ ▷ σ)`, not `σ`, so the
  -- divisor reflects any pending deltas.  The recursive call on `e1`
  -- still receives the *original* `vals`; the recursive call will
  -- recompute `(Δ ▷ σ)` itself.  (Passing `sigma'` would double-apply
  -- `Δ` once more inside the recursion and break PutGet on nested
  -- expressions like `recip(recip(x))`.)
  | .mul e1 e2, .add x =>
      let sigma' := deltas.apply vals
      let n2 := evalNumExpr sigma' e2
      if n2 = 0 then
        (deltas, embedNumDeltaInto [d] (.mul e1 e2))
      else
        let (env1, e1') :=
          backwardEvalAtomic (.add (x / n2)) vals deltas e1
        let (eM, e1'', e2'') := optMergeNum env1 deltas e1' e2
        (eM, .mul e1'' e2'')
  | .mul e1 e2, .mul _ =>
      let (env1, e1') := backwardEvalAtomic d vals deltas e1
      let (eM, e1'', e2'') := optMergeNum env1 deltas e1' e2
      (eM, .mul e1'' e2'')

  -- D-Add-Recip / D-Add-Recip-Embed.
  -- Evaluate `x` under `(Δ ▷ σ)` so the linearisation point `vx` is the
  -- current user-visible value, not the original σ-value.  The recursive
  -- call still receives the *original* `vals`; the env-update mechanism
  -- inside the recursive call already accumulates `deltas` correctly.
  | .recip x, .add v =>
      let sigma' := deltas.apply vals
      let vx := evalNumExpr sigma' x
      if vx = 0 then
        (deltas, embedNumDeltaInto [d] (.recip x))
      else if vx⁻¹ + v = 0 then
        (deltas, embedNumDeltaInto [d] (.recip x))
      else
        let (env, x') :=
          backwardEvalAtomic (.add ((vx⁻¹ + v)⁻¹ - vx)) vals deltas x
        (env, .recip x')
  | .recip x, .mul m =>
      if m = 0 then
        (deltas, embedNumDeltaInto [d] (.recip x))
      else
        let (env, x') := backwardEvalAtomic (.mul (1 / m)) vals deltas x
        (env, .recip x')


-- ============================================================================
-- backwardEvalNum: foldr over NumDelta — no recursion of its own
-- ============================================================================

/-- Apply a list of atomic deltas backwards (right-to-left) to a
let-free `NumExpr`.  Just a `List.foldr` of `backwardEvalAtomic`. -/
def backwardEvalNum {n : Nat} (ds : NumDelta) (vals : Env n)
    (deltas : DeltaEnv n) (e : NumExpr n) : DeltaEnv n × NumExpr n :=
  ds.foldr
    (fun d acc =>
      let (delt', e') := acc
      backwardEvalAtomic d vals delt' e')
    (deltas, e)

@[simp] theorem backwardEvalNum_nil {n : Nat} (vals : Env n)
    (deltas : DeltaEnv n) (e : NumExpr n) :
    backwardEvalNum [] vals deltas e = (deltas, e) := rfl

@[simp] theorem backwardEvalNum_cons {n : Nat} (d : AtomicNumDelta)
    (ds' : NumDelta) (vals : Env n) (deltas : DeltaEnv n) (e : NumExpr n) :
    backwardEvalNum (d :: ds') vals deltas e =
      (let (delt', e') := backwardEvalNum ds' vals deltas e
       backwardEvalAtomic d vals delt' e') := rfl


-- ============================================================================
-- Curve layer: backwardEvalCurve on `Curve` — structurally recursive
--
-- As you observed: curve updates only descend into numeric expressions
-- and never back, so this layer is purely structural on `Curve`.
-- ============================================================================

/-- Apply a `CurveDelta` backwards to a let-free `Curve`. -/
def backwardEvalCurve {n : Nat} (dv : CurveDelta) (vals : Env n)
    (deltas : DeltaEnv n) (c : Curve n) : DeltaEnv n × Curve n :=
  match dv, c with
  -- D-Curve-Id
  | .id, _ => (deltas, c)

  -- D-TargetEpi (hit): apply dR/dW/dP to the three numeric components,
  -- then merge their delta envs across the (free-variable-aware)
  -- `compareOperator`.
  | .targetEpi targetId dR dW dP, .epicycle eid r w p =>
      if targetId = eid then
        let (envR, r') := backwardEvalNum dR vals deltas r
        let (envW, w') := backwardEvalNum dW vals deltas w
        let (envP, p') := backwardEvalNum dP vals deltas p
        let (envRW, envRI, envWI) :=
          compareOperator envR envW (r'.isFreeIn ·) (w'.isFreeIn ·)
        let r'' := r'.embed envRI
        let w'' := w'.embed envWI
        let (eM, envRWI, envPI) :=
          compareOperator envRW envP
            (fun i => r''.isFreeIn i || w''.isFreeIn i)
            (p'.isFreeIn ·)
        (eM, .epicycle eid (r''.embed envRWI) (w''.embed envRWI) (p'.embed envPI))
      else
        -- D-TargetEpi (miss): identity on this epicycle
        (deltas, .epicycle eid r w p)

  -- D-TargetEpi (descend through append): broadcast `dv` to both halves
  -- and merge.  Recursive calls on structurally smaller `c1`, `c2`.
  | .targetEpi _ _ _ _, .append c1 c2 =>
      let (env1, c1') := backwardEvalCurve dv vals deltas c1
      let (env2, c2') := backwardEvalCurve dv vals deltas c2
      let (eM, c1'', c2'') := optMergeCurve env1 env2 c1' c2'
      (eM, .append c1'' c2'')

  -- D-ModAppend on append: route `dL` to `c1`, `dR` to `c2`.
  -- Both halves start from `deltas` independently and the resulting envs are
  -- merged.  (Threading `env1` into `c2`'s call would be unsound when c1 and
  -- c2 share free variables.)
  | .modAppend dL dR, .append c1 c2 =>
      let (env1, c1') := backwardEvalCurve dL vals deltas c1
      let (env2, c2') := backwardEvalCurve dR vals deltas c2
      let (eM, c1'', c2'') := optMergeCurve env1 env2 c1' c2'
      (eM, .append c1'' c2'')

  -- D-ModAppend on epicycle: structurally a no-op.
  | .modAppend _ _, .epicycle eid r w p =>
      (deltas, .epicycle eid r w p)


-- ============================================================================
-- Program layer: backwardEvalProgram on `Program` — structurally
-- recursive on the let-block layer; calls the `Curve` and numeric
-- layers only (one-way), never itself.
-- ============================================================================

/-- Apply a `CurveDelta` backwards to a let-normal `Program`.
Structurally recursive on the let-block layer.

In the `letBind` case we faithfully implement D-Let:
recurse on the body (smaller `Program`), extract `dv_x` from the
returned env, apply `dv_x` to the let value `e₁` via
`backwardEvalNum`, then merge through `optMergeLetProgram`. -/
def backwardEvalProgram {n : Nat} (dv : CurveDelta) (vals : Env n)
    (deltas : DeltaEnv n) (P : Program n) : DeltaEnv n × Program n :=
  match P with
  | .done c =>
      let (deltas', c') := backwardEvalCurve dv vals deltas c
      (deltas', .done c')
  | .letBind e1 body =>
      -- D-Let premise 1: σ ⊢ e₁ ⇓ v₁.  We use the **user-visible** env
      -- `(Δ ▷ σ)`, not `σ`, so the let-bound value reflects any pending
      -- outer deltas.  This is what makes `(Δ', P')` semantically equivalent
      -- to "Δ applied to (Δ, P)" at the program level.
      let v1 := evalNumExpr (deltas.apply vals) e1
      -- D-Let premise 2: recurse on the body (structurally smaller).
      let (envBody, body') :=
        backwardEvalProgram dv (vals.extend v1) (deltas.extend []) body
      let dv_x : NumDelta := envBody 0
      let deltaBody : DeltaEnv n := fun i => envBody i.succ
      -- D-Let premise 3: Δ ⊢ dv_x ◁ e₁.  `e₁` is a `NumExpr` (let-free),
      -- so this is `backwardEvalNum`, a plain foldr.
      let (envVal, e1') := backwardEvalNum dv_x vals deltas e1
      -- D-Let premise 4: ⟨Δ_val, e₁'⟩ ⋈ ⟨Δ_body, body'⟩.
      let (eM, e1'', body'') :=
        optMergeLetProgram envVal deltaBody e1' body'
      (eM, .letBind e1'' body'')


-- ============================================================================
-- Lifting NumDelta (right-to-left fold) and CurveDelta sequences
-- ============================================================================

/-- Apply a `NumDelta` backwards to a `NumExpr` by folding from the right.
Identical to `backwardEvalNum` — provided for symmetry with the curve-
and program-level fold helpers below. -/
def backwardEvalNumList {n : Nat} (ds : NumDelta) (vals : Env n)
    (deltas : DeltaEnv n) (e : NumExpr n) : DeltaEnv n × NumExpr n :=
  backwardEvalNum ds vals deltas e

/-- Compose a list of `CurveDelta`s on a `Curve` by folding from the right. -/
def backwardEvalCurveList {n : Nat} (dvs : List CurveDelta) (vals : Env n)
    (deltas : DeltaEnv n) (c : Curve n) : DeltaEnv n × Curve n :=
  dvs.foldr
    (fun dv acc =>
      let (delt', c') := acc
      backwardEvalCurve dv vals delt' c')
    (deltas, c)

/-- Compose a list of `CurveDelta`s on a `Program` by folding from the right. -/
def backwardEvalProgramList {n : Nat} (dvs : List CurveDelta) (vals : Env n)
    (deltas : DeltaEnv n) (P : Program n) : DeltaEnv n × Program n :=
  dvs.foldr
    (fun dv acc =>
      let (delt', P') := acc
      backwardEvalProgram dv vals delt' P')
    (deltas, P)


-- ============================================================================
-- Basic theorems
-- ============================================================================

theorem backwardEvalNum_id {n : Nat} (vals : Env n) (deltas : DeltaEnv n)
    (e : NumExpr n) : backwardEvalNum [] vals deltas e = (deltas, e) := rfl

theorem backwardEvalProgram_done {n : Nat} (dv : CurveDelta) (vals : Env n)
    (deltas : DeltaEnv n) (c : Curve n) :
    backwardEvalProgram dv vals deltas (.done c) =
      (let (delt', c') := backwardEvalCurve dv vals deltas c
       (delt', .done c')) := rfl

@[simp] theorem backwardEvalCurve_id {n : Nat} (vals : Env n)
    (deltas : DeltaEnv n) (c : Curve n) :
    backwardEvalCurve .id vals deltas c = (deltas, c) := by
  cases c <;> rfl

@[simp] theorem backwardEvalCurve_modAppend_epicycle {n : Nat}
    (dL dR : CurveDelta) (vals : Env n) (deltas : DeltaEnv n)
    (eid : EpicycleId) (r w p : NumExpr n) :
    backwardEvalCurve (.modAppend dL dR) vals deltas (.epicycle eid r w p) =
      (deltas, .epicycle eid r w p) := rfl

@[simp] theorem backwardEvalCurve_modAppend_append {n : Nat}
    (dL dR : CurveDelta) (vals : Env n) (deltas : DeltaEnv n)
    (c1 c2 : Curve n) :
    backwardEvalCurve (.modAppend dL dR) vals deltas (.append c1 c2) =
      (let (env1, c1') := backwardEvalCurve dL vals deltas c1
       let (env2, c2') := backwardEvalCurve dR vals deltas c2
       let (eM, c1'', c2'') := optMergeCurve env1 env2 c1' c2'
       (eM, .append c1'' c2'')) := rfl

@[simp] theorem backwardEvalCurveList_nil {n : Nat} (vals : Env n)
    (deltas : DeltaEnv n) (c : Curve n) :
    backwardEvalCurveList [] vals deltas c = (deltas, c) := rfl

@[simp] theorem backwardEvalCurveList_cons {n : Nat} (dv : CurveDelta)
    (dvs' : List CurveDelta) (vals : Env n) (deltas : DeltaEnv n)
    (c : Curve n) :
    backwardEvalCurveList (dv :: dvs') vals deltas c =
      (let (delt', c') := backwardEvalCurveList dvs' vals deltas c
       backwardEvalCurve dv vals delt' c') := rfl

@[simp] theorem backwardEvalProgramList_nil {n : Nat} (vals : Env n)
    (deltas : DeltaEnv n) (P : Program n) :
    backwardEvalProgramList [] vals deltas P = (deltas, P) := rfl

@[simp] theorem backwardEvalProgramList_cons {n : Nat} (dv : CurveDelta)
    (dvs' : List CurveDelta) (vals : Env n) (deltas : DeltaEnv n)
    (P : Program n) :
    backwardEvalProgramList (dv :: dvs') vals deltas P =
      (let (delt', P') := backwardEvalProgramList dvs' vals deltas P
       backwardEvalProgram dv vals delt' P') := rfl
