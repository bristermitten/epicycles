import Epicycles.Delta
import Epicycles.FuseDM.AST

/-!
# Delta operations on the let-normal AST

This code was generated with the assistance of AI

Mirrors the operations in `Epicycles.Delta` (`embed`, `isFreeIn`,
`compareOperator`, `optMerge`, `optMergeLet`) but for the
bipartite types `NumExpr` / `Curve` / `Program`.

The delta-environment type (`DeltaEnv`) and the comparison primitive
(`compareOperator`) are reused from `Epicycles.Delta` — they're
language-agnostic.
-/


-- ============================================================================
-- Free-variable predicates
-- ============================================================================

def NumExpr.isFreeIn {n : Nat} (ix : Fin n) : NumExpr n → Bool
  | .lit _ => false
  | .var j => ix == j
  | .add e1 e2 | .mul e1 e2 => e1.isFreeIn ix || e2.isFreeIn ix
  | .recip e => e.isFreeIn ix

def Curve.isFreeIn {n : Nat} (ix : Fin n) : Curve n → Bool
  | .epicycle _ r w p => r.isFreeIn ix || w.isFreeIn ix || p.isFreeIn ix
  | .append c1 c2 => c1.isFreeIn ix || c2.isFreeIn ix

def Program.isFreeIn {n : Nat} (ix : Fin n) : Program n → Bool
  | .done c => c.isFreeIn ix
  | .letBind e1 body => e1.isFreeIn ix || body.isFreeIn ix.succ


-- ============================================================================
-- Embedding deltas into the bipartite AST
-- ============================================================================

/-- Embed a `NumDelta` into a `NumExpr`. -/
def embedNumDeltaInto {n : Nat} (d : NumDelta) (e : NumExpr n) : NumExpr n :=
  d.foldr (fun op acc => match op with
    | .add v => .add (.lit v) acc
    | .mul v => .mul (.lit v) acc
    | .replace v => .lit v) e

def NumExpr.embed {n : Nat} (env : DeltaEnv n) : NumExpr n → NumExpr n
  | .lit v => .lit v
  | .var ix => embedNumDeltaInto (env ix) (.var ix)
  | .add e1 e2 => .add (e1.embed env) (e2.embed env)
  | .mul e1 e2 => .mul (e1.embed env) (e2.embed env)
  | .recip e => .recip (e.embed env)

def Curve.embed {n : Nat} (env : DeltaEnv n) : Curve n → Curve n
  | .epicycle k r w p => .epicycle k (r.embed env) (w.embed env) (p.embed env)
  | .append c1 c2 => .append (c1.embed env) (c2.embed env)

def Program.embed {n : Nat} (env : DeltaEnv n) : Program n → Program n
  | .done c => .done (c.embed env)
  | .letBind e1 body => .letBind (e1.embed env) (body.embed (env.extend []))


-- ============================================================================
-- Free-variable-aware merge of two delta environments
--
-- (`compareOperator` is generic over the underlying AST: it just takes two
-- delta environments and two free-variable predicates.)
-- ============================================================================

/-- Compare two delta environments via their effect on free variables.
Returns a triple `(eM, e1I, e2I)`:

* `eM`  — the merged "outer" environment.
* `e1I` — the residual `DeltaEnv` to embed into the **first** operand.
* `e2I` — the residual `DeltaEnv` to embed into the **second** operand.

The exact rules are:

* If both envs agree on `i`, or `i` is not free in the second operand,
  use `env1 i` for the merge and embed nothing.
* Else, if `i` is not free in the first operand, use `env2 i` and
  embed nothing.
* Otherwise, split a common suffix off `(env1 i, env2 i)` — the
  shared part becomes the merged env at `i`, and the residuals
  go into `e1I i` / `e2I i`.
-/
def compareOperator {n : Nat} (env1 env2 : DeltaEnv n)
    (free1 free2 : Fin n → Bool) :
    DeltaEnv n × DeltaEnv n × DeltaEnv n :=
  let eM := fun i =>
    if env1 i == env2 i || not (free2 i) then env1 i
    else if not (free1 i) then env2 i
    else (env1 i).splitSuffix (env2 i) |>.fst

  let e1I := fun i =>
    if env1 i == env2 i || not (free2 i) then []
    else if not (free1 i) then []
    else (env1 i).splitSuffix (env2 i) |>.snd.fst

  let e2I := fun i =>
    if env1 i == env2 i || not (free2 i) then []
    else if not (free1 i) then []
    else (env1 i).splitSuffix (env2 i) |>.snd.snd

  (eM, e1I, e2I)


-- ============================================================================
-- opt merges on the bipartite AST
-- ============================================================================

/-- Merge two delta environments into a `NumExpr`/`NumExpr` pair. -/
def optMergeNum {n : Nat} (env1 env2 : DeltaEnv n) (e1 e2 : NumExpr n) :
    DeltaEnv n × NumExpr n × NumExpr n :=
  let (eM, e1I, e2I) := compareOperator env1 env2 (e1.isFreeIn ·) (e2.isFreeIn ·)
  (eM, e1.embed e1I, e2.embed e2I)

/-- Merge two delta environments into a `Curve`/`Curve` pair. -/
def optMergeCurve {n : Nat} (env1 env2 : DeltaEnv n) (c1 c2 : Curve n) :
    DeltaEnv n × Curve n × Curve n :=
  let (eM, c1I, c2I) := compareOperator env1 env2 (c1.isFreeIn ·) (c2.isFreeIn ·)
  (eM, c1.embed c1I, c2.embed c2I)

/-- Merge for the let-construct in a `Program`: outer env over the bound
`NumExpr`, inner env over the body `Program (n+1)`. -/
def optMergeLetProgram {n : Nat} (envVal envBody : DeltaEnv n)
    (e1 : NumExpr n) (body : Program (n + 1)) :
    DeltaEnv n × NumExpr n × Program (n + 1) :=
  let (eM, e1I, e2I) :=
    compareOperator envVal envBody (e1.isFreeIn ·) (body.isFreeIn ·.succ)
  (eM, e1.embed e1I, body.embed (e2I.extend []))
