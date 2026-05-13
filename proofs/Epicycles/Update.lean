
import Epicycles.AST
import Epicycles.Eval
import Epicycles.Env
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith.Frontend

/-! Lean implementation of the SnS update algorithm.
Generated WITHOUT the assistance of AI
-/

/-- Division that is safe for division by 0 -/
def safeDiv (a b : Rat) : Option Rat :=
  if b = 0 then none else some (a / b)

/-- safeDiv returns none for b == 0 -/
theorem safeDiv_zero {a : Rat} : safeDiv a 0 = none := by
  simp [safeDiv]

/-- safeDiv returns some for b != 0 -/
theorem safeDiv_some {a  b : Rat} (h : b ≠ 0) : safeDiv a b = some (a / b) := by
  simp [safeDiv, h]


-- analogous to UpdateResult in Trace.hs
structure UpdateResult (n : Nat) : Type where
  expr : Expr n
  env : Env n
deriving Repr

/-- Equality of UpdateResults -/
def updateResult_eq {n : Nat}  (r: UpdateResult n) (e: Expr n) (env : Env n) : Prop :=
    r.expr = e ∧ r.env = env


/-- Non-deterministic backwards semantics -/
def mapUpdate {n : Nat} (f : Expr n -> Expr n) (r : UpdateResult n) : UpdateResult n :=
  { expr := f r.expr, env := r.env }

-- non-deterministic backwards semantics
def exprUpdate {n : Nat} (env : Env n) (e : Expr n) (targetVal : Rat) :
    List (UpdateResult n) :=
    match e with
      -- U-Const
      | Expr.lit _ => [ { expr := Expr.lit targetVal, env := env } ]
      -- U-Var
      | Expr.var i => [ { expr := Expr.var i, env := Env.update env i targetVal } ]

      -- U-Add[1/2]
      | Expr.add e1 e2 =>
        let v1 := evalExpr env e1
        let v2 := evalExpr env e2

        -- U-Add-1:
        (exprUpdate env e1 (targetVal - v2)).map (fun r =>
          { expr := Expr.add r.expr e2, env := r.env }) ++
        -- U-Add-2:
        (exprUpdate env e2 (targetVal - v1)).map (fun r =>
          { expr := Expr.add e1 r.expr, env := r.env })

      -- U-Mul[1/2]
      | Expr.mul e1 e2 =>
        let v1 := evalExpr env e1
        let v2 := evalExpr env e2

        -- U-Mul-1:
        let b1 := match safeDiv targetVal v2 with
          | some t1 => (exprUpdate env e1 t1).map (fun r => { expr := .mul r.expr e2, env := r.env })
          | none => if targetVal = 0 then [{ expr := .mul e1 e2, env := env }] else []
      -- U-Mul-2
        let b2 := match safeDiv targetVal v1 with
          | some t2 => (exprUpdate env e2 t2).map (fun r => { expr := .mul e1 r.expr, env := r.env })
          | none => if targetVal = 0 then [{ expr := .mul e1 e2, env := env }] else []
      b1 ++ b2

      -- U-Recip
      | Expr.recip e =>
        match safeDiv 1 targetVal with
          | some t => (exprUpdate env e t).map (fun r => { expr := .recip r.expr, env := r.env })
          | none => []
      -- U-Let
      | Expr.let_ e1 o =>
            let v1 := evalExpr env e1
            let extEnv := Env.extend env v1

            (exprUpdate extEnv o targetVal).flatMap fun r =>
              let v1' := r.env 0
              let bodyResults := exprUpdate env e1 v1'
              bodyResults.filterMap fun r2 =>
                let candidate := Expr.let_ r2.expr r.expr
                -- PutGet guard
                if evalExpr r2.env candidate = targetVal then
                  some { expr := candidate, env := r2.env }
                else none



/-- Helper proving getPut over some list of UpdateResults with regards to some AST wrapping function -/
lemma getPut_map {n : Nat} {env : Env n} {e : Expr n} {targetVal : Rat}
  (f : Expr n -> Expr n)
  (ih : ∀ r ∈ exprUpdate env e targetVal, updateResult_eq r e env ) :
  ∀ r ∈ (exprUpdate env e targetVal).map (mapUpdate f),
    updateResult_eq r (f e) env := by
  intro r hr
  rcases List.mem_map.mp hr with ⟨r_inner, h_mem, rfl⟩
  rcases ih r_inner h_mem with ⟨rfl, rfl⟩
  simp [mapUpdate, updateResult_eq ]



/-- GetPut: updating to the current value does not change expression or env -/
theorem exprUpdate_getPut {n : Nat} (env : Env n) (e : Expr n) :
    ∀ r ∈ exprUpdate env e (evalExpr env e), updateResult_eq r e env := by
  induction e with
  | lit v =>
      intro r hr
      simp [exprUpdate, evalExpr] at hr
      subst hr
      exact ⟨rfl, rfl⟩
  | var i =>
      intro r hr
      simp [exprUpdate, evalExpr] at hr
      subst hr
      exact ⟨rfl, Env.update_same env i⟩

  | add e1 e2 ih1 ih2 =>
    intro r hr
    unfold exprUpdate at hr
    simp only [evalExpr] at hr
    ring_nf at hr

    cases List.mem_append.mp hr with
    | inl h_left =>
      -- U-Add-1 was used
      exact getPut_map (env:=env) (e:=e1)
        (targetVal:=evalExpr env e1)
        (f:=fun e => Expr.add e e2)
        (ih:=ih1 env) r h_left
    | inr h_right =>
      -- U-Add-2 was used
      exact getPut_map (env:=env) (e:=e2)
        (targetVal:=evalExpr env e2)
        (f:=fun e => Expr.add e1 e)
        (ih:=ih2 env) r h_right
  | mul e1 e2 ih1 ih2 =>
    intro r hr
    unfold exprUpdate at hr
    simp only [evalExpr] at hr
    ring_nf at hr

    cases List.mem_append.mp hr with
    | inl h_left =>
      -- U-Mul-1 (requires e2 != 0)
      by_cases hz : evalExpr env e2 = 0
        -- Case: v2 = 0 (safeDiv returns none, but the target is 0, so the fallback catches it)
      · have ht : evalExpr env e1 * evalExpr env e2 = 0 := by simp [hz]
        simp [hz, safeDiv] at h_left
        subst h_left
        exact ⟨rfl, rfl⟩
      · rw [safeDiv_some hz, mul_div_cancel_right₀ _ hz] at h_left
        exact getPut_map (env:=env) (e:=e1)
          (targetVal:=evalExpr env e1)
          (f:=fun e => Expr.mul e e2)
          (ih:=ih1 env) r h_left
    | inr h_right =>
    --  U-Mul-1, same reasoning as left, but for e1 instead of e2
      by_cases hz : evalExpr env e1 = 0
      · have ht : evalExpr env e1 * evalExpr env e2 = 0 := by simp [hz]
        simp [hz, safeDiv] at h_right
        subst h_right
        exact ⟨rfl, rfl⟩
      · rw [safeDiv_some hz, mul_div_cancel_left₀ _ hz] at h_right
        exact getPut_map (env:=env) (e:=e2)
          (targetVal:=evalExpr env e2)
          (f:=fun e => Expr.mul e1 e)
          (ih:=ih2 env) r h_right
  | recip e ih =>
    intro r hr
    simp [exprUpdate, evalExpr] at hr

    -- U-Recip only holds if (1/v') is updatable,
    by_cases hz : evalExpr env e = 0
    · -- case 1: e = 0, safeDiv = none
      have ht : (evalExpr env e)⁻¹ = 0 := by simp [hz]
      simp [hz, safeDiv] at hr


    . --case 2: e != 0
      have hz_inv : (evalExpr env e)⁻¹ ≠ 0 := inv_ne_zero hz
      rw [safeDiv_some hz_inv] at hr
      simp only [one_div, inv_inv] at hr

      -- apply inductive hypothesis for e
      exact getPut_map (env:=env) (e:=e)
        (targetVal:=evalExpr env e)
        (f:=Expr.recip)
        (ih:=ih env) r hr

  |  let_ e1 o ihe1 iho =>
    intro r hr
    simp only [ evalExpr] at hr

    -- unpack the flatMap, apply induction to the body (o)
    rcases List.mem_flatMap.mp hr with ⟨r_inner, h_mem, h_eq⟩
    have ih_o := iho (env.extend (evalExpr env e1)) r_inner h_mem
    rcases ih_o with ⟨h_expr, h_env⟩

    -- substitute body results, simplify the environment
    subst h_expr
    rw [h_env, Env.extend_zero] at h_eq

    -- unpack filterMap, apply induction to the val (e1)
    rcases List.mem_filterMap.mp h_eq with ⟨r_body, h_mem_body, h_eq_body⟩
    have ih_e1_applied := ihe1 env r_body h_mem_body
    rcases ih_e1_applied with ⟨h_expr_body, h_env_body⟩
    subst h_expr_body h_env_body

    -- evaluate the PutGet guard and finish proof
    simp only [evalExpr, ite_true] at h_eq_body
    injection h_eq_body with h_candidate_eq
    subst h_candidate_eq
    simp [updateResult_eq ]


/-- property that an expression is valid, i.e. does not contain division by zero -/
def isValid {n : Nat} (σ : Env n) : Expr n → Prop
  | .lit _ => True
  | .var _ => True
  | .add e1 e2 => isValid σ e1 ∧ isValid σ e2
  | .mul e1 e2 => isValid σ e1 ∧ isValid σ e2
  | .recip e => isValid σ e ∧ evalExpr σ e ≠ 0
  | .let_ e1 o => isValid σ e1 ∧   ∀ v, isValid (σ.extend v) o


/--  Liveness: updating to the current value yields at least one result. -/
theorem exprUpdate_getPut_liveness {n : Nat} (env : Env n) (e : Expr n) (h_valid : isValid env e)  :
    ∃ r, r ∈ exprUpdate env e (evalExpr env e) := by
  induction e with
  | lit v =>
      simp [exprUpdate, evalExpr]
  | var i =>
      simp [exprUpdate, evalExpr]
  | add e1 e2 ih1 =>
      simp [exprUpdate,  evalExpr]
      have ⟨h_valid_e1, h_valid_e2⟩ := h_valid
      have h1 := ih1 env h_valid_e1
      rcases h1 with ⟨r_inner, h_mem⟩
      use { expr := r_inner.expr.add e2, env := r_inner.env }
      left
      use r_inner

  | mul e1 e2 ih1 ih2 =>
      simp only [exprUpdate, evalExpr]
      by_cases h2 : evalExpr env e2 = 0
      · -- Case 1: v2 = 0. safeDiv fails, but the target is 0, so the fallback catches it
        have ht : evalExpr env e1 * evalExpr env e2 = 0 := by simp [h2]
        simp [safeDiv, h2]
      · -- Case 2: v2 != 0. safeDiv succeeds, we can use the inductive hypothesis on e1
        rw [safeDiv_some h2]
        have h_cancel : evalExpr env e1 * evalExpr env e2 / evalExpr env e2 = evalExpr env e1 :=
          mul_div_cancel_right₀ _ h2
        rw [h_cancel]

        have ⟨h_valid_e1, h_valid_e2⟩ := h_valid
        have h1 := ih1 env h_valid_e1
        rcases h1 with ⟨r_inner, h_mem⟩
        use { expr := r_inner.expr.mul e2, env := r_inner.env }

        -- Prove it belongs to the left branch (b1)
        apply List.mem_append_left
        simp only [List.mem_map]
        use r_inner
  | recip e ih =>
      have ⟨h_valid_inner, h_not_zero⟩ := h_valid
      simp [exprUpdate, evalExpr]
      by_cases h : evalExpr env e = 0
      · -- Case 1: v = 0, contradicts isValid
        contradiction

      · -- Case 2: v != 0. safeDiv succeeds, we can use the inductive hypothesis on e
        rw [safeDiv_some (inv_ne_zero h)]
        simp only [one_div, inv_inv]

        have h1 := ih env h_valid_inner
        rcases h1 with ⟨r_inner, h_mem⟩
        use { expr := r_inner.expr.recip, env := r_inner.env }
        simp only [List.mem_map]
        use r_inner
  | let_ e1 o ihe1 iho =>
      simp  [exprUpdate, evalExpr]
      have ⟨h_valid_e1, h_valid_o⟩ := h_valid
      -- apply inductive hypothesis to body (o)
      have ⟨r_o, h_mem_o⟩ := iho (env.extend (evalExpr env e1)) ((h_valid_o (evalExpr env e1)))
      use r_o
      -- prove first case, that result comes from body update
      refine ⟨h_mem_o, ?_⟩

      -- so far we only have the existence of an update, need to show it is valid
      -- use GetPut property to show that environment and expr were unchanged by induction on body
      have h_o_props := exprUpdate_getPut (env.extend (evalExpr env e1)) o r_o h_mem_o
      rcases h_o_props with ⟨h_ro_expr, h_ro_env⟩

      -- reduce r_o.env 0 = evalExpr env e1, r_o.expr = o
      subst h_ro_expr
      rw [h_ro_env, Env.extend_zero]

      -- apply inductive hypothesis to val (e1)
      have ⟨r_e1, h_mem_e1⟩ := ihe1 env h_valid_e1
      use r_e1
      refine ⟨h_mem_e1, ?_⟩

      -- similarly, use GetPut to show that environment and expr were unchanged by induction on val
      have h_e1_props := exprUpdate_getPut env e1 r_e1 h_mem_e1
      rcases h_e1_props with ⟨h_re1_expr, h_re1_env⟩
      subst h_re1_expr h_re1_env

      rfl



/-- Count occurrences of a variable index in an expression. -/
def countOccurrences {n :Nat} (i : Fin n) : Expr n → Nat
  | .lit _      => 0
  | .var j      => if i = j then 1 else 0
  | .add e1 e2  => countOccurrences i e1 + countOccurrences i e2
  | .mul e1 e2  => countOccurrences i e1 + countOccurrences i e2
  | .recip e    => countOccurrences i e
  | .let_ e1 o  => countOccurrences i e1 + countOccurrences i.succ o

-- Independence: no variable index appears more than once.
def isIndependent {n : Nat} : (Expr n) -> Prop
  | .lit _ => true
  | .var _ => true
  | .add e1 e2  =>
      isIndependent e1 ∧ isIndependent e2 ∧
      ∀ i : Fin n, countOccurrences i e1 + countOccurrences i e2 ≤ 1
  | .mul e1 e2 =>
      isIndependent e1 ∧ isIndependent e2 ∧
      ∀ i : Fin n, countOccurrences i e1 + countOccurrences i e2 ≤ 1
  | .recip e => isIndependent e
  | .let_ e1 o  =>
    isIndependent e1 ∧ isIndependent o ∧
    (∀ i : Fin n, countOccurrences i e1 + countOccurrences i.succ o ≤ 1) ∧
    (countOccurrences 0 o ≤ 1)

/-- If an updated variable @i@ does not occur in e, evaluation is unchanged. -/
theorem eval_env_update_independent {n : Nat} (env : Env n) (e : Expr n) (i : Fin n) (val : Rat) :
  countOccurrences i e = 0 → evalExpr (env.update i val) e = evalExpr env e := by
  induction e generalizing  val with
  | lit e => simp [evalExpr]
  | var j =>
      intro h
      simp [countOccurrences] at h
      simp [evalExpr]
      exact Env.update_ne env val (Ne.symm h)
  | add e1 e2 ih1 ih2 =>
      intro h
      simp [countOccurrences] at h
      simp [evalExpr]
      rw [ih1 env i val h.left, ih2 env i val h.right]
  | mul e1 e2 ih1 ih2 =>
      intro h
      simp [countOccurrences] at h
      simp [evalExpr]
      rw [ih1 env i val h.left, ih2 env i val h.right]
  | recip e1 ih =>
      intro h
      simp [countOccurrences] at h
      simp [evalExpr]
      rw [ih env i val h]
  | let_ e1 o ihe1 iho =>
    intro h
    simp [countOccurrences] at h
    simp [evalExpr]
    rw [ihe1 env i val h.left]
    have ih := iho (env.extend (evalExpr env e1)) i.succ val h.right
    rw [Env.extend_update_comm]
    exact ih



/-- disjointness: updating e1 does not affect evaluation of e2 if none of e1's variables occur in e2.
    a generalisation of eval_env_update_independent, sort of
 -/
theorem exprUpdate_preserves_eval_disjoint {n : Nat}
  (env : Env n) (e1 e2 : Expr n) (targetVal : Rat)
  (h_no_occ : ∀ i : Fin n, countOccurrences i e1 > 0 → countOccurrences i e2 = 0) :
  ∀ r ∈ exprUpdate env e1 targetVal, evalExpr r.env e2 = evalExpr env e2 := by
  induction e1 generalizing targetVal with
  | lit v =>
      intro r hr
      simp [exprUpdate] at hr
      subst hr
      rfl
  | var i =>
      intro r hr
      simp [exprUpdate] at hr
      subst hr
      have h0 : countOccurrences i e2 = 0 := by
        apply h_no_occ i
        simp [countOccurrences]
      simpa using (eval_env_update_independent (env:=env) (e:=e2) (i:=i) (val:=targetVal) h0)
  | add e1a e1b ih1 ih2 =>
      intro r hr
      unfold exprUpdate at hr
      cases List.mem_append.mp hr with
      | inl h_left =>
          rcases List.mem_map.mp h_left with ⟨r_inner, h_mem, h_eq⟩
          subst h_eq
          have h_no_occ1 : ∀ i : Fin _, countOccurrences i e1a > 0 → countOccurrences i e2 = 0 := by
            intro i hi
            have h := h_no_occ i
            simp only [countOccurrences] at h
            omega
          exact ih1 env e2 (targetVal - evalExpr env e1b) h_no_occ1 r_inner h_mem
      | inr h_right =>
          rcases List.mem_map.mp h_right with ⟨r_inner, h_mem, h_eq⟩
          subst h_eq
          have h_no_occ2 : ∀ i : Fin _, countOccurrences i e1b > 0 → countOccurrences i e2 = 0 := by
            intro i hi
            have h := h_no_occ i
            simp only [countOccurrences] at h
            omega
          exact ih2 env e2 (targetVal - evalExpr env e1a) h_no_occ2 r_inner h_mem
  | mul e1a e1b ih1 ih2 =>
      intro r hr
      unfold exprUpdate at hr
      cases List.mem_append.mp hr with
      | inl h_left =>
          cases hsd : safeDiv targetVal (evalExpr env e1b) with
          | none =>
              by_cases h_target : targetVal = 0
              · have h_left' := h_left
                simp [hsd] at h_left'
                simp [h_target] at h_left'
                have h_eq : r = { expr := e1a.mul e1b, env := env } := by
                  simpa using h_left'
                subst h_eq
                rfl
              · simp [hsd, h_target] at h_left
          | some t1 =>
              simp [hsd] at h_left
              rcases h_left with ⟨r_inner, h_mem, h_eq⟩
              subst h_eq
              have h_no_occ1 : ∀ i : Fin _, countOccurrences i e1a > 0 → countOccurrences i e2 = 0 := by
                intro i hi
                have h := h_no_occ i
                simp only [countOccurrences] at h
                omega
              exact ih1 env e2 _ h_no_occ1 r_inner h_mem
      | inr h_right =>
          cases hsd : safeDiv targetVal (evalExpr env e1a) with
          | none =>
              by_cases h_target : targetVal = 0
              · have h_right' := h_right
                simp [hsd] at h_right'
                simp [h_target] at h_right'
                have h_eq : r = { expr := e1a.mul e1b, env := env } := by
                  simpa using h_right'
                subst h_eq
                rfl
              · simp [hsd, h_target] at h_right
          | some t2 =>
              simp [hsd] at h_right
              rcases h_right with ⟨r_inner, h_mem, h_eq⟩
              subst h_eq
              have h_no_occ2 : ∀ i : Fin _, countOccurrences i e1b > 0 → countOccurrences i e2 = 0 := by
                intro i hi
                have h := h_no_occ i
                simp only [countOccurrences] at h
                omega
              exact ih2 env e2 _ h_no_occ2 r_inner h_mem
  | recip e ih =>
      intro r hr
      unfold exprUpdate at hr
      cases hsd : safeDiv 1 targetVal with
      | none => simp [hsd] at hr
      | some t =>
          simp [hsd] at hr
          rcases hr with ⟨r_inner, h_mem, h_eq⟩
          subst h_eq
          have h_no_occ1 : ∀ i : Fin _, countOccurrences i e > 0 → countOccurrences i e2 = 0 := by
            intro i hi
            apply h_no_occ i
            simpa [countOccurrences] using hi
          exact ih env e2 _ h_no_occ1 r_inner h_mem
  | let_ e1 o ih1 ih2 =>
      intro r hr
      simp only [exprUpdate] at hr
      rcases List.mem_flatMap.mp hr with ⟨r_inner, h_mem, h_eq⟩
      rcases List.mem_filterMap.mp h_eq with ⟨r_body, h_mem_body, h_eq_body⟩
      have h_no_occ1 : ∀ i : Fin _, countOccurrences i e1 > 0 → countOccurrences i e2 = 0 := by
        intro i hi
        have h := h_no_occ i
        simp [countOccurrences] at h
        omega
      by_cases h_guard : evalExpr r_body.env (Expr.let_ r_body.expr r_inner.expr) = targetVal
      · have h_eq : { expr := Expr.let_ r_body.expr r_inner.expr, env := r_body.env } = r := by
          simpa [h_guard] using h_eq_body
        cases h_eq
        exact ih1 env e2 _ h_no_occ1 r_body h_mem_body
      · have h_eq_body' := h_eq_body
        simp [h_guard] at h_eq_body'


-- PutGet: updating to targetVal yields results that evaluate back to targetVal.
theorem exprUpdate_putGet {n : Nat} (env : Env n) (e : Expr n) (targetVal : Rat):
  isIndependent e -> ∀ r ∈ exprUpdate env e targetVal , evalExpr r.env r.expr = targetVal := by
  induction e generalizing  targetVal with
  | lit v =>
      intro h_ind r hr
      simp [exprUpdate] at hr
      subst hr
      simp [evalExpr]
  | var i =>
      intro h_ind r hr
      simp [exprUpdate] at hr
      subst hr
      simp [evalExpr, Env.update_eq]
  | add e1 e2 ih1 ih2 =>
      intro h_ind r hr
      rcases h_ind with ⟨h_ind1, h_ind2, h_disj⟩
      unfold exprUpdate at hr
      cases List.mem_append.mp hr with
      | inl h_left =>
          rcases List.mem_map.mp h_left with ⟨ r_inner, h_mem, h_eq ⟩
          subst h_eq
          simp only [evalExpr]
          have ih := ih1 env (targetVal - evalExpr env e2) h_ind1 r_inner h_mem
          rw [ih]
          have h_no_occ : ∀ i, countOccurrences i e1 > 0 → countOccurrences i e2 = 0 := by
            intro i _
            have := h_disj i
            omega
          have h_eval_e2 : evalExpr r_inner.env e2 = evalExpr env e2 := by
            exact exprUpdate_preserves_eval_disjoint env e1 e2 (targetVal - evalExpr env e2) h_no_occ r_inner h_mem
          calc
            targetVal - evalExpr env e2 + evalExpr r_inner.env e2
                = targetVal - evalExpr env e2 + evalExpr env e2 := by simp [h_eval_e2]
            _ = targetVal := by ring

      | inr h_right =>
          rcases List.mem_map.mp h_right with ⟨ r_inner, h_mem, h_eq ⟩
          subst h_eq
          simp only [evalExpr]
          have ih := ih2 env (targetVal - evalExpr env e1) h_ind2 r_inner h_mem
          rw [ih]
          have h_no_occ : ∀ i, countOccurrences i e2 > 0 → countOccurrences i e1 = 0 :=by
            intro i _
            have := h_disj i
            omega
          have h_eval_e1 : evalExpr r_inner.env e1 = evalExpr env e1 := by
            exact exprUpdate_preserves_eval_disjoint env e2 e1 (targetVal - evalExpr env e1) h_no_occ r_inner h_mem
          calc
            evalExpr r_inner.env e1 + (targetVal - evalExpr env e1)
                = evalExpr env e1 + (targetVal - evalExpr env e1) := by simp [h_eval_e1]
            _ = targetVal := by ring

  | mul e1 e2 ih1 ih2 =>
      intro h_ind r hr
      rcases h_ind with ⟨h_ind1, h_ind2, h_disj⟩
      unfold exprUpdate at hr
      cases List.mem_append.mp hr with
      | inl h_left =>
         by_cases hz : (evalExpr env e2)  = 0
         · by_cases ht : targetVal = 0 -- safeDiv will be none
           · simp [hz, ht, safeDiv] at h_left
             cases h_left
             simp [evalExpr, hz, ht]
           · simp [hz, ht, safeDiv] at h_left
         · have h_div : safeDiv targetVal (evalExpr env e2) = some (targetVal / evalExpr env e2) := safeDiv_some hz
           rw [h_div] at h_left
           dsimp only at h_left
           rcases List.mem_map.mp h_left with ⟨r_inner, h_mem, h_eq⟩
           subst h_eq
           simp only [evalExpr]
           have ih := ih1 env (targetVal / evalExpr env e2) h_ind1 r_inner h_mem
           rw [ih]
           have h_no_occ : ∀ i, countOccurrences i e1 > 0 → countOccurrences i e2 = 0 := by
             intro i hi
             have := h_disj i
             omega
           have h_agree : evalExpr r_inner.env e2 = evalExpr env e2 :=
            exprUpdate_preserves_eval_disjoint env e1 e2 (targetVal / evalExpr env e2) h_no_occ r_inner h_mem
           rw [h_agree]
           exact div_mul_cancel₀ targetVal hz
      | inr h_right =>
        by_cases hz : (evalExpr env e1)  = 0
        · by_cases ht : targetVal = 0 -- safeDiv will be none
          · simp [hz, ht, safeDiv] at h_right
            cases h_right
            simp [evalExpr, hz, ht]
          · simp [hz, ht, safeDiv] at h_right
        · have h_div : safeDiv targetVal (evalExpr env e1) = some (targetVal / evalExpr env e1) := safeDiv_some hz
          rw [h_div] at h_right
          dsimp only at h_right
          rcases List.mem_map.mp h_right with ⟨r_inner, h_mem, h_eq⟩
          subst h_eq
          simp only [evalExpr]
          have ih := ih2 env (targetVal / evalExpr env e1) h_ind2 r_inner h_mem
          rw [ih]
          have h_no_occ : ∀ i, countOccurrences i e2 > 0 → countOccurrences i e1 = 0 := by
             intro i hi
             have := h_disj i
             omega
          have h_agree : evalExpr r_inner.env e1 = evalExpr env e1 :=
            exprUpdate_preserves_eval_disjoint env e2 e1 (targetVal / evalExpr env e1) h_no_occ r_inner h_mem
          rw [h_agree, mul_comm]
          exact div_mul_cancel₀ targetVal hz
  | recip e1  ih =>
    intro h_ind r hr
    simp [exprUpdate] at hr
    by_cases hz : (evalExpr env e1)  = 0
    · simp [safeDiv] at hr
      by_cases ht : targetVal = 0
      · simp [ht] at hr
      · simp [ht] at hr
        rcases hr with ⟨a, h_mem, h_eq⟩
        subst h_eq
        simp only [evalExpr]
        have h_ih := ih env targetVal⁻¹ h_ind a h_mem
        rw [h_ih, Rat.inv_inv]
    · simp [safeDiv] at hr
      by_cases ht : targetVal = 0
      · simp [ht] at hr
      · simp [ht] at hr
        rcases hr with ⟨ a, h_mem, h_eq ⟩
        subst h_eq
        simp only [evalExpr]
        have h_ih := ih env targetVal⁻¹ h_ind a h_mem
        rw [h_ih, Rat.inv_inv]
  | let_ e1 o ihe1 iho =>
  intro h_int r hr
  simp [exprUpdate] at hr
  rcases hr with ⟨ ur, h_ur, a, h_a, tv_eq, r_eq ⟩
  subst r_eq
  simp only [evalExpr]
  simp [evalExpr] at tv_eq
  exact tv_eq
