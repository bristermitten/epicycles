import Epicycles.Delta
import Epicycles.FuseDM.AST
import Epicycles.FuseDM.Eval
import Epicycles.FuseDM.Delta
import Epicycles.FuseDM.Update
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Bidirectional / lens-style laws for the delta-based backwards semantics

This code was generated with the assistance of AI

This file states and proves three lens laws for the bipartite let-normal AST:

* **GetPut** — applying the identity delta is a no-op.
* **PutGet** — applying a delta and then re-evaluating yields exactly the
  delta applied to the original value.
* **PutPut** — applying `d1` and then `d2` is the same as applying the
  concatenated delta `d2 ++ d1` once.

For the numeric layer we adopt the natural notion of "current value":
a let-free `(e, deltas)` pair denotes the rational
`evalNumExpr (deltas.apply vals) e` under the original `vals`.
-/


-- ============================================================================
-- BEq reflexivity for AtomicNumDelta / NumDelta
-- (the auto-derived `BEq` for `AtomicNumDelta` is not `rfl`-reducible at
-- `replace` because `Rat`'s `BEq` is not definitionally reflexive.)
-- ============================================================================

@[simp] theorem AtomicNumDelta.beq_self : ∀ (a : AtomicNumDelta), (a == a) = true
  | .add v | .mul v | .replace v => by show (v == v) = true; simp

theorem AtomicNumDelta.eq_of_beq :
    ∀ {a b : AtomicNumDelta}, (a == b) = true → a = b
  | .add v1, .add v2, h
  | .mul v1, .mul v2, h
  | .replace v1, .replace v2, h => by
      have hb : (v1 == v2) = true := h
      have : v1 = v2 := by simpa using hb
      rw [this]
  | .add _, .mul _, h | .add _, .replace _, h
  | .mul _, .add _, h | .mul _, .replace _, h
  | .replace _, .add _, h | .replace _, .mul _, h => by cases h

instance : LawfulBEq AtomicNumDelta where
  rfl := fun {a} => AtomicNumDelta.beq_self a
  eq_of_beq := AtomicNumDelta.eq_of_beq

@[simp] theorem NumDelta.beq_self (d : NumDelta) : (d == d) = true := by
  induction d with
  | nil => rfl
  | cons a rest ih =>
      show (a == a && (rest == rest)) = true
      rw [AtomicNumDelta.beq_self a, ih]
      rfl


-- ============================================================================
-- Helper lemmas about `embed` and `DeltaEnv.id`
-- ============================================================================

@[simp] theorem embedNumDeltaInto_nil {n : Nat} (e : NumExpr n) :
    embedNumDeltaInto [] e = e := rfl

/-- Embedding the identity `DeltaEnv` into a `NumExpr` is a no-op. -/
@[simp] theorem NumExpr.embed_id {n : Nat} (e : NumExpr n) :
    e.embed (DeltaEnv.id n) = e := by
  induction e with
  | lit v => rfl
  | var i => simp [NumExpr.embed, DeltaEnv.id]
  | add e1 e2 ih1 ih2 => simp [NumExpr.embed, ih1, ih2]
  | mul e1 e2 ih1 ih2 => simp [NumExpr.embed, ih1, ih2]
  | recip e ih => simp [NumExpr.embed, ih]

/-- Embedding the identity `DeltaEnv` into a `Curve` is a no-op. -/
@[simp] theorem Curve.embed_id {n : Nat} (c : Curve n) :
    c.embed (DeltaEnv.id n) = c := by
  induction c with
  | epicycle eid r w p => simp [Curve.embed]
  | append c1 c2 ih1 ih2 => simp [Curve.embed, ih1, ih2]

/-- Extending the identity DeltaEnv with `[]` gives the identity DeltaEnv. -/
theorem DeltaEnv.id_extend (n : Nat) :
    (DeltaEnv.id n).extend [] = DeltaEnv.id (n + 1) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- Embedding the identity `DeltaEnv` into a `Program` is a no-op. -/
@[simp] theorem Program.embed_id {n : Nat} (P : Program n) :
    P.embed (DeltaEnv.id n) = P := by
  induction P with
  | done c => simp [Program.embed]
  | letBind e1 body ih =>
      simp [Program.embed, DeltaEnv.id_extend, ih]


-- ============================================================================
-- `compareOperator` on equal environments returns the identity residuals.
-- ============================================================================

theorem compareOperator_self {n : Nat} (env : DeltaEnv n)
    (free1 free2 : Fin n → Bool) :
    compareOperator env env free1 free2 = (env, DeltaEnv.id n, DeltaEnv.id n) := by
  unfold compareOperator
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext i; simp
  · funext i; simp [DeltaEnv.id]
  · funext i; simp [DeltaEnv.id]


-- ============================================================================
-- opt merges of an env with itself: identity.
-- ============================================================================

theorem optMergeNum_self {n : Nat} (env : DeltaEnv n)
    (e1 e2 : NumExpr n) :
    optMergeNum env env e1 e2 = (env, e1, e2) := by
  simp [optMergeNum, compareOperator_self]

theorem optMergeCurve_self {n : Nat} (env : DeltaEnv n)
    (c1 c2 : Curve n) :
    optMergeCurve env env c1 c2 = (env, c1, c2) := by
  simp [optMergeCurve, compareOperator_self]

theorem optMergeLetProgram_self {n : Nat} (env : DeltaEnv n)
    (e1 : NumExpr n) (body : Program (n + 1)) :
    optMergeLetProgram env env e1 body = (env, e1, body) := by
  simp [optMergeLetProgram, compareOperator_self, DeltaEnv.id_extend]


-- ============================================================================
-- GetPut at the Program layer
-- ============================================================================

/-- **GetPut for `backwardEvalProgram`**: applying the identity
`CurveDelta` leaves both the program and the delta environment
unchanged. -/
@[simp] theorem backwardEvalProgram_id {n : Nat} (vals : Env n)
    (deltas : DeltaEnv n) (P : Program n) :
    backwardEvalProgram .id vals deltas P = (deltas, P) := by
  induction P with
  | done c =>
      simp [backwardEvalProgram]
  | letBind e1 body ih =>
      simp only [backwardEvalProgram, ih]
      have hd : (fun i : Fin _ => (deltas.extend []) i.succ) = deltas := by
        funext i; simp [DeltaEnv.extend]
      have h0 : (deltas.extend []) 0 = [] := by simp [DeltaEnv.extend]
      rw [hd, h0]
      simp [optMergeLetProgram_self]


-- ============================================================================
-- GetPut: a `modAppend` of two identity deltas is also the identity.
-- ============================================================================

/-- A `.modAppend .id .id` delta acts as the identity on a `Curve`. -/
@[simp] theorem backwardEvalCurve_modAppend_id_id {n : Nat} (vals : Env n)
    (deltas : DeltaEnv n) (c : Curve n) :
    backwardEvalCurve (.modAppend .id .id) vals deltas c = (deltas, c) := by
  cases c with
  | epicycle eid r w p => rfl
  | append c1 c2 => simp [backwardEvalCurve, optMergeCurve_self]


-- ============================================================================
-- GetPut for the foldr lifters: applying an empty list of deltas is identity.
-- ============================================================================

/-- Folding the empty `CurveDelta` list is the identity on a `Curve`. -/
theorem backwardEvalCurveList_id_nil {n : Nat} (vals : Env n)
    (deltas : DeltaEnv n) (c : Curve n) :
    backwardEvalCurveList [] vals deltas c = (deltas, c) := rfl

/-- Folding the empty `CurveDelta` list is the identity on a `Program`. -/
theorem backwardEvalProgramList_id_nil {n : Nat} (vals : Env n)
    (deltas : DeltaEnv n) (P : Program n) :
    backwardEvalProgramList [] vals deltas P = (deltas, P) := rfl


-- ============================================================================
-- Embed-soundness: evaluating an embedded expression is the same as
-- evaluating the original under a delta-applied environment.
-- ============================================================================

/-- Evaluating `embedNumDeltaInto d e` is the same as applying the
delta `d` to the value of `e`. -/
theorem embedNumDeltaInto_eval {n : Nat} (vals : Env n) :
    ∀ (d : NumDelta) (e : NumExpr n),
      evalNumExpr vals (embedNumDeltaInto d e) = d.apply (evalNumExpr vals e)
  | [], _ => rfl
  | .add v :: rest, e => by
      have ih := embedNumDeltaInto_eval vals rest e
      show v + evalNumExpr vals (embedNumDeltaInto rest e) =
          NumDelta.apply rest (evalNumExpr vals e) + v
      rw [ih]
      ring
  | .mul v :: rest, e => by
      have ih := embedNumDeltaInto_eval vals rest e
      show v * evalNumExpr vals (embedNumDeltaInto rest e) =
          NumDelta.apply rest (evalNumExpr vals e) * v
      rw [ih]
      ring
  | .replace _ :: _, _ => rfl

/-- Evaluating `e.embed deltas` is the same as evaluating `e` under
`deltas.apply vals`. -/
theorem NumExpr.embed_eval {n : Nat} (vals : Env n) (deltas : DeltaEnv n) :
    ∀ (e : NumExpr n),
      evalNumExpr vals (e.embed deltas) = evalNumExpr (deltas.apply vals) e
  | .lit _ => rfl
  | .var i => by
      show evalNumExpr vals (embedNumDeltaInto (deltas i) (.var i)) =
          (deltas.apply vals) i
      rw [embedNumDeltaInto_eval]
      rfl
  | .add e1 e2 => by
      simp [NumExpr.embed, evalNumExpr, NumExpr.embed_eval vals deltas e1,
            NumExpr.embed_eval vals deltas e2]
  | .mul e1 e2 => by
      simp [NumExpr.embed, evalNumExpr, NumExpr.embed_eval vals deltas e1,
            NumExpr.embed_eval vals deltas e2]
  | .recip e => by
      simp [NumExpr.embed, evalNumExpr, NumExpr.embed_eval vals deltas e]


-- ============================================================================
-- PutPut at the foldr lifters (numeric / curve / program).
--
-- All three are `List.foldr` over a per-element step, so the PutPut law
-- is exactly `List.foldr_append`: composing `d1` then `d2` is the same
-- as collapsing them to a single `d2 ++ d1`.
-- ============================================================================

/-- **PutPut for `backwardEvalNum`**: applying `d1` then `d2` equals
applying the concatenation `d2 ++ d1`. -/
theorem backwardEvalNum_append {n : Nat} (d1 d2 : NumDelta) (vals : Env n)
    (deltas : DeltaEnv n) (e : NumExpr n) :
    backwardEvalNum (d2 ++ d1) vals deltas e =
      (let (deltas', e') := backwardEvalNum d1 vals deltas e
       backwardEvalNum d2 vals deltas' e') := by
  simp only [backwardEvalNum, List.foldr_append]

/-- **PutPut for `backwardEvalCurveList`**: applying `dvs1` then `dvs2`
equals applying the concatenation `dvs2 ++ dvs1`. -/
theorem backwardEvalCurveList_append {n : Nat} (dvs1 dvs2 : List CurveDelta)
    (vals : Env n) (deltas : DeltaEnv n) (c : Curve n) :
    backwardEvalCurveList (dvs2 ++ dvs1) vals deltas c =
      (let (deltas', c') := backwardEvalCurveList dvs1 vals deltas c
       backwardEvalCurveList dvs2 vals deltas' c') := by
  simp only [backwardEvalCurveList, List.foldr_append]

/-- **PutPut for `backwardEvalProgramList`**: applying `dvs1` then `dvs2`
equals applying the concatenation `dvs2 ++ dvs1`. -/
theorem backwardEvalProgramList_append {n : Nat} (dvs1 dvs2 : List CurveDelta)
    (vals : Env n) (deltas : DeltaEnv n) (P : Program n) :
    backwardEvalProgramList (dvs2 ++ dvs1) vals deltas P =
      (let (deltas', P') := backwardEvalProgramList dvs1 vals deltas P
       backwardEvalProgramList dvs2 vals deltas' P') := by
  simp only [backwardEvalProgramList, List.foldr_append]


-- ============================================================================
-- Supporting lemmas for the merge cases of PutGet.
-- ============================================================================

/-- `NumDelta.apply` distributes over list concatenation: foldr-append. -/
theorem NumDelta.apply_append (d1 d2 : NumDelta) (x : Rat) :
    (d1 ++ d2).apply x = d1.apply (d2.apply x) := by
  show (d1 ++ d2).foldr AtomicNumDelta.apply x =
       d1.foldr AtomicNumDelta.apply (d2.foldr AtomicNumDelta.apply x)
  rw [List.foldr_append]

/-- Evaluation of a `NumExpr` only depends on the values of its free vars. -/
theorem NumExpr.eval_eq_of_agree_on_free {n : Nat} :
    ∀ (e : NumExpr n) (σ1 σ2 : Env n),
      (∀ i : Fin n, e.isFreeIn i = true → σ1 i = σ2 i) →
      evalNumExpr σ1 e = evalNumExpr σ2 e
  | .lit _, _, _, _ => rfl
  | .var _, _, _, h => h _ (by simp [NumExpr.isFreeIn])
  | .add e1 e2, σ1, σ2, h
  | .mul e1 e2, σ1, σ2, h => by
      simp [evalNumExpr,
            NumExpr.eval_eq_of_agree_on_free e1 σ1 σ2
              (fun i hi => h i (by simp [NumExpr.isFreeIn, hi])),
            NumExpr.eval_eq_of_agree_on_free e2 σ1 σ2
              (fun i hi => h i (by simp [NumExpr.isFreeIn, hi]))]
  | .recip e, σ1, σ2, h => by
      simp [evalNumExpr,
            NumExpr.eval_eq_of_agree_on_free e σ1 σ2
              (fun i hi => h i (by simp [NumExpr.isFreeIn, hi]))]

/-- `splitCommonPrefix` returns a true common prefix of its inputs, with
the right-hand list also reconstructible from the prefix and remainder. -/
theorem splitCommonPrefix_correct {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l1 l2 : List α),
      l1 = (splitCommonPrefix l1 l2).1 ++ (splitCommonPrefix l1 l2).2.1 ∧
      l2 = (splitCommonPrefix l1 l2).1 ++ (splitCommonPrefix l1 l2).2.2
  | [], [] | [], _ :: _ | _ :: _, [] => ⟨rfl, rfl⟩
  | a :: as, b :: bs => by
      have ih := splitCommonPrefix_correct as bs
      by_cases hab : (a == b) = true
      · have hab_eq : a = b := eq_of_beq hab
        have hsplit : splitCommonPrefix (a :: as) (b :: bs) =
            (a :: (splitCommonPrefix as bs).1,
             (splitCommonPrefix as bs).2.1, (splitCommonPrefix as bs).2.2) := by
          show (if (a == b) = true then _ else _) = _; rw [if_pos hab]
        rw [hsplit]
        exact ⟨by show a :: as = a :: _ ++ _; rw [List.cons_append, ← ih.1],
               by show b :: bs = a :: _ ++ _; rw [hab_eq, List.cons_append, ← ih.2]⟩
      · have hsplit : splitCommonPrefix (a :: as) (b :: bs) = ([], a :: as, b :: bs) := by
          show (if (a == b) = true then _ else _) = _; rw [if_neg hab]
        rw [hsplit]; exact ⟨rfl, rfl⟩

/-- `splitSuffix` correctness: `d1 = p1 ++ s` and `d2 = p2 ++ s`. -/
theorem NumDelta.splitSuffix_correct (d1 d2 : NumDelta) :
    d1 = (d1.splitSuffix d2).2.1 ++ (d1.splitSuffix d2).1 ∧
    d2 = (d1.splitSuffix d2).2.2 ++ (d1.splitSuffix d2).1 := by
  simp only [NumDelta.splitSuffix]
  obtain ⟨h1, h2⟩ := splitCommonPrefix_correct d1.reverse d2.reverse
  exact ⟨by simpa [List.reverse_append] using congrArg List.reverse h1,
         by simpa [List.reverse_append] using congrArg List.reverse h2⟩


-- ============================================================================
-- compareOperator correctness: at any variable index, the residual
-- environment's value, prepended to the merged environment's value,
-- recovers the original input environment's value (provided the var is
-- "free" in the relevant operand, i.e. its eval depends on it).
--
-- We state these as direct functions of the underlying lambdas so the
-- merge-correctness proof can use them without further reasoning about
-- `compareOperator`'s internal structure.
-- ============================================================================

/-- The "merged-env" lambda inside `compareOperator`. -/
private def cmpEM {n : Nat} (env1 env2 : DeltaEnv n)
    (free1 free2 : Fin n → Bool) : DeltaEnv n :=
  fun i =>
    if env1 i == env2 i || not (free2 i) then env1 i
    else if not (free1 i) then env2 i
    else (env1 i).splitSuffix (env2 i) |>.fst

/-- The left residual lambda inside `compareOperator`. -/
private def cmpE1I {n : Nat} (env1 env2 : DeltaEnv n)
    (free1 free2 : Fin n → Bool) : DeltaEnv n :=
  fun i =>
    if env1 i == env2 i || not (free2 i) then []
    else if not (free1 i) then []
    else (env1 i).splitSuffix (env2 i) |>.snd.fst

/-- The right residual lambda inside `compareOperator`. -/
private def cmpE2I {n : Nat} (env1 env2 : DeltaEnv n)
    (free1 free2 : Fin n → Bool) : DeltaEnv n :=
  fun i =>
    if env1 i == env2 i || not (free2 i) then []
    else if not (free1 i) then []
    else (env1 i).splitSuffix (env2 i) |>.snd.snd

theorem compareOperator_eq {n : Nat} (env1 env2 : DeltaEnv n)
    (free1 free2 : Fin n → Bool) :
    compareOperator env1 env2 free1 free2 =
      (cmpEM env1 env2 free1 free2,
       cmpE1I env1 env2 free1 free2,
       cmpE2I env1 env2 free1 free2) := rfl

theorem compareOperator_recover_left {n : Nat} (env1 env2 : DeltaEnv n)
    (free1 free2 : Fin n → Bool) (i : Fin n) (hfree : free1 i = true) :
    cmpE1I env1 env2 free1 free2 i ++ cmpEM env1 env2 free1 free2 i = env1 i := by
  unfold cmpE1I cmpEM
  by_cases h12 : (env1 i == env2 i) = true
  · have h12_eq : env1 i = env2 i := eq_of_beq h12
    simp [h12]
  · simp only [h12, Bool.false_or]
    by_cases hf2 : free2 i = true
    · simp only [hf2, Bool.not_true]
      simp only [hfree, Bool.not_true]
      exact (NumDelta.splitSuffix_correct (env1 i) (env2 i)).1.symm
    · simp only [Bool.not_eq_true] at hf2
      simp [hf2]

theorem compareOperator_recover_right {n : Nat} (env1 env2 : DeltaEnv n)
    (free1 free2 : Fin n → Bool) (i : Fin n) (hfree : free2 i = true) :
    cmpE2I env1 env2 free1 free2 i ++ cmpEM env1 env2 free1 free2 i = env2 i := by
  unfold cmpE2I cmpEM
  by_cases h12 : (env1 i == env2 i) = true
  · have h12_eq : env1 i = env2 i := eq_of_beq h12
    simp [h12_eq]
  · simp only [h12, Bool.false_or]
    simp only [hfree, Bool.not_true]
    by_cases hf1 : free1 i = true
    · simp only [hf1, Bool.not_true]
      exact (NumDelta.splitSuffix_correct (env1 i) (env2 i)).2.symm
    · simp only [Bool.not_eq_true] at hf1
      simp [hf1]


-- ============================================================================
-- Merge correctness: evaluating either embedded operand under the merged
-- env recovers the evaluation under the corresponding input env.
--
-- We factor the common pattern out as a generic `recovery` lemma:
-- if `residual i ++ envFinal i = envOrig i` on every free variable of `e`,
-- then `e.embed residual` evaluated under `envFinal.apply vals` agrees with
-- `e` evaluated under `envOrig.apply vals`.
-- ============================================================================

/-- Generic merge-recovery for an embedded `NumExpr`. -/
private theorem evalNumExpr_recover {n : Nat} (vals : Env n)
    (envFinal envOrig residual : DeltaEnv n) (e : NumExpr n)
    (hRec : ∀ i : Fin n, e.isFreeIn i = true → residual i ++ envFinal i = envOrig i) :
    evalNumExpr (envFinal.apply vals) (e.embed residual) =
      evalNumExpr (envOrig.apply vals) e := by
  rw [NumExpr.embed_eval]
  apply NumExpr.eval_eq_of_agree_on_free
  intro i hfree
  show (residual i).apply ((envFinal i).apply (vals i)) = (envOrig i).apply (vals i)
  rw [← NumDelta.apply_append, hRec i hfree]

/-- Two-step chained recovery for `NumExpr`: an outer `embed` of an inner `embed`. -/
private theorem evalNumExpr_recover_chain {n : Nat} (vals : Env n)
    (eFinal eMid eOrig rOuter rInner : DeltaEnv n) (e : NumExpr n)
    (hOuter : ∀ i, (e.embed rInner).isFreeIn i = true → rOuter i ++ eFinal i = eMid i)
    (hInner : ∀ i, e.isFreeIn i = true → rInner i ++ eMid i = eOrig i) :
    evalNumExpr (eFinal.apply vals) ((e.embed rInner).embed rOuter) =
      evalNumExpr (eOrig.apply vals) e := by
  rw [evalNumExpr_recover vals eFinal eMid rOuter (e.embed rInner) hOuter]
  exact evalNumExpr_recover vals eMid eOrig rInner e hInner

theorem optMergeNum_eval_left {n : Nat} (vals : Env n)
    (env1 env2 : DeltaEnv n) (e1 e2 : NumExpr n) :
    evalNumExpr ((optMergeNum env1 env2 e1 e2).1.apply vals)
                (optMergeNum env1 env2 e1 e2).2.1 =
      evalNumExpr (env1.apply vals) e1 :=
  evalNumExpr_recover vals _ env1 _ e1
    (fun i => compareOperator_recover_left env1 env2 (e1.isFreeIn ·) (e2.isFreeIn ·) i)

theorem optMergeNum_eval_right {n : Nat} (vals : Env n)
    (env1 env2 : DeltaEnv n) (e1 e2 : NumExpr n) :
    evalNumExpr ((optMergeNum env1 env2 e1 e2).1.apply vals)
                (optMergeNum env1 env2 e1 e2).2.2 =
      evalNumExpr (env2.apply vals) e2 :=
  evalNumExpr_recover vals _ env2 _ e2
    (fun i => compareOperator_recover_right env1 env2 (e1.isFreeIn ·) (e2.isFreeIn ·) i)


-- ============================================================================
-- PutGet for `backwardEvalAtomic` — full statement (all cases).
--
-- The proof is by structural induction on `e`, with case analysis on the
-- delta `d` inside each constructor.  Recursive calls always pass the same
-- outer `vals`, so the IH is reusable across delta cases.
-- ============================================================================

/-- `[d].apply x = d.apply x`. -/
private theorem NumDelta.apply_singleton (d : AtomicNumDelta) (x : Rat) :
    NumDelta.apply [d] x = d.apply x := rfl

/-- `evalNumExpr` of a singleton-embedded delta unfolds to the delta's
action on the original eval. -/
private theorem embedNumDeltaInto_singleton_eval {n : Nat} (vals : Env n)
    (d : AtomicNumDelta) (e : NumExpr n) :
    evalNumExpr vals (embedNumDeltaInto [d] e) = d.apply (evalNumExpr vals e) := by
  rw [embedNumDeltaInto_eval, NumDelta.apply_singleton]

/-- **PutGet for `backwardEvalAtomic`**: applying an atomic delta backwards
and re-evaluating yields exactly the delta applied to the original
evaluation. -/
theorem backwardEvalAtomic_putGet {n : Nat} (vals : Env n) :
    ∀ (e : NumExpr n) (d : AtomicNumDelta) (deltas : DeltaEnv n),
      evalNumExpr ((backwardEvalAtomic d vals deltas e).1.apply vals)
                  (backwardEvalAtomic d vals deltas e).2 =
        d.apply (evalNumExpr (deltas.apply vals) e) := by
  intro e
  induction e with
  | lit v =>
      intro d deltas
      cases d with
      | add a => rfl
      | mul m => rfl
      | replace v' => rfl
  | var i =>
      intro d deltas
      cases d with
      | add a =>
          show ((deltas.update i (.add a :: deltas i)).apply vals) i =
               (deltas.apply vals) i + a
          show (deltas.update i (.add a :: deltas i) i).apply (vals i) =
               (deltas i).apply (vals i) + a
          rw [DeltaEnv.update]
          simp [NumDelta.apply, AtomicNumDelta.apply]
      | mul m =>
          show ((deltas.update i (.mul m :: deltas i)).apply vals) i =
               (deltas.apply vals) i * m
          show (deltas.update i (.mul m :: deltas i) i).apply (vals i) =
               (deltas i).apply (vals i) * m
          rw [DeltaEnv.update]
          simp [NumDelta.apply, AtomicNumDelta.apply]
      | replace v' => rfl
  | add e1 e2 ih1 ih2 =>
      intro d deltas
      cases d with
      | replace v' => rfl
      | add a =>
          dsimp only [backwardEvalAtomic]
          show evalNumExpr _ _ + evalNumExpr _ _ = _
          rw [optMergeNum_eval_left, optMergeNum_eval_right, ih1 (.add a) deltas]
          show evalNumExpr (deltas.apply vals) e1 + a + evalNumExpr (deltas.apply vals) e2 =
               evalNumExpr (deltas.apply vals) e1 + evalNumExpr (deltas.apply vals) e2 + a
          ring
      | mul m =>
          dsimp only [backwardEvalAtomic]
          show evalNumExpr _ _ + evalNumExpr _ _ = _
          rw [optMergeNum_eval_left, optMergeNum_eval_right,
              ih1 (.mul m) deltas, ih2 (.mul m) deltas]
          show evalNumExpr (deltas.apply vals) e1 * m + evalNumExpr (deltas.apply vals) e2 * m =
               (evalNumExpr (deltas.apply vals) e1 + evalNumExpr (deltas.apply vals) e2) * m
          ring
  | mul e1 e2 ih1 ih2 =>
      intro d deltas
      cases d with
      | replace v' => rfl
      | add x =>
          dsimp only [backwardEvalAtomic]
          set sigma' := deltas.apply vals with hsigma'
          set n2 := evalNumExpr sigma' e2 with hn2
          by_cases hzero : n2 = 0
          · rw [if_pos hzero, embedNumDeltaInto_singleton_eval]
          · rw [if_neg hzero]
            show evalNumExpr _ _ * evalNumExpr _ _ = _
            rw [optMergeNum_eval_left, optMergeNum_eval_right,
                ih1 (.add (x / n2)) deltas]
            show (evalNumExpr (deltas.apply vals) e1 + x / n2) *
                  evalNumExpr (deltas.apply vals) e2 =
                  evalNumExpr (deltas.apply vals) e1 *
                    evalNumExpr (deltas.apply vals) e2 + x
            rw [show evalNumExpr (deltas.apply vals) e2 = n2 from rfl]
            field_simp
      | mul m =>
          dsimp only [backwardEvalAtomic]
          show evalNumExpr _ _ * evalNumExpr _ _ = _
          rw [optMergeNum_eval_left, optMergeNum_eval_right, ih1 (.mul m) deltas]
          show (evalNumExpr (deltas.apply vals) e1 * m) *
                evalNumExpr (deltas.apply vals) e2 =
                evalNumExpr (deltas.apply vals) e1 *
                  evalNumExpr (deltas.apply vals) e2 * m
          ring
  | recip x ihx =>
      intro d deltas
      cases d with
      | replace v' => rfl
      | add v =>
          dsimp only [backwardEvalAtomic]
          set sigma' := deltas.apply vals with hsigma'
          set vx := evalNumExpr sigma' x with hvx
          by_cases hvx0 : vx = 0
          · rw [if_pos hvx0, embedNumDeltaInto_singleton_eval]
          · rw [if_neg hvx0]
            by_cases hsum : vx⁻¹ + v = 0
            · rw [if_pos hsum, embedNumDeltaInto_singleton_eval]
            · rw [if_neg hsum]
              have ih := ihx (.add ((vx⁻¹ + v)⁻¹ - vx)) deltas
              show (evalNumExpr _ _)⁻¹ = _
              rw [ih]
              show ((evalNumExpr (deltas.apply vals) x) + ((vx⁻¹ + v)⁻¹ - vx))⁻¹ =
                   ((evalNumExpr (deltas.apply vals) x))⁻¹ + v
              rw [show evalNumExpr (deltas.apply vals) x = vx from rfl]
              have h1 : vx + ((vx⁻¹ + v)⁻¹ - vx) = (vx⁻¹ + v)⁻¹ := by ring
              rw [h1, inv_inv]
      | mul m =>
          dsimp only [backwardEvalAtomic]
          by_cases hm : m = 0
          · rw [if_pos hm, embedNumDeltaInto_singleton_eval]
          · rw [if_neg hm]
            have ih := ihx (.mul (1 / m)) deltas
            show (evalNumExpr _ _)⁻¹ = _
            rw [ih]
            show ((evalNumExpr (deltas.apply vals) x) * (1 / m))⁻¹ =
                 ((evalNumExpr (deltas.apply vals) x))⁻¹ * m
            rw [mul_inv, one_div, inv_inv]


-- ============================================================================
-- PutGet for `backwardEvalNum` (the foldr-lift over a NumDelta list).
-- ============================================================================

/-- **PutGet for `backwardEvalNum`**: applying a NumDelta backwards and
re-evaluating yields the delta applied to the original evaluation. -/
theorem backwardEvalNum_putGet {n : Nat} (vals : Env n) :
    ∀ (ds : NumDelta) (deltas : DeltaEnv n) (e : NumExpr n),
      evalNumExpr ((backwardEvalNum ds vals deltas e).1.apply vals)
                  (backwardEvalNum ds vals deltas e).2 =
        ds.apply (evalNumExpr (deltas.apply vals) e) := by
  intro ds
  induction ds with
  | nil =>
      intro deltas e
      rfl
  | cons d ds' ih =>
      intro deltas e
      -- backwardEvalNum (d :: ds) vals deltas e
      --   = let (delt', e') := backwardEvalNum ds vals deltas e
      --     backwardEvalAtomic d vals delt' e'
      show evalNumExpr
            ((backwardEvalAtomic d vals
                (backwardEvalNum ds' vals deltas e).1
                (backwardEvalNum ds' vals deltas e).2).1.apply vals)
            ((backwardEvalAtomic d vals
                (backwardEvalNum ds' vals deltas e).1
                (backwardEvalNum ds' vals deltas e).2).2) =
            d.apply (NumDelta.apply ds' (evalNumExpr (deltas.apply vals) e))
      rw [backwardEvalAtomic_putGet vals
            (backwardEvalNum ds' vals deltas e).2
            d
            (backwardEvalNum ds' vals deltas e).1]
      rw [ih]


-- ============================================================================
-- Semantic value layer for Curves and Programs.
--
-- A `CurveValue` is the geometric "skeleton" of a curve with all numeric
-- expressions replaced by their `Rat` evaluations.  This lets us state PutGet
-- for `backwardEvalCurve` and `backwardEvalProgram` as a numeric equality
-- between values, lifted structurally over the curve tree.
-- ============================================================================

inductive CurveValue
  | epicycle : EpicycleId → Rat → Rat → Rat → CurveValue
  | append   : CurveValue → CurveValue → CurveValue
  deriving Repr

/-- Evaluate a `Curve` to its `CurveValue` skeleton. -/
def Curve.eval {n : Nat} (env : Env n) : Curve n → CurveValue
  | .epicycle eid r w p =>
      .epicycle eid (evalNumExpr env r) (evalNumExpr env w) (evalNumExpr env p)
  | .append c1 c2 => .append (c1.eval env) (c2.eval env)

/-- Evaluate a `Program` to its `CurveValue` skeleton (extending the env
through each `let`). -/
def Program.eval {n : Nat} : Env n → Program n → CurveValue
  | env, .done c => c.eval env
  | env, .letBind e1 body =>
      let v1 := evalNumExpr env e1
      Program.eval (env.extend v1) body

/-- The semantic action of a `CurveDelta` on a `CurveValue`. -/
def CurveDelta.applyVal : CurveDelta → CurveValue → CurveValue
  | .id,                          cv                  => cv
  | .targetEpi targetId dR dW dP, .epicycle eid r w p =>
      if targetId = eid then
        .epicycle eid (dR.apply r) (dW.apply w) (dP.apply p)
      else
        .epicycle eid r w p
  | dv@(.targetEpi _ _ _ _),      .append c1 c2       =>
      .append (dv.applyVal c1) (dv.applyVal c2)
  | .modAppend dL dR,             .append c1 c2       =>
      .append (dL.applyVal c1) (dR.applyVal c2)
  | .modAppend _ _,               cv@(.epicycle _ _ _ _) => cv

@[simp] theorem CurveDelta.applyVal_id (cv : CurveValue) :
    CurveDelta.id.applyVal cv = cv := by cases cv <;> rfl

@[simp] theorem CurveDelta.applyVal_targetEpi_append (targetId : EpicycleId)
    (dR dW dP : NumDelta) (v1 v2 : CurveValue) :
    (CurveDelta.targetEpi targetId dR dW dP).applyVal (.append v1 v2) =
      .append ((CurveDelta.targetEpi targetId dR dW dP).applyVal v1)
              ((CurveDelta.targetEpi targetId dR dW dP).applyVal v2) := rfl

@[simp] theorem CurveDelta.applyVal_modAppend_append (dL dR : CurveDelta)
    (v1 v2 : CurveValue) :
    (CurveDelta.modAppend dL dR).applyVal (.append v1 v2) =
      .append (dL.applyVal v1) (dR.applyVal v2) := rfl

@[simp] theorem CurveDelta.applyVal_modAppend_epicycle (dL dR : CurveDelta)
    (eid : EpicycleId) (r w p : Rat) :
    (CurveDelta.modAppend dL dR).applyVal (.epicycle eid r w p) =
      .epicycle eid r w p := rfl


-- ============================================================================
-- Helper: agreement of evals on free variables for Curves.
-- ============================================================================

theorem Curve.eval_eq_of_agree_on_free {n : Nat} :
    ∀ (c : Curve n) (σ1 σ2 : Env n),
      (∀ i : Fin n, c.isFreeIn i = true → σ1 i = σ2 i) →
      c.eval σ1 = c.eval σ2
  | .epicycle _ r w p, σ1, σ2, h => by
      simp [Curve.eval,
            NumExpr.eval_eq_of_agree_on_free r σ1 σ2
              (fun i hi => h i (by simp [Curve.isFreeIn, hi])),
            NumExpr.eval_eq_of_agree_on_free w σ1 σ2
              (fun i hi => h i (by simp [Curve.isFreeIn, hi])),
            NumExpr.eval_eq_of_agree_on_free p σ1 σ2
              (fun i hi => h i (by simp [Curve.isFreeIn, hi]))]
  | .append c1 c2, σ1, σ2, h => by
      simp [Curve.eval,
            Curve.eval_eq_of_agree_on_free c1 σ1 σ2
              (fun i hi => h i (by simp [Curve.isFreeIn, hi])),
            Curve.eval_eq_of_agree_on_free c2 σ1 σ2
              (fun i hi => h i (by simp [Curve.isFreeIn, hi]))]


-- ============================================================================
-- Embed-soundness for Curves: evaluating an embedded curve under `vals`
-- equals evaluating the original under `env.apply vals`.
-- ============================================================================

theorem Curve.embed_eval {n : Nat} (vals : Env n) (env : DeltaEnv n) :
    ∀ (c : Curve n), (c.embed env).eval vals = c.eval (env.apply vals)
  | .epicycle eid r w p => by
      simp [Curve.embed, Curve.eval, NumExpr.embed_eval]
  | .append c1 c2 => by
      simp [Curve.embed, Curve.eval, Curve.embed_eval vals env c1,
            Curve.embed_eval vals env c2]


-- ============================================================================
-- Merge-correctness for Curves (analogue of optMergeNum_eval_*).
-- ============================================================================

/-- Generic merge-recovery for an embedded `Curve`. -/
private theorem evalCurve_recover {n : Nat} (vals : Env n)
    (envFinal envOrig residual : DeltaEnv n) (c : Curve n)
    (hRec : ∀ i : Fin n, c.isFreeIn i = true → residual i ++ envFinal i = envOrig i) :
    (c.embed residual).eval (envFinal.apply vals) = c.eval (envOrig.apply vals) := by
  rw [Curve.embed_eval]
  apply Curve.eval_eq_of_agree_on_free
  intro i hfree
  show (residual i).apply ((envFinal i).apply (vals i)) = (envOrig i).apply (vals i)
  rw [← NumDelta.apply_append, hRec i hfree]

theorem optMergeCurve_eval_left {n : Nat} (vals : Env n)
    (env1 env2 : DeltaEnv n) (c1 c2 : Curve n) :
    ((optMergeCurve env1 env2 c1 c2).2.1).eval
      ((optMergeCurve env1 env2 c1 c2).1.apply vals) =
      c1.eval (env1.apply vals) :=
  evalCurve_recover vals _ env1 _ c1
    (fun i => compareOperator_recover_left env1 env2 (c1.isFreeIn ·) (c2.isFreeIn ·) i)

theorem optMergeCurve_eval_right {n : Nat} (vals : Env n)
    (env1 env2 : DeltaEnv n) (c1 c2 : Curve n) :
    ((optMergeCurve env1 env2 c1 c2).2.2).eval
      ((optMergeCurve env1 env2 c1 c2).1.apply vals) =
      c2.eval (env2.apply vals) :=
  evalCurve_recover vals _ env2 _ c2
    (fun i => compareOperator_recover_right env1 env2 (c1.isFreeIn ·) (c2.isFreeIn ·) i)



-- ============================================================================
-- PutGet for `backwardEvalCurve`.
-- ============================================================================

/-- **PutGet for `backwardEvalCurve`**: applying a `CurveDelta` backwards
to a let-free `Curve` and re-evaluating yields the curve delta applied to
the original evaluation. -/
theorem backwardEvalCurve_putGet {n : Nat} (vals : Env n) :
    ∀ (dv : CurveDelta) (deltas : DeltaEnv n) (c : Curve n),
      ((backwardEvalCurve dv vals deltas c).2).eval
        ((backwardEvalCurve dv vals deltas c).1.apply vals) =
        dv.applyVal (c.eval (deltas.apply vals)) := by
  intro dv
  induction dv with
  | id =>
      intro deltas c
      simp
  | targetEpi targetId dR dW dP =>
      intro deltas c
      induction c with
      | epicycle eid r w p =>
          dsimp only [backwardEvalCurve]
          by_cases hk : targetId = eid
          · -- Hit case.  Names for per-component backwards results.
            rw [if_pos hk]
            set envR := (backwardEvalNum dR vals deltas r).1
            set r'   := (backwardEvalNum dR vals deltas r).2
            set envW := (backwardEvalNum dW vals deltas w).1
            set w'   := (backwardEvalNum dW vals deltas w).2
            set envP := (backwardEvalNum dP vals deltas p).1
            set p'   := (backwardEvalNum dP vals deltas p).2
            set envRW := (compareOperator envR envW r'.isFreeIn w'.isFreeIn).1
            set envRI := (compareOperator envR envW r'.isFreeIn w'.isFreeIn).2.1
            set envWI := (compareOperator envR envW r'.isFreeIn w'.isFreeIn).2.2
            set r'' := r'.embed envRI
            set w'' := w'.embed envWI
            set eM     := (compareOperator envRW envP
                            (fun i => r''.isFreeIn i || w''.isFreeIn i) p'.isFreeIn).1
            set envRWI := (compareOperator envRW envP
                            (fun i => r''.isFreeIn i || w''.isFreeIn i) p'.isFreeIn).2.1
            set envPI  := (compareOperator envRW envP
                            (fun i => r''.isFreeIn i || w''.isFreeIn i) p'.isFreeIn).2.2
            -- Reduce RHS to component-wise applies via `applyVal` + `hk`.
            show CurveValue.epicycle eid _ _ _ =
                 (CurveDelta.targetEpi targetId dR dW dP).applyVal
                   (CurveValue.epicycle eid _ _ _)
            rw [show (CurveDelta.targetEpi targetId dR dW dP).applyVal
                       (CurveValue.epicycle eid (evalNumExpr (deltas.apply vals) r)
                                                (evalNumExpr (deltas.apply vals) w)
                                                (evalNumExpr (deltas.apply vals) p)) =
                 CurveValue.epicycle eid (dR.apply (evalNumExpr (deltas.apply vals) r))
                                         (dW.apply (evalNumExpr (deltas.apply vals) w))
                                         (dP.apply (evalNumExpr (deltas.apply vals) p))
                 from by simp [CurveDelta.applyVal, hk]]
            -- Recovery shorthands for the outer and inner merges.
            have outerL := fun i (h : (r''.isFreeIn i || w''.isFreeIn i) = true) =>
              compareOperator_recover_left envRW envP
                (fun j => r''.isFreeIn j || w''.isFreeIn j) p'.isFreeIn i h
            have outerR := compareOperator_recover_right envRW envP
                              (fun j => r''.isFreeIn j || w''.isFreeIn j) p'.isFreeIn
            have innerL := compareOperator_recover_left envR envW r'.isFreeIn w'.isFreeIn
            have innerR := compareOperator_recover_right envR envW r'.isFreeIn w'.isFreeIn
            congr 1
            · rw [evalNumExpr_recover_chain vals eM envRW envR envRWI envRI r'
                    (fun i hf => outerL i (by show (_ || _) = true; rw [hf]; rfl)) innerL]
              exact backwardEvalNum_putGet vals dR deltas r
            · rw [evalNumExpr_recover_chain vals eM envRW envW envRWI envWI w'
                    (fun i hf => outerL i (by show (_ || _) = true; rw [hf]; simp)) innerR]
              exact backwardEvalNum_putGet vals dW deltas w
            · rw [evalNumExpr_recover vals eM envP envPI p' outerR]
              exact backwardEvalNum_putGet vals dP deltas p
          · -- Miss case.
            rw [if_neg hk]
            simp [Curve.eval, CurveDelta.applyVal, hk]
      | append c1 c2 ih1 ih2 =>
          dsimp only [backwardEvalCurve, Curve.eval]
          simp only [CurveDelta.applyVal_targetEpi_append]
          congr 1
          · rw [optMergeCurve_eval_left]; exact ih1
          · rw [optMergeCurve_eval_right]; exact ih2
  | modAppend dL dR ihL ihR =>
      intro deltas c
      cases c with
      | epicycle eid r w p => rfl
      | append c1 c2 =>
          dsimp only [backwardEvalCurve, Curve.eval]
          simp only [CurveDelta.applyVal_modAppend_append]
          congr 1
          · rw [optMergeCurve_eval_left]; exact ihL deltas c1
          · rw [optMergeCurve_eval_right]; exact ihR deltas c2


-- ============================================================================
-- Helper: agreement of evals on free variables for Programs
-- ============================================================================

theorem Program.eval_eq_of_agree_on_free {n : Nat} :
    ∀ (P : Program n) (σ1 σ2 : Env n),
      (∀ i : Fin n, P.isFreeIn i = true → σ1 i = σ2 i) →
      P.eval σ1 = P.eval σ2
  | .done c, σ1, σ2, h => Curve.eval_eq_of_agree_on_free c σ1 σ2 h
  | .letBind e1 body, σ1, σ2, h => by
      dsimp only [Program.eval]
      have he1 : evalNumExpr σ1 e1 = evalNumExpr σ2 e1 :=
        NumExpr.eval_eq_of_agree_on_free e1 σ1 σ2
          (fun i hi => h i (by simp [Program.isFreeIn, hi]))
      rw [he1]
      apply Program.eval_eq_of_agree_on_free
      intro i hi
      cases i using Fin.cases with
      | zero => rfl
      | succ j => exact h j (by simp [Program.isFreeIn, hi])

-- ============================================================================
-- Embed-soundness for Programs
-- ============================================================================

@[simp] theorem DeltaEnv.extend_apply {n : Nat} (env : DeltaEnv n) (vals : Env n) (v : Rat) :
    (env.extend []).apply (vals.extend v) = (env.apply vals).extend v := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Splitting a `DeltaEnv (n+1)` into its head and tail recovers the original
on `apply` of an extended `Env`, provided the head is applied to the bound value. -/
@[simp] theorem DeltaEnv.split_extend_apply {n : Nat} (env : DeltaEnv (n+1))
    (vals : Env n) (v : Rat) :
    DeltaEnv.apply (DeltaEnv.extend (fun i : Fin n => env i.succ) []) (vals.extend ((env 0).apply v)) =
      env.apply (vals.extend v) := by
  funext i; cases i using Fin.cases <;> rfl

theorem Program.embed_eval {n : Nat} (vals : Env n) (env : DeltaEnv n) :
    ∀ (P : Program n), (P.embed env).eval vals = P.eval (env.apply vals)
  | .done c => Curve.embed_eval vals env c
  | .letBind e1 body => by
      dsimp only [Program.embed, Program.eval]
      rw [NumExpr.embed_eval, Program.embed_eval, DeltaEnv.extend_apply]

-- ============================================================================
-- Merge-correctness for Programs
-- ============================================================================

/-- The left half of a let-merge is just `evalNumExpr_recover` on `e1`. -/
theorem optMergeLetProgram_eval_left {n : Nat} (vals : Env n)
    (envVal envBody : DeltaEnv n) (e1 : NumExpr n) (body : Program (n + 1)) :
    evalNumExpr ((optMergeLetProgram envVal envBody e1 body).1.apply vals)
                (optMergeLetProgram envVal envBody e1 body).2.1 =
      evalNumExpr (envVal.apply vals) e1 :=
  evalNumExpr_recover vals _ envVal _ e1
    (fun i => compareOperator_recover_left envVal envBody
                (e1.isFreeIn ·) (body.isFreeIn ·.succ) i)

/-- The right half of a let-merge: the residual on the body is extended by
`[]` at the bound variable, and the recovery follows from
`compareOperator_recover_right` at the `succ`-indices. -/
theorem optMergeLetProgram_eval_right {n : Nat} (vals : Env n)
    (envVal envBody : DeltaEnv n) (e1 : NumExpr n) (body : Program (n + 1)) (v : Rat) :
    ((optMergeLetProgram envVal envBody e1 body).2.2).eval
      (((optMergeLetProgram envVal envBody e1 body).1.extend []).apply (vals.extend v)) =
      body.eval ((envBody.extend []).apply (vals.extend v)) := by
  show (body.embed ((cmpE2I envVal envBody (e1.isFreeIn ·) (body.isFreeIn ·.succ)).extend [])).eval
        (((cmpEM envVal envBody (e1.isFreeIn ·) (body.isFreeIn ·.succ)).extend []).apply (vals.extend v)) =
       body.eval ((envBody.extend []).apply (vals.extend v))
  rw [Program.embed_eval]
  apply Program.eval_eq_of_agree_on_free
  intro i hfree
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
      show ((cmpE2I envVal envBody (e1.isFreeIn ·) (body.isFreeIn ·.succ)) j).apply
            (((cmpEM envVal envBody (e1.isFreeIn ·) (body.isFreeIn ·.succ)) j).apply (vals j)) =
           (envBody j).apply (vals j)
      rw [← NumDelta.apply_append,
          compareOperator_recover_right envVal envBody (e1.isFreeIn ·) (body.isFreeIn ·.succ) j hfree]

-- ============================================================================
-- PutGet for `backwardEvalProgram`
-- ============================================================================

/-- **PutGet for `backwardEvalProgram`**: applying a `CurveDelta` backwards
to a let-normal `Program` and re-evaluating yields the curve delta applied to
the original evaluation. -/
theorem backwardEvalProgram_putGet {n : Nat} (vals : Env n) :
    ∀ (dv : CurveDelta) (deltas : DeltaEnv n) (P : Program n),
      ((backwardEvalProgram dv vals deltas P).2).eval
        ((backwardEvalProgram dv vals deltas P).1.apply vals) =
        dv.applyVal (P.eval (deltas.apply vals)) := by
  intro dv deltas P
  induction P with
  | done c =>
      exact backwardEvalCurve_putGet vals dv deltas c
  | letBind e1 body ih =>
      dsimp only [backwardEvalProgram, Program.eval]
      set v1 := evalNumExpr (deltas.apply vals) e1
      set envBody := (backwardEvalProgram dv (vals.extend v1) (deltas.extend []) body).1
      set body' := (backwardEvalProgram dv (vals.extend v1) (deltas.extend []) body).2
      set dv_x := envBody 0
      set deltaBody : DeltaEnv _ := fun i => envBody i.succ
      set envVal := (backwardEvalNum dv_x vals deltas e1).1
      set e1' := (backwardEvalNum dv_x vals deltas e1).2
      -- 1. Bound-value evaluation: merge-left + putGet on numeric layer.
      rw [optMergeLetProgram_eval_left, backwardEvalNum_putGet]
      -- 2. Body: switch outer env to the extend-form, apply merge-right, then simp.
      rw [show ((optMergeLetProgram envVal deltaBody e1' body').1.apply vals).extend (dv_x.apply v1)
            = ((optMergeLetProgram envVal deltaBody e1' body').1.extend []).apply
                (vals.extend (dv_x.apply v1)) from
            (DeltaEnv.extend_apply _ _ _).symm,
          optMergeLetProgram_eval_right, DeltaEnv.split_extend_apply]
      simpa using ih (vals.extend v1) (deltas.extend [])
