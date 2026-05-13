import Epicycles.AST
import Mathlib.Data.Fin.Tuple.Basic

/-! Lean implementation of the environment type and some useful lemmas for it.
Generated WITHOUT the assistance of AI
-/

/-- The empty environment -/
def Env.empty : Env 0 :=
  fun i => nomatch i

/-- Extend env with a new innermost variable (for entering a let body) -/
def Env.extend {n : Nat} (env : Env n) (v : Rat) : Env (n + 1) :=
  Fin.cons v env

/-- Update a single variable in the environment -/
def Env.update {n : Nat} (env : Env n) (i : Fin n) (v : Rat) : Env n  :=
  fun j =>
    if j = i then v else env j


/-- if we update an environment at index i with the value that is already at index i, we get back the same environment -/
theorem Env.update_same {n : Nat} (env : Env n) (i : Fin n) :
    Env.update env i (env i) = env := by
  funext j -- prove function equality over parameter j
  unfold Env.update
  split --
  case isTrue h =>
   -- case j = i
    subst h
    rfl
  case isFalse h =>
   -- case j ≠ i
   rfl

/-- lemma that updating an environment at index i with value v, and then looking up index i, gives back v. i.e.  PutGet for environments -/
theorem Env.update_eq {n : Nat} (env : Env n) (i : Fin n) (v : Rat) :
    (Env.update env i) v i = v := by
  unfold Env.update
  simp

/-- lemma that updating env at index i with value v, and then looking up any index j that is not i, gives back the original env j
 i.e. updating an environment only changes the value at the updated index, and leaves all other indices unchanged
-/
theorem Env.update_ne {n : Nat} (env : Env n) {i j : Fin n} (v : Rat) (h : j ≠ i) :
    Env.update env i v j = env j := by
  unfold Env.update
  simp [h]


/-- PutPut for environments, i.e. setting env[i] = a, then env[i] = b is the same as just env[i] = b -/
lemma Env.update_putPut {n : Nat} (env : Env n) { i : Fin n} (v1 v2 : Rat):
   (Env.update env i v2) = (Env.update (Env.update env i v1) i v2) := by
   funext j
   simp [Env.update]
   split
   rfl
   rfl


/-- evaluating an extended environment at index 0 gives back the extended value -/
theorem Env.extend_zero {n : Nat} (env : Env n) (v : Rat) :
    Env.extend env v 0 = v := by
  unfold Env.extend
  simp

/-- evaluating an extended environment at index (i + 1) gives back the original environment at index i -/
theorem Env.extend_succ {n : Nat} (env : Env n) (v : Rat) (i : Fin n) :
    Env.extend env v (Fin.succ i) = env i := by
  unfold Env.extend
  simp


/-- extending an environment shifts all indices by 1 -/
theorem Env.extend_update_comm {n : Nat} (env : Env n) (i : Fin n) (v val : Rat) :
  (env.update i val).extend v = (env.extend v).update i.succ val := by
  funext j
  cases j using Fin.cases with
  | zero =>
      unfold Env.extend Env.update
      simp
      intro h_cont
      nomatch h_cont
  | succ j =>
      -- index j+1: both reduce to updating the original env
      simp [Env.extend, Env.update]
