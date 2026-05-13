import Mathlib.Data.Fin.Tuple.Basic
import Epicycles.Env

/-! Lean implementation of the delta language for our DSL.
Generated WITHOUT the assistance of AI
-/

inductive AtomicNumDelta
  | add (n : Rat)
  | mul (n : Rat)
  | replace (n : Rat)
  deriving Repr, BEq, DecidableEq

abbrev NumDelta := List AtomicNumDelta

def AtomicNumDelta.apply : AtomicNumDelta → Rat → Rat
  | .add n, x => x + n
  | .mul n, x => x * n
  | .replace n, _ => n

def NumDelta.apply (ds : NumDelta) (x : Rat) : Rat :=
  ds.foldr AtomicNumDelta.apply x

def AtomicNumDelta.isId : AtomicNumDelta → Bool
  | .add n => n == 0
  | .mul n => n == 1
  | _ => false

def NumDelta.simplify (d : NumDelta) : NumDelta :=
  d.filter (not ∘ AtomicNumDelta.isId)

def NumDelta.size (d : NumDelta) : Nat := d.length

inductive CurveDelta
  | id
  | targetEpi (k : EpicycleId) (r w p : NumDelta)
  | modAppend (dL dR : CurveDelta)
  deriving Repr, BEq

abbrev DeltaEnv (n : Nat) := Fin n → NumDelta

def DeltaEnv.empty : DeltaEnv 0 :=
  fun i => nomatch i

def DeltaEnv.extend {n : Nat} (dEnv : DeltaEnv n) (d : NumDelta) : DeltaEnv (n + 1) :=
  Fin.cons d dEnv

def DeltaEnv.apply {n : Nat} (dEnv : DeltaEnv n) (env : Env n) : Env n :=
  fun i => (dEnv i).apply (env i)

def DeltaEnv.update {n : Nat} (env : DeltaEnv n) (ix : Fin n) (d : NumDelta) : DeltaEnv n :=
  fun i => if i == ix then d else env i

def DeltaEnv.id (n : Nat) : DeltaEnv n :=
  fun _ => []

@[simp] theorem DeltaEnv.apply_id {n : Nat} (env : Env n) :
    (DeltaEnv.id n).apply env = env := by
  funext i
  rfl

def splitCommonPrefix {α} [BEq α] : List α → List α → List α × List α × List α
  | a::as, b::bs =>
      if a == b then
        let (c, a', b') := splitCommonPrefix as bs
        (a::c, a', b')
      else ([], a::as, b::bs)
  | as, bs => ([], as, bs)

def NumDelta.splitSuffix (d1 d2 : NumDelta) : NumDelta × NumDelta × NumDelta :=
  let (sRev, p1Rev, p2Rev) := splitCommonPrefix d1.reverse d2.reverse
  (sRev.reverse, p1Rev.reverse, p2Rev.reverse)
