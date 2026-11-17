import Epicycles.AST
inductive ProxyTop : Nat → Type
  | ptop {n : Nat} : ProxyTop (n + 1)



class ReifyIndex (b u : Nat) where
  reify : ProxyTop b → Fin u

instance instRefl {n : Nat} : ReifyIndex n n where
  reify := fun p => match p with
  | .ptop => 0

instance instSnoc {b u : Nat} [instRec: ReifyIndex b u] : ReifyIndex b (u + 1) where
  reify p := (ReifyIndex.reify p).succ

inductive ProxyVar (n : Nat) : Type where
  | pvar {b : Nat} [inst: ReifyIndex b n] : ProxyTop b → ProxyVar n

inductive ExprCtx : Nat → Type where
  | clit   : {n : Nat} → Rat → ExprCtx n
  | cvar   {b n: Nat} [ReifyIndex b n] : ProxyTop b → ExprCtx n
  | cadd   : {n : Nat} → ExprCtx n → ExprCtx n → ExprCtx n
  | cmul   : {n : Nat} → ExprCtx n → ExprCtx n → ExprCtx n
  | crecip : {n : Nat} → ExprCtx n → ExprCtx n
  | clet  : {n : Nat} → ExprCtx n → (ProxyTop (n + 1) → ExprCtx (n + 1)) → ExprCtx n


/-
unembed :: ASTCtx env s -> AST Parsed env s
unembed (CLit n) = Lit n
unembed (CParam_ x p) = Param_ x (reify p)
unembed (CAdd a b) = Add (unembed a) (unembed b)
unembed (CMul a b) = Mul (unembed a) (unembed b)
unembed (CRecip a) = Recip (unembed a)
unembed (CEpicycle r f p) = Epicycle () (unembed r) (unembed f) (unembed p)
unembed (CAppend a b) = Append (unembed a) (unembed b)
unembed (CLet v k) = Let (unembed v) (unembed (k ProxyTop))
-/
def unembed  {n:Nat} : ExprCtx n → Expr n
  | .clit r => .lit r
  | @ExprCtx.cvar _ _ _ p => .var (ReifyIndex.reify p)
  | .cadd a b => .add (unembed a) (unembed b)
  | .cmul a b => .mul (unembed a) (unembed b)
  | .crecip n => .recip (unembed n)
  | .clet v k => .let_ (unembed v) (unembed (k .ptop))


def weaken {n : Nat} : ProxyVar n → ProxyVar (n + 1)
  | @ProxyVar.pvar _ _ _ p => .pvar p

def fromIndex : {n : Nat} → (Fin n) → ProxyVar n
  | 0, i => i.elim0
  | m + 1, ⟨ 0, _ ⟩ => .pvar ( b := m + 1) .ptop
  | _m + 1, ⟨ k + 1, h ⟩ => weaken (fromIndex ⟨ k, Nat.lt_of_succ_lt_succ h⟩)

def contextualise {n : Nat}  : Expr n → ExprCtx n
  | .lit n => .clit n
  | .var i => match fromIndex i with
      | @ProxyVar.pvar _ _ _ top  => .cvar top
  | .add a b => .cadd (contextualise a) (contextualise b)
  | .mul a b => .cmul (contextualise a) (contextualise b)
  | .recip n => .crecip (contextualise n)
  | .let_ v k => .clet (contextualise v) (fun _ => contextualise k)

def fromVar {n: Nat} : ProxyVar n → ExprCtx n
  | ProxyVar.pvar i => .cvar i

def toCVar : {n : Nat} → Fin n → ExprCtx n :=
  λ i => fromVar (fromIndex i)


theorem reify_weaken {n : Nat} (v : ProxyVar n) :
    (weaken v).2.reify (weaken v).3 = (v.2.reify v.3).succ := by
  cases v
  rfl

theorem fromIndex_succ {n : Nat} (i : Fin n) : fromIndex i.succ = weaken (fromIndex i) := rfl

theorem reify_snoc {b u : Nat} [inst : ReifyIndex b u] (p : ProxyTop b) :
    (instSnoc (instRec := inst) : ReifyIndex b (u + 1)).reify p = (inst.reify p).succ := rfl

theorem indexIsoL : { n : Nat} →  (i : Fin n) → (fromIndex i).2.reify (fromIndex i).3 = i
   | 0, i => i.elim0
   | m + 1, ⟨ 0, _h ⟩ => rfl
   | m + 1, ⟨ k + 1, h ⟩ => by
    rw [fromIndex, reify_weaken, indexIsoL]
    simp

axiom closedWorld {n n' : Nat} (inst : ReifyIndex n n')
  : (∃(hEq : n = n'), hEq ▸ inst = instRefl) -- instRefl used
    \/
    (∃ (n2' : Nat) (hEq : n' = n2' + 1) (inst' : ReifyIndex n n2'),
      hEq ▸ inst = instSnoc (instRec := inst'))

theorem indexIsoR { n n': Nat } (inst : ReifyIndex n n')  (i : ProxyTop n) : fromIndex (inst.reify i) = ProxyVar.pvar (inst := inst) i :=
 Or.elim (closedWorld inst)
  (λ⟨ hEq, instRefl⟩ => by

    subst hEq
    simp at instRefl
    rw [instRefl]
    cases i
    · rfl
   )
   (λ ⟨ n2', hEq, inst', hInst ⟩ => by
    subst hEq
    simp at hInst
    subst hInst
    rw [reify_snoc, fromIndex_succ, indexIsoR inst' i]
    rfl
   )




theorem isoL {n : Nat}  {e : Expr n} : unembed (contextualise e) = e := by
  induction e with
  | lit n => rfl
  | var i =>
    simp [unembed, contextualise, indexIsoL]
  | add x y ih1 ih2 => simp [ih1, ih2, unembed, contextualise]
  | mul x y ih1 ih2 => simp [ih1, ih2, unembed, contextualise]
  | recip n ih => simp [ih, unembed, contextualise]
  | let_ v k ih1 ih2 =>simp [ih1, ih2, unembed, contextualise]

theorem isoR {n : Nat} { e : ExprCtx n} : contextualise (unembed e) = e := by
  induction e with
  | clit n => rfl
  | cvar  n =>
    simp only [unembed, contextualise]
    rw [indexIsoR]
  | cadd a b iha ihb => simp [unembed, contextualise, iha, ihb]
  | cmul a b iha ihb => simp [unembed, contextualise, iha, ihb]
  | crecip n ih => simp [unembed, contextualise, ih]
  | clet v e ihv ihe =>
      simp [unembed, contextualise, ihv, ihe]
      funext x
      cases x
      rfl
