import Conjectures.RollerIdealBasis

/-! The multiplicative monoid consisting of the primal and dual face basis vectors
and the absorbing zero. It embeds into the actual idealization over any field. -/
noncomputable section
open scoped Classical
open RollerFaceRing

namespace RollerFaceMonoid

variable {V : Type*} (C : Complex V)

inductive Term
  | killed : Term
  | primal : Face C → Term
  | dual : Face C → Term

def indexEquiv : Term C ≃ Option (Face C ⊕ Face C) where
  toFun
    | .killed => none
    | .primal s => some (.inl s)
    | .dual s => some (.inr s)
  invFun
    | none => .killed
    | some (.inl s) => .primal s
    | some (.inr s) => .dual s
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | (s | s) <;> rfl

instance [Fintype V] : Fintype (Term C) := Fintype.ofEquiv _ (indexEquiv C).symm

instance : Zero (Term C) := ⟨.killed⟩
instance : One (Term C) := ⟨.primal (emptyFace C)⟩

private def combine (s t : Face C) : Term C :=
  if h : Disjoint s.val t.val ∧ C.face (s.val ∪ t.val) then .primal ⟨s.val ∪ t.val,h.2⟩
  else .killed

private def remove (s t : Face C) : Term C :=
  if s.val ⊆ t.val then .dual ⟨t.val \ s.val, C.downward Finset.sdiff_subset t.property⟩
  else .killed

instance : Mul (Term C) where
  mul
    | .killed, _ => .killed
    | _, .killed => .killed
    | .primal s, .primal t => combine C s t
    | .primal s, .dual t => remove C s t
    | .dual t, .primal s => remove C s t
    | .dual _, .dual _ => .killed

theorem primal_mul_primal (s t : Face C) :
    Term.primal s * Term.primal t =
    if h : Disjoint s.val t.val ∧ C.face (s.val ∪ t.val) then
      Term.primal ⟨s.val ∪ t.val,h.2⟩ else (0 : Term C) := rfl

theorem primal_mul_dual (s t : Face C) :
    Term.primal s * Term.dual t =
    if s.val ⊆ t.val then Term.dual ⟨t.val \ s.val, C.downward Finset.sdiff_subset t.property⟩
    else (0 : Term C) := rfl

@[simp] theorem dual_mul_dual (s t : Face C) : Term.dual s * Term.dual t = (0 : Term C) := rfl

variable [Fintype V] (K : Type*) [Field K]

def value : Term C → RollerIdealGrading.A K C
  | .killed => 0
  | .primal s => RollerIdealGrading.primal K C s
  | .dual s => RollerIdealGrading.dual K C s

theorem value_injective : Function.Injective (value C K) := by
  let b := RollerIdealGrading.idealBasis K C
  have h (t : Term C) :
      value C K t = ((indexEquiv C t).elim 0 fun i => b i) := by
    cases t <;> simp [value,indexEquiv,b]
  intro x y he
  apply (indexEquiv C).injective
  rw [h,h] at he
  generalize indexEquiv C x = i at he ⊢
  generalize indexEquiv C y = j at he ⊢
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact False.elim (b.ne_zero j he.symm)
  | some i =>
    cases j with
    | none => exact False.elim (b.ne_zero i he)
    | some j => exact congrArg some (b.injective he)

theorem value_mul (x y : Term C) : value C K (x*y) = value C K x * value C K y := by
  cases x with
  | killed => cases y <;> simp [value]
  | primal s =>
    cases y with
    | killed => simp [value]
    | primal t =>
      rw [primal_mul_primal]
      simp only [value, RollerIdealGrading.primal_mul_primal]
      by_cases h : Disjoint s.val t.val ∧ C.face (s.val ∪ t.val) <;> simp [h]
    | dual t =>
      rw [primal_mul_dual]
      simp only [value, RollerIdealGrading.primal_mul_dual]
      by_cases h : s.val ⊆ t.val <;> simp [h]
  | dual s =>
    cases y with
    | killed => simp [value]
    | primal t =>
      change value C K (Term.primal t * Term.dual s) = _
      rw [primal_mul_dual]
      simp only [value,mul_comm (RollerIdealGrading.dual K C s), RollerIdealGrading.primal_mul_dual]
      by_cases h : t.val ⊆ s.val <;> simp [h]
    | dual t => rw [dual_mul_dual]; simp [value]

theorem value_one : value C K 1 = 1 := RollerIdealGrading.primal_empty K C

instance : CommMonoidWithZero (Term C) where
  mul_assoc x y z := (value_injective C ℚ) (by simp only [value_mul,mul_assoc])
  mul_comm x y := (value_injective C ℚ) (by simp only [value_mul,mul_comm])
  mul_one x := (value_injective C ℚ) (by rw [value_mul,value_one,mul_one])
  one_mul x := (value_injective C ℚ) (by rw [value_mul,value_one,one_mul])
  zero_mul x := by cases x <;> rfl
  mul_zero x := by cases x <;> rfl

def toRing : Term C →*₀ RollerIdealGrading.A K C where
  toFun := value C K
  map_zero' := rfl
  map_one' := value_one C K
  map_mul' := value_mul C K

theorem toRing_injective : Function.Injective (toRing C K) := value_injective C K

end RollerFaceMonoid
