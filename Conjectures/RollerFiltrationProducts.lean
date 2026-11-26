import Conjectures.RollerFiltration

/-! Multiplication of face basis vectors, with the finite-set operations taken
in the caller's decidable-equality instance. -/
noncomputable section
namespace RollerFiltration
open Finset RollerFaceMonoid RollerFaceRing
variable {V : Type*} {C : Complex V} [dec : DecidableEq V]

theorem primal_ok (s t : Face C) (hd : Disjoint s.val t.val) (hf : C.face (s.val∪t.val)) :
    Term.primal s * Term.primal t = Term.primal (⟨s.val∪t.val,hf⟩ : Face C) := by
  have eq : dec = Classical.decEq V := Subsingleton.elim _ _
  subst dec
  rw [primal_mul_primal,dif_pos ⟨hd,hf⟩]

theorem primal_fail (s t : Face C) (hn : ¬(Disjoint s.val t.val ∧ C.face (s.val∪t.val))) :
    Term.primal s * Term.primal t = (0 : Term C) := by
  have eq : dec = Classical.decEq V := Subsingleton.elim _ _
  subst dec
  rw [primal_mul_primal,dif_neg hn]

theorem dual_ok (s t : Face C) (hs : s.val⊆t.val) :
    Term.dual t * Term.primal s = Term.dual (⟨t.val \ s.val,C.downward sdiff_subset t.property⟩ : Face C) := by
  have eq : dec = Classical.decEq V := Subsingleton.elim _ _
  subst dec
  change Term.primal s * Term.dual t = _
  rw [primal_mul_dual,if_pos hs]

omit dec in
theorem dual_fail (s t : Face C) (hs : ¬s.val⊆t.val) :
    Term.dual t * Term.primal s = (0 : Term C) := by
  change Term.primal s * Term.dual t = _
  rw [primal_mul_dual,if_neg hs]

end RollerFiltration
