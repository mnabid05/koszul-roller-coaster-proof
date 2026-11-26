import Conjectures.RollerIdealBasisDefs

/-! Multiplication on the face and dual-face basis, inside the commutative
idealization. In particular, multiplying a dual face removes a subset. -/
noncomputable section
open scoped Classical
open RollerFaceRing RollerGorenstein
namespace RollerIdealGrading
variable {V : Type*} [Fintype V] (K : Type*) [Field K] (C : Complex V)

omit [Fintype V] in
theorem primal_empty : primal K C (emptyFace C) = 1 := by
  apply Prod.ext
  · exact faceMonomial_empty K C
  · rfl

omit [Fintype V] in
theorem primal_mul_primal (s t : Face C) :
    primal K C s * primal K C t =
      if h : Disjoint s.val t.val ∧ C.face (s.val ∪ t.val) then
        primal K C ⟨s.val ∪ t.val,h.2⟩ else 0 := by
  apply Prod.ext
  · rw [mul_fst]
    simpa only [primal,apply_dite Prod.fst] using faceMonomial_mul K C s t
  · rw [show ((primal K C s * primal K C t).2) = 0 from by
      apply LinearMap.ext; intro x; rw [mul_snd]; change (0 : K) + 0 = 0; exact add_zero 0]
    split <;> rfl

@[simp] theorem dual_mul_dual (s t : Face C) : dual K C s * dual K C t = 0 := by
  apply Prod.ext
  · rw [mul_fst]; exact zero_mul _
  · apply LinearMap.ext
    intro x
    rw [mul_snd]
    change (basis K C).coord t (0*x) + (basis K C).coord s (0*x) = 0
    simp

private theorem coord_mul_face (s t u : Face C) :
    (basis K C).coord t (faceMonomial K C s * faceMonomial K C u) =
    if _h : s.val ⊆ t.val then
      (basis K C).coord ⟨t.val \ s.val,C.downward Finset.sdiff_subset t.property⟩ (faceMonomial K C u)
    else 0 := by
  simp only [Basis.coord_apply, basis_repr_apply, coordinates_faceMonomial, faceMonomial_mul]
  split
  next h =>
    rw [coordinates_faceMonomial]
    by_cases hst : s.val ⊆ t.val
    · rw [dif_pos hst]
      apply if_congr ?_ rfl rfl
      constructor
      · intro he
        apply Subtype.ext
        have ht : s.val ∪ u.val = t.val := congrArg Subtype.val he
        change u.val = t.val \ s.val
        rw [← ht,Finset.union_sdiff_cancel_left h.1]
      · intro he
        apply Subtype.ext
        have hu := congrArg Subtype.val he
        change u.val = t.val \ s.val at hu
        change s.val ∪ u.val = t.val
        rw [hu,Finset.union_sdiff_of_subset hst]
    · rw [dif_neg hst]
      apply if_neg
      intro he
      apply hst
      exact (congrArg Subtype.val he) ▸ Finset.subset_union_left
  next h =>
    rw [map_zero]
    split
    next hst =>
      apply Eq.symm
      apply if_neg
      intro he
      have hu := congrArg Subtype.val he
      change u.val = t.val \ s.val at hu
      apply h
      rw [hu]
      exact ⟨Finset.disjoint_sdiff, (Finset.union_sdiff_of_subset hst).symm ▸ t.property⟩
    next => rfl

theorem primal_mul_dual (s t : Face C) :
    primal K C s * dual K C t =
      if _h : s.val ⊆ t.val then
        dual K C ⟨t.val \ s.val, C.downward Finset.sdiff_subset t.property⟩ else 0 := by
  apply Prod.ext
  · rw [mul_fst]
    change faceMonomial K C s * 0 = _
    rw [mul_zero]
    split <;> rfl
  · apply (basis K C).ext
    intro u
    rw [basis_apply]
    change (primal K C s * dual K C t).2 (faceMonomial K C u) = _
    rw [mul_snd]
    change (basis K C).coord t (faceMonomial K C s * faceMonomial K C u) + 0 = _
    rw [add_zero,coord_mul_face]
    split <;> rfl

end RollerIdealGrading
