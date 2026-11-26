import Conjectures.RollerFiltrationProducts

/-! Facet-generator steps of the Koszul filtration. The surviving products
remember their multiplier by complementation inside the chosen facet. -/
noncomputable section
open scoped Classical
namespace RollerFiltration
open Finset RollerRealization RollerVertices RollerFaceMonoid RollerFaceRing

variable {p : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b)

private def recover (T : F h) : M h → M h
  | .dual u => .primal ⟨T.val \ u.val,(complex h).downward sdiff_subset T.property⟩
  | _ => .killed

private theorem recover_dual_product (T : F h) (a : M h) (hn : Term.dual T * a ≠ 0) :
    recover h T (Term.dual T*a) = a := by
  cases a with
  | killed => exact False.elim (hn (mul_zero _))
  | dual s => exact False.elim (hn (dual_mul_dual ..))
  | primal s =>
    by_cases hs : s.val ⊆ T.val
    · rw [dual_ok s T hs]
      apply congrArg Term.primal
      exact Subtype.ext (Finset.sdiff_sdiff_eq_self hs)
    · exact False.elim (hn (dual_fail s T hs))

/-- Removing a maximal old face gives a degree-one dual facet generator, its
previous stage, its colon, and cancellation outside that previous stage. -/
theorem facet_step (P : Initial h) (t : Finset (Vertex bs)) (ht : t∈P.faces)
    (hm : ∀ u∈P.faces,u.card≤t.card) :
    let Q := P.eraseMax t ht hm
    ∃ x : M h, (grading h).degree x = 1 ∧
      (∀ a, a∈facetIdeal h P ↔ a∈facetIdeal h Q ∨ ∃ b, x*b=a) ∧
      (∀ a, a∈vertexIdeal h (forbidden h t) ↔ x*a∈facetIdeal h Q) ∧
      ∀ a b, x*a∉facetIdeal h Q → x*a=x*b → a=b := by
  let Q := P.eraseMax t ht hm
  let T : F h := ⟨RollerShelling.completion (color h) t,completion_face (P.valid t ht)⟩
  let x : M h := .dual T
  have ht_card : T.val.card = p := by simp [T,RollerShelling.card_completion _ t (P.valid t ht).2]
  have hxP : x∈facetIdeal h P := by
    change (RollerShelling.completion (color h) t).toLeft∈P.faces
    simpa using ht
  refine ⟨x,?_,?_,?_,?_⟩
  · change p+1-T.val.card=1
    omega
  · intro a
    constructor
    · intro ha
      cases a with
      | killed => exact Or.inl trivial
      | primal s => exact False.elim ha
      | dual s =>
        change s.val.toLeft∈P.faces at ha
        by_cases he : s.val.toLeft = t
        · have hs : s.val⊆T.val := by simpa [T,← he] using subset_of_own_completion s.property
          let b : F h := ⟨T.val\s.val,(complex h).downward sdiff_subset T.property⟩
          refine Or.inr ⟨Term.primal b,?_⟩
          change Term.dual T * Term.primal b = Term.dual s
          rw [dual_ok b T (show b.val⊆T.val from sdiff_subset)]
          apply congrArg Term.dual
          exact Subtype.ext (Finset.sdiff_sdiff_eq_self hs)
        · exact Or.inl (mem_erase.mpr ⟨he,ha⟩)
    · rintro (ha|⟨b,rfl⟩)
      · cases a with
        | killed => trivial
        | primal s => exact False.elim ha
        | dual s => exact (mem_erase.mp ha).2
      · exact (facet_closed h P).mul_mem x hxP b
  · intro a
    cases a with
    | killed => exact iff_of_true trivial trivial
    | dual s => exact iff_of_true trivial trivial
    | primal s =>
      change hits (forbidden h t) s.val ↔ Term.dual T * Term.primal s ∈ facetIdeal h Q
      rw [hits_forbidden]
      by_cases hs : s.val ⊆ T.val
      · rw [dual_ok s T hs]
        change (¬s.val⊆T.val ∨ s.val.toLeft.Nonempty) ↔ (T.val\s.val).toLeft∈P.faces.erase t
        rw [dual_previous_iff P ht hs]
        simp [hs]
      · rw [dual_fail s T hs]
        exact iff_of_true (Or.inl hs) trivial
  · intro a b ha he
    have hn : x*a ≠ 0 := fun e => ha (e ▸ trivial)
    exact (recover_dual_product h T a hn).symm.trans
      ((congrArg (recover h T) he).trans (recover_dual_product h T b (he ▸ hn)))

end RollerFiltration
