import Conjectures.RollerIdealGrading

/-! Multiplication to the top degree gives perfect pairings on complementary
homogeneous components of the graded face idealization. -/
noncomputable section
namespace RollerIdealGrading

open RollerFaceRing RollerGorenstein
open scoped Classical
variable {V : Type*} [Fintype V] (K : Type*) [Field K] (C : Complex V)

private theorem trace_dual (s : Face C) :
    trace K _ (dual K C s) = if s=emptyFace C then 1 else 0 := by
  change (basis K C).repr 1 s = _
  rw [basis_repr_apply,← faceMonomial_empty K C,coordinates_faceMonomial]
  simp [eq_comm]

theorem trace_zero_other_degree {d k : ℕ} (hk : k≠d) {x : A K C} (hx : x∈piece K C d k) :
    trace K _ x = 0 := by
  have le : piece K C d k ≤ LinearMap.ker (trace K (Ring K C)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change trace K _ (idealBasis K C i)=0
    cases i with
    | inl s => rw [idealBasis_inl]; rfl
    | inr s =>
      rw [idealBasis_inr,trace_dual,if_neg]
      intro hs
      subst s
      change (∅ : Finset V).card+k=d at hi
      exact hk (by simpa using hi)
  exact le hx

/-- Multiplication followed by the Frobenius functional on one complementary pair. -/
def gradedPairing (d k : ℕ) :
    piece K C d k →ₗ[K] Module.Dual K (piece K C d (d-k)) :=
  (piece K C d (d-k)).dualRestrict.comp ((pairing K (Ring K C)).comp (piece K C d k).subtype)

private theorem gradedPairing_injective (d k : ℕ) (bound : ∀ s : Face C, s.val.card≤d) :
    Function.Injective (gradedPairing K C d k) := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  apply pairing_injective K (Ring K C)
  rw [Submodule.coe_zero,map_zero]
  apply (idealBasis K C).ext
  intro i
  obtain ⟨l,hi⟩ : ∃ l, HasDegree C d l i := by
    cases i with
    | inl s => exact ⟨s.val.card,rfl⟩
    | inr s => exact ⟨d-s.val.card,by change s.val.card+(d-s.val.card)=d; have := bound s; omega⟩
  have hm := basis_mem_piece K C hi
  by_cases hk : k+l=d
  · have hl : l=d-k := by omega
    subst l
    exact LinearMap.congr_fun hx ⟨idealBasis K C i,hm⟩
  · exact trace_zero_other_degree K C hk (mul_mem K C x.property hm)

/-- The ordinary graded Gorenstein duality, constructed from multiplication in
the ring, as a linear equivalence of complementary graded pieces. -/
def perfectGradedPairing (d k : ℕ) (hk : k≤d) (bound : ∀ s : Face C, s.val.card≤d) :
    piece K C d k ≃ₗ[K] Module.Dual K (piece K C d (d-k)) := by
  have dimEq : Module.finrank K (piece K C d k) =
      Module.finrank K (Module.Dual K (piece K C d (d-k))) := by
    rw [Subspace.dual_finrank_eq,finrank_piece,finrank_piece,if_pos hk,
      if_pos (Nat.sub_le _ _),Nat.sub_sub_self hk,add_comm]
  have h := gradedPairing_injective K C d k bound
  exact LinearEquiv.ofBijective (gradedPairing K C d k)
    ⟨h,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dimEq).mp h⟩

theorem perfectGradedPairing_apply (d k : ℕ) (hk : k≤d) (bound : ∀ s : Face C, s.val.card≤d)
    (x : piece K C d k) (y : piece K C d (d-k)) :
    perfectGradedPairing K C d k hk bound x y = trace K _ (x.val*y.val) := rfl

end RollerIdealGrading
