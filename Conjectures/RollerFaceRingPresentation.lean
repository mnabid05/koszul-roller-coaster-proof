import Conjectures.RollerFaceRing
import Conjectures.RollerShelling

/-! Polynomial presentations by vertex squares and squarefree nonfaces. A flag
complex on its actual vertex set has a quadratic monomial presentation. -/

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace RollerFaceRing
variable {V : Type*} (K : Type*) [Field K] (C : Complex V)

theorem squarefree_monomial (s : Finset V) :
    (monomial (exponent s) 1 : MvPolynomial V K) = ∏ a ∈ s, X a := by
  rw [← prod_X_pow_eq_monomial, support_exponent]
  apply Finset.prod_congr rfl
  intro a ha
  simp [ha]

private def badGenerators (Q : Finset V → Prop) : Set (V →₀ ℕ) :=
  {e | (∃ v, e = Finsupp.single v 2) ∨ ∃ s, Q s ∧ e = exponent s}

private theorem exponent_le_iff (s : Finset V) (e : V →₀ ℕ) :
    exponent s ≤ e ↔ s ⊆ e.support := by
  constructor
  · intro h v hv
    have hh := h v
    rw [exponent_apply, if_pos hv] at hh
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h v
    by_cases hv : v ∈ s
    · have := Finsupp.mem_support_iff.mp (h hv)
      simp [hv]; omega
    · simp [hv]

/-- Any family of forbidden sets that detects nonfaces gives the same quotient. -/
theorem presentation_of_forbidden (Q : Finset V → Prop)
    (hQ : ∀ s, ¬ C.face s ↔ ∃ t ⊆ s, Q t) :
    definingIdeal K C = Ideal.span ({p | (∃ v : V, p = X v ^ 2) ∨
      ∃ t : Finset V, Q t ∧ p = ∏ a ∈ t, X a} : Set (MvPolynomial V K)) := by
  have detect (e : V →₀ ℕ) : (∃ f ∈ badGenerators Q, f ≤ e) ↔ ¬Standard C e := by
    constructor
    · rintro ⟨_, (⟨v,rfl⟩ | ⟨t,ht,rfl⟩), hle⟩ he
      · have hs := he.1 v
        have := Finsupp.single_le_iff.mp hle
        omega
      · exact ((hQ _).mpr ⟨_, (exponent_le_iff ..).mp hle, ht⟩) he.2
    · intro hn
      by_cases hs : ∀ v, e v ≤ 1
      · have hf : ¬ C.face e.support := fun hh => hn ⟨hs,hh⟩
        obtain ⟨t,ht,hQ⟩ := (hQ _).mp hf
        exact ⟨_, Or.inr ⟨t,hQ,rfl⟩, (exponent_le_iff ..).mpr ht⟩
      · push_neg at hs
        obtain ⟨v,hv⟩ := hs
        exact ⟨_, Or.inl ⟨v,rfl⟩, Finsupp.single_le_iff.mpr hv⟩
  have img : ((fun e => monomial e (1 : K)) '' badGenerators Q) =
      ({p | (∃ v : V, p = X v ^ 2) ∨ ∃ t : Finset V, Q t ∧ p = ∏ a ∈ t, X a} :
        Set (MvPolynomial V K)) := by
    ext p
    constructor
    · rintro ⟨_,(⟨v,rfl⟩ | ⟨t,ht,rfl⟩),rfl⟩
      · exact Or.inl ⟨v, by simp [X_pow_eq_monomial]⟩
      · exact Or.inr ⟨t,ht,squarefree_monomial K t⟩
    · rintro (⟨v,rfl⟩ | ⟨t,ht,rfl⟩)
      · exact ⟨_,Or.inl ⟨v,rfl⟩,by simp [X_pow_eq_monomial]⟩
      · exact ⟨_, Or.inr ⟨t,ht,rfl⟩,squarefree_monomial K t⟩
  ext p
  rw [← img, mem_ideal_span_monomial_image, mem_definingIdeal_iff]
  constructor
  · intro h e he
    exact (detect e).mpr fun hs => (mem_support_iff.mp he) (h e hs)
  · intro h e he
    by_contra hn
    exact (detect e).mp (h e (mem_support_iff.mpr hn)) he

theorem presentation_nonfaces :
    definingIdeal K C = Ideal.span ({p | (∃ v : V, p = X v ^ 2) ∨
      ∃ t : Finset V, ¬ C.face t ∧ p = ∏ a ∈ t, X a} : Set (MvPolynomial V K)) := by
  apply presentation_of_forbidden
  intro s
  exact ⟨fun h => ⟨s,Finset.Subset.rfl,h⟩, fun ⟨_,h,hn⟩ hs => hn (C.downward h hs)⟩

theorem presentation_flag (hflag : RollerShelling.Flag C.face) (hv : ∀ v : V, C.face {v}) :
    definingIdeal K C = Ideal.span ({p | (∃ v : V, p = X v ^ 2) ∨
      ∃ a b : V, a ≠ b ∧ ¬ C.face {a,b} ∧ p = X a * X b} : Set (MvPolynomial V K)) := by
  let Q (s : Finset V) := s.card = 2 ∧ ¬ C.face s
  have hQ (s : Finset V) : ¬ C.face s ↔ ∃ t ⊆ s, Q t := by
    constructor
    · intro h
      by_contra! hn
      apply h (hflag s ?_)
      intro t ht hc
      by_cases h0 : t.card = 0
      · simp only [Finset.card_eq_zero] at h0
        simpa [h0] using C.empty
      by_cases h1 : t.card = 1
      · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h1
        exact hv a
      by_contra hf
      exact hn t ht ⟨by omega,hf⟩
    · rintro ⟨t,ht,hq⟩ hs
      exact hq.2 (C.downward ht hs)
  rw [presentation_of_forbidden K C Q hQ]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro (h | ⟨t,⟨hc,hn⟩,rfl⟩)
    · exact Or.inl h
    · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
      exact Or.inr ⟨a,b,hab,hn,by simp [hab]⟩
  · rintro (h | ⟨a,b,h,hn,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨{a,b},⟨by simp [h],hn⟩,by simp [h]⟩

end RollerFaceRing
