import Conjectures.RollerIdealBasisDefs
import Mathlib.RingTheory.GradedAlgebra.Basic

/-! Additive homogeneous pieces of the shifted idealization and their dimensions. -/
noncomputable section
open scoped Classical BigOperators
namespace RollerIdealGrading

open RollerFaceRing
variable {V : Type*} [Fintype V] (K : Type*) [Field K] (C : Complex V)

/-- Degree k on the dual side means face size + k = d. This equality also
specifies the zero dual component above the shift d. -/
def HasDegree (d k : ℕ) : Face C ⊕ Face C → Prop
  | .inl s => s.val.card=k
  | .inr s => s.val.card+k=d

def piece (d k : ℕ) : Submodule K (A K C) :=
  Submodule.span K ((idealBasis K C) '' {i | HasDegree C d k i})

theorem basis_mem_piece {d k : ℕ} {i : Face C ⊕ Face C} (h : HasDegree C d k i) :
    idealBasis K C i ∈ piece K C d k := Submodule.subset_span ⟨i,h,rfl⟩

theorem primal_mem (d : ℕ) (s : Face C) : primal K C s ∈ piece K C d s.val.card := by
  simpa using (basis_mem_piece K C (i:=.inl s) (d:=d) (k:=s.val.card) rfl)

theorem dual_mem {d k : ℕ} (s : Face C) (h : s.val.card+k=d) :
    dual K C s ∈ piece K C d k := by
  simpa using (basis_mem_piece K C (i:=.inr s) (d:=d) (k:=k) h)

omit [Fintype V] in
private theorem unique_degree {d k l : ℕ} {i : Face C ⊕ Face C}
    (hk : HasDegree C d k i) (hl : HasDegree C d l i) : k=l := by
  cases i with
  | inl s => exact hk.symm.trans hl
  | inr s => exact Nat.add_left_cancel (hk.trans hl.symm)

theorem isInternal (d : ℕ) (bound : ∀ s : Face C, s.val.card≤d) :
    DirectSum.IsInternal (piece K C d) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro k
    let T := {i : Face C ⊕ Face C | ¬HasDegree C d k i}
    have dis := (idealBasis K C).linearIndependent.disjoint_span_image
      (s:={i | HasDegree C d k i}) (t:=T) (Set.disjoint_right.mpr (fun _ hn hp => hn hp))
    refine dis.mono_right (iSup_le fun j => iSup_le fun h => ?_)
    apply Submodule.span_mono
    apply Set.image_mono
    intro i hi hn
    exact h (unique_degree C hi hn)
  · apply top_unique
    rw [← (idealBasis K C).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    obtain ⟨k,hk⟩ : ∃ k, HasDegree C d k i := by
      cases i with
      | inl s => exact ⟨s.val.card,rfl⟩
      | inr s => exact ⟨d-s.val.card, by change s.val.card+(d-s.val.card)=d; have := bound s; omega⟩
    exact (le_iSup (piece K C d) k) (basis_mem_piece K C hk)

private def fiberEquiv (d k : ℕ) :
    {i // HasDegree C d k i} ≃ FaceAt C k ⊕ {s : Face C // s.val.card+k=d} where
  toFun
    | ⟨.inl s,h⟩ => .inl ⟨s.val,s.property,h⟩
    | ⟨.inr s,h⟩ => .inr ⟨s,h⟩
  invFun
    | .inl s => ⟨.inl ⟨s.val,s.property.1⟩,s.property.2⟩
    | .inr s => ⟨.inr s.val,s.property⟩
  left_inv := by rintro ⟨i,h⟩; cases i <;> rfl
  right_inv := by rintro (s|s) <;> rfl

private def dualFiberEquiv {d k : ℕ} (h : k≤d) :
    {s : Face C // s.val.card+k=d} ≃ FaceAt C (d-k) where
  toFun s := ⟨s.val.val,s.val.property,by have := s.property; omega⟩
  invFun s := ⟨⟨s.val,s.property.1⟩,by change s.val.card+k=d; have := s.property.2; omega⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The Hilbert function of the shifted idealization in every degree, including
the zero dual contribution for degrees above d. -/
theorem finrank_piece (d k : ℕ) :
    Module.finrank K (piece K C d k) =
      Fintype.card (FaceAt C k) +
       (if k≤d then Fintype.card (FaceAt C (d-k)) else 0) := by
  let S := {i : Face C ⊕ Face C | HasDegree C d k i}
  have he : Set.range (fun i : S => idealBasis K C i.val) = (idealBasis K C) '' S := by
    ext x; constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  unfold piece
  rw [← he,finrank_span_eq_card (b:=fun i : S => idealBasis K C i.val) ((idealBasis K C).linearIndependent.comp _ Subtype.val_injective)]
  calc
    Fintype.card S = Fintype.card (FaceAt C k ⊕ {s : Face C // s.val.card+k=d}) :=
      Fintype.card_congr (fiberEquiv C d k)
    _ = _ := ?_
  rw [Fintype.card_sum]
  congr 1
  split
  · exact Fintype.card_congr (dualFiberEquiv C ‹_›)
  · haveI : IsEmpty {s : Face C // s.val.card+k=d} := ⟨fun s => by have := s.property; omega⟩
    exact Fintype.card_of_isEmpty

theorem piece_eq_bot_of_gt {d k : ℕ} (hk : d<k) (bound : ∀ s : Face C, s.val.card≤d) :
    piece K C d k=⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,hi,rfl⟩
  cases i with
  | inl s => change s.val.card=k at hi; have := bound s; omega
  | inr s => change s.val.card+k=d at hi; omega

end RollerIdealGrading
