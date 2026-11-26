import Conjectures.RollerIdealPieces
import Conjectures.RollerIdealBasis
import Conjectures.RollerGorensteinFaces

/-! The shifted idealization is a graded Artinian Gorenstein algebra, with the
socle in its top degree. -/
noncomputable section
open scoped Classical Pointwise
namespace RollerIdealGrading

open RollerFaceRing RollerGorenstein
variable {V : Type*} [Fintype V] (K : Type*) [Field K] (C : Complex V)

private theorem mixed {d k l : ℕ} (s t : Face C) (hs : s.val.card=k) (ht : t.val.card+l=d) :
    primal K C s * dual K C t ∈ piece K C d (k+l) := by
  rw [primal_mul_dual]
  split
  next h =>
    apply dual_mem
    change (t.val \ s.val).card + (k+l) = d
    rw [Finset.card_sdiff h]
    have := Finset.card_le_card h
    omega
  next => exact Submodule.zero_mem _

private theorem basis_mul_mem {d k l : ℕ} (a b : Face C ⊕ Face C)
    (ha : HasDegree C d k a) (hb : HasDegree C d l b) :
    idealBasis K C a * idealBasis K C b ∈ piece K C d (k+l) := by
  cases a with
  | inl s =>
    cases b with
    | inl t =>
      rw [idealBasis_inl,idealBasis_inl,primal_mul_primal]
      split
      next h =>
        have hh : (s.val ∪ t.val).card=k+l := by
          rw [Finset.card_union_of_disjoint h.1,show s.val.card=k from ha,show t.val.card=l from hb]
        exact hh ▸ primal_mem K C d (⟨s.val ∪ t.val,h.2⟩ : Face C)
      next => exact Submodule.zero_mem _
    | inr t => rw [idealBasis_inl,idealBasis_inr]; exact mixed K C s t ha hb
  | inr s =>
    cases b with
    | inl t => rw [idealBasis_inl,idealBasis_inr,mul_comm,add_comm k l]; exact mixed K C t s hb ha
    | inr t => rw [idealBasis_inr,idealBasis_inr,dual_mul_dual]; exact Submodule.zero_mem _

theorem mul_mem {d k l : ℕ} {x y : A K C} (hx : x∈piece K C d k) (hy : y∈piece K C d l) :
    x*y∈piece K C d (k+l) := by
  apply Submodule.mul_le.mp _ x hx y hy
  unfold piece
  rw [Submodule.span_mul_span,Submodule.span_le]
  rintro _ ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,rfl⟩
  exact basis_mul_mem K C a b ha hb

theorem one_mem (d : ℕ) : (1:A K C) ∈ piece K C d 0 := by
  rw [← primal_empty K C]
  exact primal_mem K C d (emptyFace C)

instance (d : ℕ) : SetLike.GradedMonoid (piece K C d) where
  one_mem := one_mem K C d
  mul_mem := fun _ _ => mul_mem K C

/-- The Lean graded-algebra structure over the complete family of degree pieces. -/
def grading (d : ℕ) (bound : ∀ s : Face C, s.val.card≤d) :
    GradedAlgebra (piece K C d) := (isInternal K C d bound).gradedAlgebra

theorem socleGenerator_eq_dual :
    socleGenerator (RollerFaceRing.augmentation K C) = dual K C (emptyFace C) := by
  apply Prod.ext (by rfl)
  apply LinearMap.ext
  intro b
  exact (RollerFaceRing.augmentation_eq_coordinates K C b).trans
    (basis_repr_apply K C b (emptyFace C)).symm

/-- If the largest primal face has degree strictly smaller than d, the entire
degree-d piece consists of the multiples of the dual empty face. -/
theorem top_piece_eq_span (d : ℕ) (bound : ∀ s : Face C, s.val.card<d) :
    piece K C d d=Submodule.span K {dual K C (emptyFace C)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    cases i with
    | inl s => change s.val.card=d at hi; have := bound s; omega
    | inr s =>
      change s.val.card+d=d at hi
      have hs : s=emptyFace C := Subtype.ext (Finset.card_eq_zero.mp (by omega))
      rw [hs,idealBasis_inr]
      exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_singleton_le_iff_mem]
    exact dual_mem K C _ (by simp [emptyFace])

theorem top_piece_eq_socle (d : ℕ) (bound : ∀ s : Face C, s.val.card<d) :
    piece K C d d = ((IsLocalRing.maximalIdeal (A K C)).annihilator).restrictScalars K := by
  rw [top_piece_eq_span K C d bound,←augmentation_kernel_eq_maximal (RollerFaceRing.augmentation K C),
    augmentation_annihilator,socleGenerator_eq_dual]

theorem degree_zero_eq_span (d : ℕ) (bound : ∀ s : Face C, s.val.card<d) :
    piece K C d 0 = Submodule.span K {(1:A K C)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    cases i with
    | inl s =>
      have h : s=emptyFace C := Subtype.ext (Finset.card_eq_zero.mp hi)
      rw [h,idealBasis_inl,primal_empty]
      exact Submodule.mem_span_singleton_self _
    | inr s => change s.val.card+0=d at hi; have := bound s; omega
  · rw [Submodule.span_singleton_le_iff_mem]; exact one_mem K C d

end RollerIdealGrading
