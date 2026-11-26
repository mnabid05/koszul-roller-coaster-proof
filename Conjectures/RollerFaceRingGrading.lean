import Conjectures.RollerFaceRing
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The homogeneous pieces of the polynomial quotient, its residue map, and
nilpotence of each element of the augmentation ideal. -/

noncomputable section
open scoped BigOperators Classical
open MvPolynomial

namespace RollerFaceRing

variable {V : Type*} (K : Type*) [Field K] (C : Complex V)

def augmentation : Ring K C →ₐ[K] K :=
  Ideal.Quotient.liftₐ (definingIdeal K C)
    { MvPolynomial.constantCoeff with commutes' := MvPolynomial.constantCoeff_C V } (by
      intro p hp
      apply (mem_definingIdeal_iff K C p).mp hp 0
      exact ⟨by simp, by simpa using C.empty⟩)

@[simp] theorem augmentation_mk (p : MvPolynomial V K) :
    augmentation K C (Ideal.Quotient.mk _ p) = coeff 0 p := rfl

variable [Fintype V]

instance finiteRing : Module.Finite K (Ring K C) := Module.Finite.of_basis (basis K C)

@[simp] theorem basis_repr_apply (x : Ring K C) (s : Face C) :
    (basis K C).repr x s = coordinates K C x s := by simp [basis]

theorem sum_coordinates (x : Ring K C) :
    ∑ s : Face C, coordinates K C x s • faceMonomial K C s = x := by
  simpa only [basis_apply, basis_repr_apply] using (basis K C).sum_repr x

theorem mem_piece_iff (k : ℕ) (x : Ring K C) :
    x ∈ piece K C k ↔ ∀ s : Face C, s.val.card ≠ k → coordinates K C x s = 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩ s hs
    rw [show (Ideal.Quotient.mkₐ K (definingIdeal K C)).toLinearMap p =
      Ideal.Quotient.mk _ p from rfl, coordinates_mk]
    exact (show p.IsHomogeneous k from hp).coeff_eq_zero (by simpa using hs)
  · intro h
    rw [← sum_coordinates K C x]
    apply Submodule.sum_mem
    intro s _
    by_cases hs : s.val.card = k
    · rw [← hs]
      exact Submodule.smul_mem _ _ (mem_piece_faceMonomial K C s)
    · simp [h s hs]

def pieceCoordinates (k : ℕ) : piece K C k ≃ₗ[K] (FaceAt C k → K) := by
  let forget (s : FaceAt C k) : Face C := ⟨s.val,s.property.1⟩
  let res : piece K C k →ₗ[K] (FaceAt C k → K) :=
    { toFun := fun x s => coordinates K C x.val (forget s)
      map_add' := fun x y => by funext s; simp
      map_smul' := fun a x => by funext s; simp }
  apply LinearEquiv.ofBijective res
  constructor
  · intro x y h
    apply Subtype.ext
    apply (coordinates K C).injective
    funext s
    by_cases hs : s.val.card = k
    · exact congrFun h (⟨s.val,s.property,hs⟩ : FaceAt C k)
    · rw [(mem_piece_iff K C k x.val).mp x.property s hs,
          (mem_piece_iff K C k y.val).mp y.property s hs]
  · intro f
    let g (s : Face C) := if h : s.val.card = k then f ⟨s.val,s.property,h⟩ else 0
    let x := (coordinates K C).symm g
    have hx : x ∈ piece K C k := by
      apply (mem_piece_iff K C k x).mpr
      intro s hs
      simp [x,g,hs]
    refine ⟨⟨x,hx⟩, ?_⟩
    funext s
    change coordinates K C ((coordinates K C).symm g) (forget s) = f s
    simp [g,forget,s.property.2]

@[simp] theorem finrank_piece (k : ℕ) :
    Module.finrank K (piece K C k) = Fintype.card (FaceAt C k) := by
  rw [(pieceCoordinates K C k).finrank_eq]
  exact Module.finrank_eq_card_basis (Pi.basisFun K (FaceAt C k))

theorem augmentation_eq_coordinates (x : Ring K C) :
    augmentation K C x = coordinates K C x (emptyFace C) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [coordinates_mk, augmentation_mk]
  have he : exponent (∅ : Finset V) = 0 := by ext v; simp
  simp [emptyFace,he]

theorem nilpotent_of_augmentation_zero (x : Ring K C) (hx : augmentation K C x = 0) :
    IsNilpotent x := by
  rw [← sum_coordinates K C x]
  apply isNilpotent_sum
  intro s _
  by_cases hs : s = emptyFace C
  · subst s
    rw [← augmentation_eq_coordinates, hx, zero_smul]
    exact IsNilpotent.zero
  · apply IsNilpotent.smul
    refine ⟨2, ?_⟩
    rw [pow_two, faceMonomial_mul, dif_neg]
    rintro ⟨hd,_⟩
    have hh : s.val = ∅ := disjoint_self.mp hd
    exact hs (Subtype.ext hh)

theorem isUnit_iff_augmentation_ne_zero (x : Ring K C) :
    IsUnit x ↔ augmentation K C x ≠ 0 := by
  constructor
  · intro h
    exact (h.map (augmentation K C).toMonoidHom).ne_zero
  · intro h
    let u := algebraMap K (Ring K C) (augmentation K C x)
    have hu : IsUnit u := (isUnit_iff_ne_zero.mpr h).map _
    have hn : IsNilpotent (x-u) := nilpotent_of_augmentation_zero K C _ (by simp [u])
    simpa only [sub_add_cancel] using hn.isUnit_add_right_of_commute hu (Commute.all _ _)

end RollerFaceRing
