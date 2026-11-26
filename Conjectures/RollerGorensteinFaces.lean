import Conjectures.RollerFaceRingGrading
import Conjectures.RollerGorensteinSocle

/-! The Artinian Gorenstein property of the finite face-algebra idealizations. -/
namespace RollerGorenstein

noncomputable section

variable (K : Type*) [Field K] {V : Type*} [Fintype V] (C : RollerFaceRing.Complex V)

instance : IsLocalRing (RollerFaceRing.Ring K C) := by
  have hn : Nontrivial (RollerFaceRing.Ring K C) :=
    (RollerFaceRing.augmentation K C).toRingHom.domain_nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  by_cases h : RollerFaceRing.augmentation K C x = 0
  · exact Or.inr ((RollerFaceRing.isUnit_iff_augmentation_ne_zero K C _).2 (by simp [h]))
  · exact Or.inl ((RollerFaceRing.isUnit_iff_augmentation_ne_zero K C _).2 h)

/-- The actual squarefree face-algebra idealization is an Artinian local K-algebra
with residue K and a one-dimensional socle. -/
theorem face_artinian_gorenstein :
    let A := Idealization K (RollerFaceRing.Ring K C)
    IsArtinianRing A ∧ IsLocalRing A ∧
      Nonempty ((A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[K] K) ∧
      Module.finrank K ((IsLocalRing.maximalIdeal A).annihilator.restrictScalars K) = 1 :=
  ⟨inferInstance,inferInstance,⟨residueEquiv (RollerFaceRing.augmentation K C)⟩,
    finrank_socle (RollerFaceRing.augmentation K C)⟩

end
end RollerGorenstein
