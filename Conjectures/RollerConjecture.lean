import Conjectures.RollerKoszulAugmentation
import Conjectures.RollerWhiskeredKoszul

/-! Holleben–Nicklasson, Conjecture 5.8. This version works over every field
and for every socle degree at least three. Hilbert entries below are dimensions
of the indicated subspaces of the same algebra whose bar cohomology is diagonal. -/
noncomputable section
namespace KoszulRollerCoaster
universe u
variable (K : Type u) [Field K]

/-- Standard graded Artinian Gorenstein with residue field K and socle degree d.
The socle is the annihilator of the maximal ideal and is exactly one-dimensional. -/
structure StandardGradedGorenstein (A : Type u) [CommRing A] [Algebra K A] [IsLocalRing A]
    (pieces : ℕ → Submodule K A) (d : ℕ) : Prop where
  artinian : IsArtinianRing A
  residue : Nonempty ((A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[K] K)
  graded : Nonempty (GradedAlgebra pieces)
  connected : pieces 0 = Submodule.span K {1}
  standard : Algebra.adjoin K (pieces 1 : Set A) = ⊤
  socle : pieces d = (IsLocalRing.maximalIdeal A).annihilator.restrictScalars K
  top_dimension : Module.finrank K (pieces d) = 1
  finite : Module.Finite K A
  above : ∀ k, d<k → pieces k = ⊥

/-- Every permutation of the first half of the Hilbert function occurs for a
Koszul standard graded Artinian Gorenstein algebra over the given field. -/
theorem conjecture_5_8 (d : ℕ) (hd : 3 ≤ d) (π : Equiv.Perm (Fin (d/2))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A) (_ : IsLocalRing A)
      (pieces : ℕ → Submodule K A),
      StandardGradedGorenstein K A pieces d ∧ RollerKoszul.IsKoszulAlgebra K A pieces ∧
      StrictMono (fun i : Fin (d/2) => Module.finrank K (pieces ((π i).val+1))) := by
  obtain ⟨bs,h,H,horder⟩ := RollerAlgebraRealization.every_order K d hd π
  have he : d-1+1=d := by omega
  refine ⟨RollerAlgebraRealization.algebra K h,inferInstance,inferInstance,H.localRing,
    RollerAlgebraRealization.homogeneous K h,?_,
    RollerAlgebraRealization.isKoszulAlgebra_of_bar K h (RollerFiltration.whiskered_koszul h K),horder⟩
  have hdim := congrArg (fun k => Module.finrank K (RollerAlgebraRealization.homogeneous K h k)) he.symm
  exact ⟨H.artinian, H.residue, H.graded, H.connected, H.standard,
    by simpa only [he] using H.socle, hdim.trans H.top_dimension, inferInstance,
    by simpa only [he] using H.above⟩

end KoszulRollerCoaster
