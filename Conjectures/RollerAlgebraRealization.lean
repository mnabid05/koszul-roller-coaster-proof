import Conjectures.RollerComplex
import Conjectures.RollerGorensteinPairing
import Conjectures.RollerFaceRingStandard

/-! Actual graded Artinian Gorenstein algebras realizing every first-half ordering. -/
noncomputable section
namespace RollerAlgebraRealization

open RollerRealization RollerVertices RollerIdealGrading RollerGorenstein
variable (K : Type*) [Field K] {p : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b)

/-- The algebra attached to a finite list of admissible multipartite blocks. -/
abbrev algebra := A K (complex h)

/-- Its homogeneous submodules, with the dual placed in complementary degrees. -/
abbrev homogeneous : ℕ → Submodule K (algebra K h) := piece K (complex h) (p+1)

/-- The ring, grading, and socle properties of this very algebra. -/
structure Properties : Prop where
  artinian : IsArtinianRing (algebra K h)
  localRing : IsLocalRing (algebra K h)
  residue : Nonempty ((algebra K h ⧸ IsLocalRing.maximalIdeal (algebra K h)) ≃ₐ[K] K)
  graded : Nonempty (GradedAlgebra (homogeneous K h))
  connected : homogeneous K h 0 = Submodule.span K {1}
  standard : Algebra.adjoin K (homogeneous K h 1 : Set (algebra K h)) = ⊤
  socle : homogeneous K h (p+1) =
    (IsLocalRing.maximalIdeal (algebra K h)).annihilator.restrictScalars K
  top_dimension : Module.finrank K (homogeneous K h (p+1)) = 1
  perfect : ∀ k, k≤p+1 → Nonempty (homogeneous K h k ≃ₗ[K] Module.Dual K (homogeneous K h (p+1-k)))
  above : ∀ k, p+1<k → homogeneous K h k = ⊥

theorem properties : Properties K h := by
  let ε := RollerFaceRing.augmentation K (complex h)
  have hb (s : RollerFaceRing.Face (complex h)) : s.val.card<p+1 := (size_bound h s).trans_lt (Nat.lt_succ_self _)
  have ht := top_piece_eq_socle K (complex h) (p+1) hb
  exact ⟨inferInstance,inferInstance,⟨residueEquiv ε⟩,
    ⟨grading K (complex h) (p+1) (fun s => (hb s).le)⟩,
    degree_zero_eq_span K (complex h) (p+1) hb,whiskered_standard K h,ht,
    (congrArg (fun S : Submodule K (algebra K h) => Module.finrank K S) ht).trans (finrank_socle ε),
    fun k hk => ⟨perfectGradedPairing K (complex h) (p+1) k hk (fun s => (hb s).le)⟩,
    fun _ hk => piece_eq_bot_of_gt K (complex h) hk (fun s => (hb s).le)⟩

theorem hilbert_value {k : ℕ} (hk : k≤p+1) :
    Module.finrank K (homogeneous K h k) = RollerCoaster.hilbert p bs k := by
  rw [homogeneous,finrank_piece,if_pos hk,card_faceAt,card_faceAt,RollerCoaster.hilbert]

/-- For all fields and every prescribed permutation, the actual Hilbert function
of one graded Artinian Gorenstein algebra obeys the prescribed strict ordering. -/
theorem every_order (d : ℕ) (hd : 3≤d) (π : Equiv.Perm (Fin (d/2))) :
    ∃ (bs : List Block) (h : ∀ b ∈ bs, Admissible (d-1) b),
      Properties K h ∧ StrictMono (fun k : Fin (d/2) =>
        Module.finrank K (homogeneous K h ((π k).val+1))) := by
  obtain ⟨bs,h,hm⟩ := RollerCoaster.every_order d hd π
  refine ⟨bs,h,properties K h,?_⟩
  intro i j hij
  change Module.finrank K (homogeneous K h ((π i).val+1)) <
    Module.finrank K (homogeneous K h ((π j).val+1))
  rw [hilbert_value K h (by have := (π i).isLt; omega),
    hilbert_value K h (by have := (π j).isLt; omega)]
  exact hm hij

end RollerAlgebraRealization
