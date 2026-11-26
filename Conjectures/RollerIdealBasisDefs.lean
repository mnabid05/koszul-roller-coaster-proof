import Conjectures.RollerFaceRingGrading
import Conjectures.RollerGorenstein
import Mathlib.LinearAlgebra.Basis.Prod

/-! Face monomials and their dual basis vectors in the idealization. -/
noncomputable section
namespace RollerIdealGrading

open RollerFaceRing RollerGorenstein
open scoped Classical

variable {V : Type*} [Fintype V] (K : Type*) [Field K] (C : Complex V)

abbrev A := Idealization K (Ring K C)

/-- A face on the algebra side of the idealization. -/
def primal (s : Face C) : A K C := (faceMonomial K C s,0)

/-- The coordinate functional supported at a single face, on the dual side. -/
def dual (s : Face C) : A K C := (0,(basis K C).coord s)

/-- Basis of the idealization consisting of the face monomials and their coordinate duals. -/
def idealBasis : Basis (Face C ⊕ Face C) K (A K C) :=
  ((basis K C).prod (basis K C).dualBasis).map (RollerGorenstein.coordinates K _).symm

@[simp] theorem idealBasis_inl (s : Face C) : idealBasis K C (.inl s) = primal K C s := by
  unfold idealBasis primal
  rw [Basis.map_apply]
  change (basis K C).prod (basis K C).dualBasis (.inl s) = _
  apply Prod.ext
  · rw [Basis.prod_apply_inl_fst,basis_apply]
  · exact Basis.prod_apply_inl_snd _ _ _

@[simp] theorem idealBasis_inr (s : Face C) : idealBasis K C (.inr s) = dual K C s := by
  unfold idealBasis dual
  rw [Basis.map_apply]
  change (basis K C).prod (basis K C).dualBasis (.inr s) = _
  apply Prod.ext
  · exact Basis.prod_apply_inr_fst _ _ _
  · rw [Basis.prod_apply_inr_snd,Basis.coe_dualBasis]

end RollerIdealGrading
