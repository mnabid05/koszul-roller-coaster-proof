import Conjectures.RollerAlgebraRealization
import Conjectures.RollerFiltration
import Conjectures.RollerKoszulFiltration

/-! A certificate relating diagonal normalized bar cohomology to the algebra
whose graded pieces occur in the Hilbert function. -/
noncomputable section
open scoped Classical

namespace RollerKoszul

variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]
variable (pieces : ℕ → Submodule K A)

/-- A finite multiplicative basis, together with its unit, its augmentation
ideal, the degrees of its vectors, and diagonal exactness of its normalized
bar complex. The basis labels can be chosen independently of the ground field. -/
structure AlgebraBarWitness (S : Type) [MonoidWithZero S] [Fintype S] where
  degree : BasisGrading S
  value : S →*₀ A
  injective : Function.Injective value
  basis : Basis {s : S // s≠0} K A
  basis_apply : ∀ s, basis s=value s.val
  homogeneous : ∀ s, value s∈pieces (degree.degree s)
  graded : Nonempty (GradedAlgebra pieces)
  augmentation : A →ₐ[K] K
  augmentation_kernel : LinearMap.ker augmentation.toLinearMap =
    Submodule.span K (value '' (degree.positive : Set S))
  diagonal : degree.IsKoszul K

/-- Existence of a homogeneous multiplicative basis on which the actual
normalized bar complex has diagonal cohomology. This sufficient certificate
for Koszulness takes only the graded algebra as input. -/
def IsKoszulAlgebra : Prop :=
  ∃ (S : Type) (_ : MonoidWithZero S) (_ : Fintype S),
    Nonempty (AlgebraBarWitness K A pieces S)

namespace AlgebraBarWitness

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {pieces : ℕ → Submodule K A}
variable {S : Type} [MonoidWithZero S] [Fintype S] (W : AlgebraBarWitness K A pieces S)

abbrev PositiveIndex := {s : S // s≠0 ∧ 0<W.degree.degree s}

private theorem positive_independent :
    LinearIndependent K (fun s : W.PositiveIndex => W.value s.val) := by
  let j (s : W.PositiveIndex) : {s : S // s≠0} := ⟨s.val,s.property.1⟩
  have inj : Function.Injective j := fun _ _ h => Subtype.ext (congrArg (fun t : {s : S // s≠0} => t.val) h)
  have hh := W.basis.linearIndependent.comp j inj
  simpa only [Function.comp_def, W.basis_apply,j] using hh

private theorem positive_span :
    Submodule.span K (Set.range (fun s : W.PositiveIndex => W.value s.val)) =
      LinearMap.ker W.augmentation.toLinearMap := by
  rw [W.augmentation_kernel]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨s,rfl⟩
    exact ⟨s.val,Or.inr s.property.2,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨s,hs,rfl⟩
    by_cases hz : s=0
    · subst s; rw [map_zero]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨s,hz,hs.resolve_left hz⟩,rfl⟩

/-- The bar alphabet without the absorbing zero is an actual vector-space
basis of the augmentation ideal. -/
def positiveBasis : Basis W.PositiveIndex K (LinearMap.ker W.augmentation.toLinearMap) :=
  (Basis.span W.positive_independent).map (LinearEquiv.ofEq _ _ W.positive_span)

theorem positiveBasis_apply (s : W.PositiveIndex) :
    ((W.positiveBasis s : LinearMap.ker W.augmentation.toLinearMap) : A) = W.value s.val := by
  rw [positiveBasis,Basis.map_apply,LinearEquiv.coe_ofEq_apply,Basis.span_apply]

end AlgebraBarWitness
end RollerKoszul

namespace RollerAlgebraRealization

open RollerRealization RollerVertices RollerIdealGrading RollerGorenstein RollerFaceMonoid
open RollerFaceRing
variable (K : Type*) [Field K] {p : ℕ} {bs : List Block} (h : ∀ b∈bs,Admissible p b)

private def nonzeroIndex (C : Complex V) : Face C ⊕ Face C ≃ {s : Term C // s≠0} where
  toFun
    | .inl a => ⟨.primal a,fun hh => by cases hh⟩
    | .inr a => ⟨.dual a,fun hh => by cases hh⟩
  invFun
    | ⟨.killed,hn⟩ => False.elim (hn rfl)
    | ⟨.primal a,_⟩ => .inl a
    | ⟨.dual a,_⟩ => .inr a
  left_inv i := by cases i <;> rfl
  right_inv := by rintro ⟨s,hs⟩; cases s with
                  | killed => exact False.elim (hs rfl)
                  | primal _ => rfl
                  | dual _ => rfl

private def barBasis : Basis {s : RollerFiltration.M h // s≠0} K (algebra K h) :=
  (idealBasis K (complex h)).reindex (nonzeroIndex (complex h))

private theorem barBasis_apply (s : {s : RollerFiltration.M h // s≠0}) :
    barBasis K h s = toRing (complex h) K s.val := by
  rw [barBasis,Basis.reindex_apply]
  rcases s with ⟨s,hs⟩
  cases s with
  | killed => exact False.elim (hs rfl)
  | primal t => exact idealBasis_inl K _ t
  | dual t => exact idealBasis_inr K _ t

private theorem value_homogeneous (s : RollerFiltration.M h) :
    toRing (complex h) K s ∈ homogeneous K h ((RollerFiltration.grading h).degree s) := by
  cases s with
  | killed => exact Submodule.zero_mem _
  | primal a => exact primal_mem K _ (p+1) a
  | dual a =>
    apply dual_mem K _ a
    change a.val.card+(p+1-a.val.card)=p+1
    have := size_bound h a
    omega

abbrev residueAugmentation : algebra K h →ₐ[K] K :=
  RollerGorenstein.augmentation (RollerFaceRing.augmentation K (complex h))

private theorem aug_of_positive (s : RollerFiltration.M h)
    (hs : 0<(RollerFiltration.grading h).degree s) : residueAugmentation K h (toRing _ K s)=0 := by
  cases s with
  | killed => rfl
  | dual a => exact map_zero (RollerFaceRing.augmentation K (complex h))
  | primal a =>
    change RollerFaceRing.augmentation K _ (faceMonomial K _ a)=0
    rw [augmentation_eq_coordinates,coordinates_faceMonomial,if_neg]
    intro hh
    subst a
    change 0<(∅ : Finset (ActualVertex bs p)).card at hs
    simp at hs

/-- The bar symbols of positive degree span the kernel of the actual residue
homomorphism on the idealization. -/
theorem bar_augmentation_kernel :
    LinearMap.ker (residueAugmentation K h).toLinearMap = Submodule.span K
      ((toRing (complex h) K) '' ((RollerFiltration.grading h).positive : Set (RollerFiltration.M h))) := by
  classical
  let b := barBasis K h
  let e := toRing (complex h) K
  let g := RollerFiltration.grading h
  let u : {s : RollerFiltration.M h // s≠0} := ⟨1,by intro he; cases he⟩
  have hu : (residueAugmentation K h).toLinearMap = b.coord u := by
    apply b.ext
    intro i
    rw [Basis.coord_apply,b.repr_self]
    rw [show b i=e i.val from barBasis_apply K h i]
    by_cases eq : i=u
    · subst i
      change residueAugmentation K h (e 1)=_
      simp
    · have hn : i.val≠1 := fun t => eq (Subtype.ext t)
      have hp : 0<g.degree i.val := Nat.pos_of_ne_zero (fun hz => hn (g.unit_of_degree_zero _ i.property hz))
      rw [Finsupp.single_apply,if_neg eq]
      exact aug_of_positive K h i.val hp
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker,hu] at hx
    apply (Submodule.span_mono (s:=b '' {i | 0<g.degree i.val}) (t:=e '' (g.positive : Set _)) ?_)
    · apply b.mem_span_image.mpr
      intro i hi
      have hi' := Finsupp.mem_support_iff.mp hi
      have hn : i.val≠1 := by
        intro t
        have he : i=u := Subtype.ext t
        exact hi' (he ▸ hx)
      exact Nat.pos_of_ne_zero (fun hz => hn (g.unit_of_degree_zero _ i.property hz))
    · rintro _ ⟨i,hi,rfl⟩
      exact ⟨i.val,Or.inr hi,(barBasis_apply K h i).symm⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨s,hs,rfl⟩
    rcases hs with rfl|hp
    · simp
    · exact aug_of_positive K h s hp

/-- A result in normalized bar cohomology of the face basis provides the
algebra-level certificate on the same witness used for the Hilbert function. -/
theorem isKoszulAlgebra_of_bar (hk : (RollerFiltration.grading h).IsKoszul K) :
    RollerKoszul.IsKoszulAlgebra K (algebra K h) (homogeneous K h) :=
  ⟨RollerFiltration.M h,inferInstance,inferInstance,
    ⟨{ degree := RollerFiltration.grading h
       value := toRing (complex h) K
       injective := toRing_injective (complex h) K
       basis := barBasis K h
       basis_apply := barBasis_apply K h
       homogeneous := value_homogeneous K h
       graded := (properties K h).graded
       augmentation := residueAugmentation K h
       augmentation_kernel := bar_augmentation_kernel K h
       diagonal := hk }⟩⟩

end RollerAlgebraRealization
