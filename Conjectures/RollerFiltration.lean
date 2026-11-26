import Conjectures.RollerFiltrationFaces
import Conjectures.RollerFaceMonoidGrading

/-! The monomial ideals in the Koszul filtration of the idealized face algebra. -/
noncomputable section
namespace RollerFiltration
open Finset RollerRealization RollerVertices RollerFaceMonoid RollerFaceRing
open scoped Classical

variable {p : ℕ} {bs : List Block} (h : ∀ b∈bs, Admissible p b)
abbrev M := Term (complex h)
abbrev F := Face (complex h)
def grading := barGrading (complex h) (p+1) (fun f => Nat.lt_succ_of_le (size_bound h f))

inductive Stage where
  | vertices (s : Finset (W bs p)) : Stage
  | facets (P : Initial h) : Stage

def vertexIdeal (S : Finset (W bs p)) : Set (M h)
  | .killed => True
  | .primal f => hits S f.val
  | .dual _ => True

def facetIdeal (P : Initial h) : Set (M h)
  | .killed => True
  | .primal _ => False
  | .dual f => f.val.toLeft∈P.faces

def ideal : Stage h → Set (M h)
  | .vertices S => vertexIdeal h S
  | .facets P => facetIdeal h P

def measure : Stage h → ℕ
  | .vertices S => (full h).faces.card + 1 + S.card
  | .facets P => P.faces.card

theorem vertex_closed (S : Finset (W bs p)) : RollerKoszul.BasisGrading.Closed (vertexIdeal h S) := by
  classical
  letI : DecidableEq (W bs p) := Classical.decEq _
  refine ⟨trivial,?_⟩
  rintro (_|a|a) ha b
  · change (0 : M h)*b∈_; rw [zero_mul]; trivial
  · cases b with
    | killed => change _ * (0 : M h) ∈ _; rw [mul_zero]; trivial
    | primal b =>
      rw [primal_mul_primal]
      split
      · obtain ⟨v,hv,hS⟩ := ha
        refine ⟨v,?_,hS⟩
        exact Finset.mem_union.mpr (Or.inl hv)
      · trivial
    | dual b =>
      rw [primal_mul_dual]
      split <;> trivial
  · cases b with
    | killed => trivial
    | primal b => rw [mul_comm,primal_mul_dual]; split <;> trivial
    | dual b => trivial

theorem facet_closed (P : Initial h) : RollerKoszul.BasisGrading.Closed (facetIdeal h P) := by
  classical
  letI : DecidableEq (W bs p) := Classical.decEq _
  refine ⟨trivial,?_⟩
  rintro (_|a|a) ha b
  · change (0 : M h)*b∈_; rw [zero_mul]; trivial
  · exact False.elim ha
  · cases b with
    | killed => trivial
    | primal b =>
      rw [mul_comm,primal_mul_dual]
      split
      · change (a.val \ b.val).toLeft ∈ P.faces
        apply P.closed _ ha
        intro v hv
        exact mem_toLeft.mpr (mem_sdiff.mp (mem_toLeft.mp hv)).1
      · trivial
    | dual b => trivial

theorem ideal_closed (i : Stage h) : RollerKoszul.BasisGrading.Closed (ideal h i) := by
  classical
  cases i with
  | vertices s => exact vertex_closed h s
  | facets P => exact facet_closed h P

theorem ideal_proper (i : Stage h) : 1∉ideal h i := by
  classical
  cases i with
  | vertices s => change ¬ hits s ∅; simp [hits]
  | facets P => exact id

theorem vertex_empty : vertexIdeal h ∅ = facetIdeal h (full h) := by
  classical
  ext a
  cases a with
  | killed => rfl
  | primal f => change hits ∅ f.val ↔ False; simp [hits]
  | dual f =>
    change True ↔ f.val.toLeft ∈ (full h).faces
    exact iff_of_true trivial (mem_filter.mpr ⟨mem_univ _,f.property.1⟩)

theorem residue : ideal h (.vertices univ) = {a | a ≠ 1} := by
  classical
  ext a
  cases a with
  | killed => exact iff_of_true trivial (by intro e; cases e)
  | dual f => exact iff_of_true trivial (by intro e; cases e)
  | primal f =>
    change hits univ f.val ↔ Term.primal f ≠ Term.primal (emptyFace _)
    simp only [hits,mem_univ,and_true,Term.primal.injEq]
    change f.val.Nonempty ↔ Term.primal f ≠ Term.primal (emptyFace _)
    rw [Finset.nonempty_iff_ne_empty]
    exact not_congr ⟨fun e => congrArg Term.primal (Subtype.ext e),fun e => congrArg Subtype.val (Term.primal.inj e)⟩

end RollerFiltration
