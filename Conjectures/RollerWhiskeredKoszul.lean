import Conjectures.RollerFiltrationVertex
import Conjectures.RollerFiltrationDual
import Conjectures.RollerKoszulFiltration

/-! A Koszul filtration and diagonal bar cohomology for every constructed algebra. -/
noncomputable section
namespace RollerFiltration
open Finset RollerRealization RollerVertices RollerFaceMonoid RollerFaceRing
open scoped Classical
variable {p : ℕ} {bs : List Block} (h : ∀ b∈bs, Admissible p b)

private def descent (I : Set (M h)) (bound : ℕ) :=
  I={0} ∨ ∃ (j k : Stage h) (x : M h),
    measure h j < bound ∧ (grading h).Colon I (ideal h j) (ideal h k) x

private theorem facet_descent (P : Initial h) (m : ℕ) (hm : P.faces.card ≤ m) :
    descent h (facetIdeal h P) m := by
  by_cases hp : P.faces.Nonempty
  · obtain ⟨t,ht,hmax⟩ := P.faces.exists_max_image card hp
    let Q := P.eraseMax t ht hmax
    obtain ⟨x,hx,ha,hc,hinj⟩ := facet_step h P t ht hmax
    refine Or.inr ⟨.facets Q,.vertices (forbidden h t),x,?_,hx,ha,hc,hinj⟩
    change (P.faces.erase t).card < m
    exact (Finset.card_erase_lt_of_mem ht).trans_le hm
  · left
    ext a
    have he := not_nonempty_iff_eq_empty.mp hp
    cases a with
    | killed => exact iff_of_true trivial rfl
    | primal f => exact iff_of_false id (by rintro ⟨⟩)
    | dual f =>
      exact iff_of_false (by change f.val.toLeft∉P.faces; rw [he]; simp) (by rintro ⟨⟩)

private theorem filtration_step (i : Stage h) : descent h (ideal h i) (measure h i) := by
  cases i with
  | facets P => exact facet_descent h P _ (le_refl _)
  | vertices S =>
    by_cases hn : S.Nonempty
    · obtain ⟨v,hv⟩ := hn
      refine Or.inr ⟨.vertices (S.erase v),.vertices (neighborsForbidden h (S.erase v) v),
        varTerm h v,?_,?_,vertex_adds h hv,vertex_colon h (Finset.not_mem_erase v S),
        vertex_cancel h (S.erase v) v⟩
      · change _ + (S.erase v).card < _ + S.card
        exact Nat.add_lt_add_left (Finset.card_erase_lt_of_mem hv) _
      · change ({v} : Finset (W bs p)).card = 1
        exact card_singleton v
    · rw [not_nonempty_iff_eq_empty.mp hn]
      change descent h (vertexIdeal h ∅) _
      rw [vertex_empty]
      exact facet_descent h (full h) _ (by simp [measure])

/-- Off-diagonal cohomology of the normalized bar complex of the residue field
vanishes over every field (indeed the basis computation works for any coefficient group). -/
theorem whiskered_koszul (K : Type*) [AddCommGroup K] : (grading h).IsKoszul K := by
  letI : Nontrivial (M h) := ⟨⟨0,1,fun e => by cases e⟩⟩
  apply (grading h).koszul_of_filtration (ideal h) (measure h) (ideal_closed h)
    (filtration_step h) (.vertices univ)
  rw [residue]
  ext a
  change (a ≠ 1) ↔ a=0 ∨ 0 < (grading h).degree a
  constructor
  · intro hu
    by_cases hz : a=0
    · exact Or.inl hz
    · exact Or.inr (Nat.pos_of_ne_zero (fun hd => hu ((grading h).unit_of_degree_zero a hz hd)))
  · rintro (rfl|hd)
    · exact zero_ne_one
    · rintro rfl
      rw [(grading h).one_degree] at hd
      omega

end RollerFiltration
