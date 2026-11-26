import Conjectures.RollerCoaster

/-! A face after colored whiskering consists of the old face and a subset of its
unused colors. We encode this subset by the colors that remain unoccupied.
The empty old face is a separate summand, so it is counted once. -/
namespace RollerCoaster

open Finset RollerRealization
open scoped Classical

private def colors {p s : ℕ} : (bs : List Block) → (∀ b ∈ bs, Admissible p b) →
    LocatedFace s bs → Finset (Fin p)
  | [], _, x => nomatch x
  | b :: bs, h, .inl (_, f) =>
    (f.val.image Prod.fst).map
      ⟨Fin.castLE (h b (by simp)).2.2.1, fun _ _ e => Fin.ext (congrArg (fun a : Fin p => a.val) e)⟩
  | b :: bs, h, .inr f => colors bs (fun x hx => h x (List.mem_cons_of_mem b hx)) f

private theorem colors_card {p s : ℕ} (bs : List Block) (h : ∀ b ∈ bs, Admissible p b)
    (f : LocatedFace s bs) : (colors bs h f).card = s := by
  induction bs with
  | nil => exact False.elim (nomatch f)
  | cons b bs ih =>
    rcases f with ⟨_,f⟩ | f
    · simpa [colors, Finset.card_image_of_injOn f.property.2] using f.property.1
    · exact ih _ f

private def unused {p s : ℕ} (bs : List Block) (h : ∀ b ∈ bs, Admissible p b)
    (f : LocatedFace s bs) := (univ : Finset (Fin p)) \ colors bs h f

private theorem unused_card {p s : ℕ} (bs : List Block) (h : ∀ b ∈ bs, Admissible p b)
    (f : LocatedFace s bs) : (unused bs h f).card = p-s := by
  simp [unused, card_sdiff (subset_univ _), colors_card]

abbrev Selection (V : Type) (k : ℕ) := {u : Finset V // u.card = k}

/-- k-faces of the colored whiskering, with vertices selected in a named component
and additional leaves chosen from precisely the old face's unused color classes. -/
def ColoredFace (p : ℕ) (bs : List Block) (h : ∀ b ∈ bs, Admissible p b) (k : ℕ) : Type :=
  if k≤p then Selection (Fin p) k ⊕
      (Σ i : Fin p, Σ f : LocatedFace (p-i) bs, Selection (unused bs h f) (p-k))
  else Empty

noncomputable instance coloredFintype (p : ℕ) (bs : List Block) (h : ∀ b ∈ bs, Admissible p b)
    (k : ℕ) : Fintype (ColoredFace p bs h k) := by
  unfold ColoredFace
  split <;> infer_instance

theorem card_coloredFace (p : ℕ) (bs : List Block) (h : ∀ b ∈ bs, Admissible p b)
    (k : ℕ) : Fintype.card (ColoredFace p bs h k) = whiskeredFaces p bs k := by
  classical
  by_cases hk : k≤p
  · rw [whiskeredFaces, if_pos hk]
    let E : ColoredFace p bs h k ≃ Selection (Fin p) k ⊕
        (Σ i : Fin p, Σ f : LocatedFace (p-i) bs, Selection (unused bs h f) (p-k)) :=
      Equiv.cast (if_pos (α := Type) hk)
    rw [Fintype.card_congr E, Fintype.card_sum]
    simp only [Selection, Fintype.card_finset_len, Fintype.card_fin, Fintype.card_sigma,
      Fintype.card_coe, unused_card]
    rw [Finset.sum_range]
    congr 1
    apply sum_congr rfl
    intro i _
    simp [show p-(p-i.val)=i.val by have := i.isLt; omega, card_locatedFace]
  · let E : ColoredFace p bs h k ≃ Empty := Equiv.cast (if_neg (α := Type) hk)
    rw [whiskeredFaces, if_neg hk, Fintype.card_congr E, Fintype.card_empty]

/-- The two classes of basis elements appearing in the published Artinian reduction. -/
abbrev BasisIndex (p : ℕ) (bs : List Block) (h : ∀ b ∈ bs, Admissible p b) (k : ℕ) :=
  ColoredFace p bs h k ⊕ ColoredFace p bs h (p+1-k)

/-- Every ordering of the first half of the symmetric face counts, with each
count given as the cardinality of explicit finite sets of faces. -/
theorem every_order_of_faces (d : ℕ) (hd : 3≤d) (π : Equiv.Perm (Fin (d/2))) :
    ∃ (bs : List Block) (h : ∀ b ∈ bs, Admissible (d-1) b),
      StrictMono (fun k : Fin (d/2) =>
        Fintype.card (BasisIndex (d-1) bs h ((π k).val+1))) := by
  obtain ⟨bs,h,ho⟩ := every_order d hd π
  exact ⟨bs,h,by simpa only [BasisIndex, Fintype.card_sum, card_coloredFace, hilbert] using ho⟩

end RollerCoaster
