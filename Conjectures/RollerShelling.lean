import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Powerset

/-! The facet order and two-vertex nonface test for colored whiskering (Biermann–Van Tuyl).
The shelling witness uses the old vertex that distinguishes the later facet. -/

namespace RollerShelling

variable {V C : Type*} [DecidableEq V] [DecidableEq C] [Fintype C]
variable (color : V → C) (Old : Finset V → Prop)

/-- An old face, extended by one new vertex in each unused color. -/
def completion (s : Finset V) : Finset (V ⊕ C) := s.disjSum (s.image color)ᶜ

/-- A collection of old and new vertices is a face precisely when its old vertices are a face
and the new vertices have colors unused by that face. -/
def Face (u : Finset (V ⊕ C)) : Prop :=
  Old u.toLeft ∧ ∀ i ∈ u.toRight, i ∉ u.toLeft.image color

def Facet (u : Finset (V ⊕ C)) : Prop :=
  Face color Old u ∧ ∀ v, Face color Old v → u ⊆ v → v = u

def Downward (P : Finset V → Prop) : Prop := ∀ ⦃s t⦄, s ⊆ t → P t → P s

/-- The usual two-vertex test for a flag simplicial complex. -/
def Flag {A : Type*} (P : Finset A → Prop) : Prop :=
  ∀ s, (∀ t ⊆ s, t.card ≤ 2 → P t) → P s

omit [DecidableEq V] in
@[simp] theorem old_completion (s : Finset V) : (completion color s).toLeft = s := by
  simp [completion]

omit [DecidableEq V] in
@[simp] theorem new_completion (s : Finset V) : (completion color s).toRight = (s.image color)ᶜ := by
  simp [completion]

omit [DecidableEq V] [Fintype C] in
theorem face_downward (hd : Downward Old) : Downward (Face color Old) := by
  rintro s t hs ⟨ho, hc⟩
  have hl := Finset.toLeft_subset_toLeft hs
  exact ⟨hd hl ho, fun i hi him => hc i (Finset.toRight_subset_toRight hs hi) (Finset.image_subset_image hl him)⟩

omit [DecidableEq V] in
theorem face_iff_subset_completion (hd : Downward Old) (u : Finset (V ⊕ C)) :
    Face color Old u ↔ ∃ s, Old s ∧ u ⊆ completion color s := by
  constructor
  · rintro ⟨ho,hc⟩
    exact ⟨u.toLeft,ho,Finset.subset_disjSum.mpr ⟨Finset.Subset.rfl,
      fun _ h => Finset.mem_compl.mpr (hc _ h)⟩⟩
  · rintro ⟨s,ho,h⟩
    apply face_downward color Old hd h
    simp [Face, ho]

omit [DecidableEq V] in
theorem card_completion (s : Finset V) (h : Set.InjOn color (s : Set V)) :
    (completion color s).card = Fintype.card C := by
  rw [completion, Finset.card_disjSum, Finset.card_compl]
  have hi := Finset.card_image_of_injOn h
  have hle := Finset.card_le_univ (s.image color)
  omega

omit [DecidableEq V] in
/-- The completions are exactly the maximal faces. In particular, every facet has one vertex
in each color. -/
theorem facet_iff_completion (hd : Downward Old) (proper : ∀ s, Old s → Set.InjOn color (s : Set V))
    (u : Finset (V ⊕ C)) : Facet color Old u ↔ ∃ s, Old s ∧ u = completion color s := by
  constructor
  · rintro ⟨hf,hm⟩
    obtain ⟨s,hs,hu⟩ := (face_iff_subset_completion color Old hd u).mp hf
    have hsc := (face_iff_subset_completion color Old hd _).mpr ⟨s,hs,Finset.Subset.rfl⟩
    exact ⟨s,hs,(hm _ hsc hu).symm⟩
  · rintro ⟨s,hs,rfl⟩
    refine ⟨(face_iff_subset_completion color Old hd _).mpr ⟨s,hs,Finset.Subset.rfl⟩, ?_⟩
    intro v hv hsub
    obtain ⟨t,ht,hvt⟩ := (face_iff_subset_completion color Old hd v).mp hv
    apply (Finset.eq_of_subset_of_card_le hsub _).symm
    calc
      v.card ≤ (completion color t).card := Finset.card_le_card hvt
      _ = (completion color s).card := (card_completion color t (proper t ht)).trans
        (card_completion color s (proper s hs)).symm

/-- Deleting an old vertex gives a facet meeting the original completion in a ridge. -/
theorem erased_inter (s : Finset V) (v : V) :
    completion color (s.erase v) ∩ completion color s = (completion color s).erase (.inl v) := by
  ext a
  cases a with
  | inl u => simp [completion, and_assoc]
  | inr i =>
    have hsub : (s.erase v).image color ⊆ s.image color := Finset.image_subset_image (Finset.erase_subset _ _)
    simp only [Finset.mem_inter, completion, Finset.inr_mem_disjSum, Finset.mem_compl,
      Finset.mem_erase, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    exact ⟨And.right, fun h => ⟨fun h' => h (hsub h'),h⟩⟩

/-- The shelling criterion for any ordering of the completions that refines increasing old
face size. The auxiliary completion is earlier because its old face is strictly smaller. -/
theorem shelling_witness (hd : Downward Old) {s t : Finset V} (ht : Old t)
    (hst : s ≠ t) (hc : s.card ≤ t.card) :
    ∃ v ∈ t, v ∉ s ∧ Old (t.erase v) ∧ (t.erase v).card < t.card ∧
      completion color s ∩ completion color t ⊆ completion color (t.erase v) ∩ completion color t ∧
      completion color (t.erase v) ∩ completion color t = (completion color t).erase (.inl v) := by
  have hnot : ¬ t ⊆ s := fun h => hst (Finset.eq_of_subset_of_card_le h hc).symm
  obtain ⟨v,hvt,hvs⟩ := Finset.not_subset.mp hnot
  refine ⟨v,hvt,hvs,hd (Finset.erase_subset _ _) ht,Finset.card_erase_lt_of_mem hvt,?_,
    erased_inter color t v⟩
  rw [erased_inter]
  intro a ha
  obtain ⟨has,hat⟩ := Finset.mem_inter.mp ha
  refine Finset.mem_erase.mpr ⟨?_,hat⟩
  rintro rfl
  exact hvs (Finset.inl_mem_disjSum.mp has)

omit [DecidableEq V] [Fintype C] in
theorem face_flag (hf : Flag Old) : Flag (Face color Old) := by
  intro u h
  constructor
  · apply hf
    intro s hs hcard
    let v : Finset (V ⊕ C) := s.disjSum ∅
    have hv : v ⊆ u := Finset.disjSum_subset.mpr ⟨hs,Finset.empty_subset _⟩
    have hface := h v hv (by simpa [v] using hcard)
    simpa only [v, Finset.toLeft_disjSum] using hface.1
  · intro i hi hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
    let w := ({v} : Finset V).disjSum ({color v} : Finset C)
    have hw : w ⊆ u := Finset.disjSum_subset.mpr
      ⟨Finset.singleton_subset_iff.mpr hv,Finset.singleton_subset_iff.mpr hi⟩
    have hh := h w hw (by simp [w])
    have hb := hh.2 (color v) (by simp [w])
    exact hb (by simp [w])

end RollerShelling
