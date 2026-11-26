import Conjectures.RollerComplex
import Mathlib.Data.Finset.Max

/-! The combinatorics of the two kinds of colon ideal in the colored-whiskering
Koszul filtration. Old faces can be removed in any order refining size. -/
noncomputable section
namespace RollerFiltration
open Finset RollerRealization RollerVertices
open scoped Classical

variable {p : ℕ} {bs : List Block} (h : ∀ b∈bs, Admissible p b)
abbrev W (bs : List Block) (p : ℕ) := RollerVertices.ActualVertex bs p

theorem singleton_face (v : W bs p) : (complex h).face {v} := by
  classical
  cases v with
  | inl x =>
    change RollerShelling.Face _ _ _
    simp [RollerShelling.Face,Old]
    intro a ha b hb _
    have ha' : a=x := by simpa using (show Sum.inl a ∈ ({Sum.inl x} : Finset (W bs p)) from Finset.mem_toLeft.mp ha)
    have hb' : b=x := by simpa using (show Sum.inl b ∈ ({Sum.inl x} : Finset (W bs p)) from Finset.mem_toLeft.mp hb)
    exact ha'.trans hb'.symm
  | inr i =>
    change RollerShelling.Face _ _ _
    simp [RollerShelling.Face,Old]
    intro a ha
    simp at ha

theorem face_insert_iff {s : Finset (W bs p)} (hs : (complex h).face s) (v : W bs p) :
    (complex h).face (insert v s) ↔ ∀ w∈s, (complex h).face {v,w} := by
  classical
  constructor
  · intro hf w hw
    exact (complex h).downward (insert_subset (mem_insert_self ..)
      (singleton_subset_iff.mpr (mem_insert_of_mem hw))) hf
  · intro hp
    apply RollerVertices.flag h
    intro t ht hc
    by_cases hv : v∈t
    · have he : (t.erase v).card ≤ 1 := by rw [card_erase_of_mem hv]; omega
      by_cases hn : (t.erase v).Nonempty
      · obtain ⟨w,hw⟩ := hn
        have eq : t.erase v={w} := eq_of_subset_of_card_le (singleton_subset_iff.mpr hw)
          (by simpa using he) |>.symm
        have hwv := mem_erase.mp hw
        have hws := (mem_insert.mp (ht hwv.2)).resolve_left hwv.1
        have ht' := insert_erase hv
        rw [eq] at ht'
        rw [← ht']
        exact hp w hws
      · have ht' := insert_erase hv
        rw [not_nonempty_iff_eq_empty.mp hn] at ht'
        rw [← ht']
        exact singleton_face h v
    · exact (complex h).downward (fun w hw => (mem_insert.mp (ht hw)).resolve_left
          (fun eq => hv (eq ▸ hw))) hs

/-- An initial collection of old faces, closed under passing to subfaces. -/
structure Initial (h : ∀ b∈bs, Admissible p b) where
  faces : Finset (Finset (Vertex bs))
  valid : ∀ t∈faces, Old h t
  closed : ∀ t∈faces, ∀ u⊆t, u∈faces

def full : Initial h where
  faces := Finset.univ.filter (Old h)
  valid := by simp
  closed := by
    intro t ht u hu
    exact Finset.mem_filter.mpr ⟨mem_univ _,old_down h hu (mem_filter.mp ht).2⟩

variable {h}
def Initial.eraseMax (P : Initial h) (t : Finset (Vertex bs))
    (ht : t∈P.faces) (hm : ∀ u∈P.faces, u.card≤t.card) : Initial h where
  faces := P.faces.erase t
  valid := fun u hu => P.valid u (mem_erase.mp hu).2
  closed := by
    intro u hu v hv
    obtain ⟨hne,hmem⟩ := mem_erase.mp hu
    refine mem_erase.mpr ⟨?_, P.closed u hmem v hv⟩
    rintro rfl
    exact hne (eq_of_subset_of_card_le hv (hm u hmem)).symm

/-- At the facet of t, primal multiplication survives modulo the preceding
dual generators only on monomials supported entirely on unused dummy vertices. -/
def forbidden (h : ∀ b∈bs, Admissible p b) (t : Finset (Vertex bs)) : Finset (W bs p) :=
  ((∅ : Finset (Vertex bs)).disjSum (t.image (color h))ᶜ)ᶜ

def hits {V : Type*} (S f : Finset V) : Prop := ∃v∈f, v∈S

theorem hits_forbidden {t : Finset (Vertex bs)} {s : Finset (W bs p)} :
    hits (forbidden h t) s ↔
      ¬s ⊆ RollerShelling.completion (color h) t ∨ s.toLeft.Nonempty := by
  classical
  constructor
  · rintro ⟨v,hv,hb⟩
    by_cases hs : s ⊆ RollerShelling.completion (color h) t
    · right
      cases v with
      | inl x => exact ⟨x,by simpa using hv⟩
      | inr x => exact False.elim ((mem_compl.mp hb)
          (Finset.inr_mem_disjSum.mpr (Finset.inr_mem_disjSum.mp (hs hv))))
    · exact Or.inl hs
  · rintro (hn|⟨x,hx⟩)
    · obtain ⟨v,hv,hb⟩ := Finset.not_subset.mp hn
      refine ⟨v,hv,mem_compl.mpr (fun hm => hb ?_)⟩
      exact disjSum_mono (empty_subset t) (Subset.rfl) hm
    · exact ⟨.inl x,by simpa using hx,by simp [forbidden]⟩

theorem dual_previous_iff (P : Initial h) {t : Finset (Vertex bs)} (ht : t∈P.faces)
    {s : Finset (W bs p)} (hs : s⊆RollerShelling.completion (color h) t) :
    ((RollerShelling.completion (color h) t) \ s).toLeft∈P.faces.erase t ↔
      s.toLeft.Nonempty := by
  classical
  have hst : s.toLeft⊆t := (Finset.subset_disjSum.mp hs).1
  rw [toLeft_sdiff,RollerShelling.old_completion,mem_erase]
  have hvalid := P.closed t ht (t \ s.toLeft) sdiff_subset
  constructor
  · rintro ⟨hn,_⟩
    by_contra h0
    exact hn (by rw [not_nonempty_iff_eq_empty.mp h0,sdiff_empty])
  · rintro ⟨x,hx⟩
    exact ⟨fun eq => (mem_sdiff.mp (show x∈t \ s.toLeft from by rw [eq]; exact hst hx)).2 hx,hvalid⟩

theorem subset_of_own_completion {f : Finset (W bs p)} (hf : (complex h).face f) :
    f ⊆ RollerShelling.completion (color h) f.toLeft :=
  subset_disjSum.mpr ⟨Subset.rfl,fun i hi => mem_compl.mpr (hf.2 i hi)⟩

theorem completion_face {t : Finset (Vertex bs)} (ht : Old h t) :
    (complex h).face (RollerShelling.completion (color h) t) := by
  change RollerShelling.Face _ _ _
  simp [RollerShelling.Face,ht]

/-- The primal colon consists of variables already in S, the generator v, and
all vertices incompatible with v. -/
def neighborsForbidden (h : ∀ b∈bs, Admissible p b) (S : Finset (W bs p))
    (v : W bs p) : Finset (W bs p) :=
  Finset.univ.filter (fun w => w∈S ∨ w=v ∨ ¬(complex h).face {v,w})

theorem primal_colon_iff {S s : Finset (W bs p)} {v : W bs p} (hv : v∉S)
    (hs : (complex h).face s) :
    hits (neighborsForbidden h S v) s ↔
      v∈s ∨ ¬(complex h).face (insert v s) ∨ hits S (insert v s) := by
  classical
  simp only [neighborsForbidden,hits,mem_filter,mem_univ,true_and,face_insert_iff h hs]
  constructor
  · rintro ⟨w,hw,(hS|rfl|hn)⟩
    · exact Or.inr (Or.inr ⟨w,mem_insert_of_mem hw,hS⟩)
    · exact Or.inl hw
    · exact Or.inr (Or.inl (fun hyp => hn (hyp w hw)))
  · rintro (hvs|hn|⟨w,hw,hS⟩)
    · exact ⟨v,hvs,Or.inr (Or.inl rfl)⟩
    · push_neg at hn
      obtain ⟨w,hw,hn⟩ := hn
      exact ⟨w,hw,Or.inr (Or.inr hn)⟩
    · exact ⟨w,(mem_insert.mp hw).resolve_left (fun eq => hv (eq ▸ hS)),Or.inl hS⟩

end RollerFiltration
