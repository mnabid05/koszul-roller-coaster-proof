import Conjectures.RollerVertices
import Conjectures.RollerFaceRing

/-! Actual simplicial complexes realizing the required face polynomials. -/
noncomputable section
namespace RollerVertices
open Finset RollerShelling RollerRealization RollerFaceRing
open scoped Classical

variable {p k : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b)

abbrev ActualVertex (bs : List Block) (p : ℕ) := Vertex bs ⊕ Fin p

def complex (h : ∀ b ∈ bs, Admissible p b) : Complex (ActualVertex bs p) where
  face := RollerShelling.Face (color h) (Old h)
  empty := ⟨old_empty h, by simp⟩
  downward := fun {s t} sub ht => face_downward (color h) _ (old_down h) sub ht

theorem flag : RollerShelling.Flag (complex h).face :=
  face_flag _ _ (old_flag h)

theorem size_bound (f : RollerFaceRing.Face (complex h)) : f.val.card ≤ p := by
  obtain ⟨s,hs,hu⟩ := (face_iff_subset_completion (color h) (Old h) (old_down h) f.val).mp f.property
  exact (card_le_card hu).trans_eq (by simpa using card_completion (color h) s hs.2)

private def available (s : Finset (Vertex bs)) := (s.image (color h))ᶜ

private lemma card_available {s : Finset (Vertex bs)} (hs : Old h s) :
    (available h s).card = p-s.card := by
  simp [available,card_compl,card_image_of_injOn hs.2]

private abbrev OldAt (j : ℕ) := {s : Finset (Vertex bs) // Old h s ∧ s.card=j}

private abbrev Code (k : ℕ) := RollerCoaster.Selection (Fin p) k ⊕
  (Σ i : Fin p, Σ s : OldAt h (p-i.val), ↥((available h s.val).powersetCard (p-k)))

private def codeToFace (hk : k≤p) : Code h k → FaceAt (complex h) k
  | .inl t => ⟨(∅ : Finset (Vertex bs)).disjSum t.val,
      by change RollerShelling.Face _ _ _; simp only [RollerShelling.Face,toLeft_disjSum,toRight_disjSum]; exact ⟨old_empty h,by simp⟩, by simpa using t.property⟩
  | .inr ⟨i,s,m⟩ => by
    let free := available h s.val
    have hm := Finset.mem_powersetCard.mp m.property
    have hfc := card_available h s.property.1
    have hsc := s.property.2
    have hi := i.isLt
    have hle := card_le_card hm.1
    refine ⟨s.val.disjSum (free \ m.val),?_,?_⟩
    · simp only [complex,RollerShelling.Face,toLeft_disjSum,toRight_disjSum]
      exact ⟨s.property.1,fun x hx => mem_compl.mp (mem_sdiff.mp hx).1⟩
    · rw [card_disjSum,card_sdiff hm.1]
      omega

private lemma inject_code (hk : k≤p) : Function.Injective (codeToFace h hk) := by
  rintro (t|⟨i,s,m⟩) (u|⟨j,v,n⟩) he
  · have he' := congrArg (fun z : FaceAt (complex h) k => z.val.toRight) he
    simp only [codeToFace,toRight_disjSum] at he'
    exact congrArg Sum.inl (Subtype.ext he')
  · have he' := congrArg (fun z : FaceAt (complex h) k => z.val.toLeft.card) he
    simp only [codeToFace,toLeft_disjSum,card_empty,v.property.2] at he'
    have := j.isLt
    omega
  · have he' := congrArg (fun z : FaceAt (complex h) k => z.val.toLeft.card) he
    simp only [codeToFace,toLeft_disjSum,card_empty,s.property.2] at he'
    have := i.isLt
    omega
  · have eqs := congrArg (fun z : FaceAt (complex h) k => z.val.toLeft) he
    simp only [codeToFace,toLeft_disjSum] at eqs
    have eqi : i=j := by
      apply Fin.ext
      have hs := s.property.2
      have hv := v.property.2
      rw [eqs] at hs
      have := i.isLt
      have := j.isLt
      omega
    subst j
    have eqv : s=v := Subtype.ext eqs
    subst v
    have eqm := congrArg (fun z : FaceAt (complex h) k => z.val.toRight) he
    simp only [codeToFace,toRight_disjSum] at eqm
    have meq := congrArg (fun z => available h s.val \ z) eqm
    simp only [Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp m.property).1,
      Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp n.property).1] at meq
    have eqn : m=n := Subtype.ext meq
    subst n
    rfl

private lemma surject_code (hk : k≤p) : Function.Surjective (codeToFace h hk) := by
  rintro ⟨f,hf,hk'⟩
  have hOld := hf.1
  have hsub : f.toRight ⊆ available h f.toLeft := fun x hx => mem_compl.mpr (hf.2 x hx)
  have dims := Finset.card_toLeft_add_card_toRight (u:=f)
  by_cases he : f.toLeft=∅
  · have hc : f.toRight.card=k := by simpa [he,hk'] using dims
    refine ⟨.inl ⟨_,hc⟩,Subtype.ext ?_⟩
    change (∅ : Finset (Vertex bs)).disjSum f.toRight=f
    rw [← he,toLeft_disjSum_toRight]
  · have hsize : f.toLeft.card ≤ p := by
      have ht := card_le_univ (f.toLeft.image (color h))
      rw [card_image_of_injOn hOld.2,Fintype.card_fin] at ht
      exact ht
    have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    let i : Fin p := ⟨p-f.toLeft.card, by omega⟩
    let s : OldAt h (p-i.val) := ⟨f.toLeft,hOld,by dsimp [i]; omega⟩
    let m := available h f.toLeft \ f.toRight
    have hm : m ∈ (available h s.val).powersetCard (p-k) := by
      apply mem_powersetCard.mpr
      refine ⟨Finset.sdiff_subset,?_⟩
      rw [show m = available h f.toLeft \ f.toRight by rfl,card_sdiff hsub,card_available h hOld]
      omega
    refine ⟨.inr ⟨i,s,⟨m,hm⟩⟩,Subtype.ext ?_⟩
    change f.toLeft.disjSum (available h f.toLeft \ (available h f.toLeft \ f.toRight)) = f
    rw [Finset.sdiff_sdiff_eq_self hsub,toLeft_disjSum_toRight]

theorem card_faceAt (k : ℕ) : Fintype.card (FaceAt (complex h) k) =
    RollerCoaster.whiskeredFaces p bs k := by
  classical
  by_cases hk : k≤p
  · rw [← Fintype.card_congr (Equiv.ofBijective _ ⟨inject_code h hk,surject_code h hk⟩)]
    change Fintype.card (RollerCoaster.Selection (Fin p) k ⊕ _) = _
    rw [Fintype.card_sum, RollerCoaster.whiskeredFaces,if_pos hk]
    simp only [RollerCoaster.Selection,Fintype.card_finset_len,Fintype.card_fin,Fintype.card_sigma,
      Fintype.card_coe,Finset.card_powersetCard]
    rw [Finset.sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hw (s : OldAt h (p-i.val)) : (available h s.val).card=i.val := by
      rw [card_available h s.property.1,s.property.2,Nat.sub_sub_self i.isLt.le]
    simp only [hw,Finset.sum_const,Finset.card_univ, Nat.nsmul_eq_mul]
    rw [card_old h (by have := i.isLt; omega)]
  · rw [RollerCoaster.whiskeredFaces, if_neg hk, Fintype.card_eq_zero_iff]
    exact ⟨fun f => hk (f.property.2 ▸ size_bound h ⟨f.val,f.property.1⟩)⟩

end RollerVertices
