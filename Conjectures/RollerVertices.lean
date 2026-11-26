import Conjectures.RollerFaces
import Conjectures.RollerShelling
import Mathlib.Data.Finset.Preimage

/-! The components and vertices of the realizing graph, and its old faces as actual
subsets of a common finite vertex set. A nonempty face identifies its component uniquely. -/
namespace RollerVertices
open RollerRealization Finset
open scoped Classical

def Component : List Block → Type
  | [] => Empty
  | b :: bs => Fin b.copies ⊕ Component bs

instance componentFinite (bs : List Block) : Fintype (Component bs) := by
  induction bs with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons b bs ih => exact inferInstanceAs (Fintype (Fin b.copies ⊕ Component bs))

def parts : (bs : List Block) → Component bs → ℕ
  | [], x => nomatch x
  | b :: _, .inl _ => b.parts
  | _ :: bs, .inr q => parts bs q

def partSize : (bs : List Block) → Component bs → ℕ
  | [], x => nomatch x
  | b :: _, .inl _ => b.size
  | _ :: bs, .inr q => partSize bs q

theorem parts_le {p : ℕ} (bs : List Block) (h : ∀ b ∈ bs, Admissible p b) (t : Component bs) :
    parts bs t ≤ p := by
  induction bs with
  | nil => exact nomatch t
  | cons b bs ih =>
    rcases t with t|t
    · exact (h b (by simp)).2.2.1
    · exact ih (fun b hb => h b (by simp [hb])) t

abbrev Point (bs : List Block) (t : Component bs) := Fin (parts bs t) × Fin (partSize bs t)
abbrev Vertex (bs : List Block) := Σ t : Component bs, Point bs t

def color {p : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b) (x : Vertex bs) : Fin p :=
  Fin.castLE (parts_le bs h x.1) x.2.1

def Old {p : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b) (s : Finset (Vertex bs)) : Prop :=
  (∀ x ∈ s, ∀ y ∈ s, x.1=y.1) ∧ Set.InjOn (color h) (s : Set _)

theorem old_down {p : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b) :
    RollerShelling.Downward (Old h) := by
  rintro s t hs ⟨hc,hi⟩
  exact ⟨fun x hx y hy => hc x (hs hx) y (hs hy),hi.mono hs⟩

theorem old_flag {p : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b) :
    RollerShelling.Flag (Old h) := by
  classical
  intro s hh
  have pair (x y : Vertex bs) (hx : x∈s) (hy : y∈s) : Old h {x,y} :=
    hh {x,y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) Finset.card_le_two
  exact ⟨fun x hx y hy => (pair x y hx hy).1 x (by simp) y (by simp),
    fun x hx y hy e => (pair x y hx hy).2 (by simp) (by simp) e⟩

theorem old_empty {p : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b) : Old h ∅ := by
  simp [Old]

def pointEmbedding {bs : List Block} (t : Component bs) : Point bs t ↪ Vertex bs :=
  ⟨Sigma.mk t, fun _ _ e => eq_of_heq (Sigma.mk.inj e).2⟩

variable {p k : ℕ} {bs : List Block}

private def oldMap (h : ∀ b ∈ bs, Admissible p b)
    (s : Σ t : Component bs, CliqueFace (parts bs t) (partSize bs t) k) :
    {S : Finset (Vertex bs) // Old h S ∧ S.card=k} := by
  rcases s with ⟨t,f⟩
  refine ⟨f.val.map (pointEmbedding t), ⟨?_,?_⟩, by simpa using f.property.1⟩
  · intro x hx y hy
    obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hy
    rfl
  · intro x hx y hy e
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
    exact congrArg (pointEmbedding t) (f.property.2 hu hv (Fin.ext (congrArg (fun i : Fin p => i.val) e)))

private lemma oldMap_bijective (h : ∀ b ∈ bs, Admissible p b) (hk : 0<k) :
    Function.Bijective (oldMap (k:=k) h) := by
  classical
  constructor
  · rintro ⟨t,f⟩ ⟨u,g⟩ e
    have he : f.val.map (pointEmbedding t) = g.val.map (pointEmbedding u) := congrArg Subtype.val e
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < f.val.card by omega)
    have hx' : pointEmbedding t x ∈ g.val.map (pointEmbedding u) := he ▸ Finset.mem_map.mpr ⟨x,hx,rfl⟩
    obtain ⟨_, _, htu⟩ := Finset.mem_map.mp hx'
    have eqtag : u=t := congrArg Sigma.fst htu
    subst u
    have efg : f=g := Subtype.ext (Finset.map_injective (pointEmbedding t) he)
    cases efg
    rfl
  · rintro ⟨S,hS,hcard⟩
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<S.card by omega)
    let t := x.1
    let e := pointEmbedding (bs:=bs) t
    let f := S.preimage e e.injective.injOn
    have hmap : f.map e = S := by
      ext v
      constructor
      · rintro hv
        obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hv
        exact Finset.mem_preimage.mp hz
      · intro hv
        rcases v with ⟨j,z⟩
        have htag : t=j := hS.1 x hx ⟨j,z⟩ hv
        subst j
        exact Finset.mem_map.mpr ⟨z, Finset.mem_preimage.mpr hv,rfl⟩
    have hfc : f.card=k := by rw [← hcard, ← hmap, Finset.card_map]
    have hi : Set.InjOn (fun z : Point bs t => z.1) (f : Set (Point bs t)) := by
      intro z hz w hw he
      apply e.injective
      apply hS.2 (Finset.mem_preimage.mp hz) (Finset.mem_preimage.mp hw)
      exact Fin.ext (congrArg (fun i : Fin (parts bs t) => i.val) he)
    exact ⟨⟨t,⟨f,hfc,hi⟩⟩,Subtype.ext hmap⟩

private theorem sum_component (bs : List Block) (k : ℕ) :
    (∑ t : Component bs, (parts bs t).choose k * (partSize bs t)^k) = faceCount k bs := by
  induction bs with
  | nil => exact Finset.sum_empty
  | cons b bs ih =>
    change (∑ t : Fin b.copies ⊕ Component bs, _) = _
    rw [Fintype.sum_sum_type]
    simp [parts,partSize,faceCount,ih,Nat.mul_assoc]

theorem card_old (h : ∀ b ∈ bs, Admissible p b) (hk : 0<k) :
    Fintype.card {S : Finset (Vertex bs) // Old h S ∧ S.card=k} = faceCount k bs := by
  rw [← Fintype.card_congr (Equiv.ofBijective _ (oldMap_bijective h hk)),
    Fintype.card_sigma]
  simp only [card_cliqueFace, sum_component]

end RollerVertices
