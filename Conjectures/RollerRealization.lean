import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

/-! Exact positive rational face counts using disjoint unions of clique complexes of complete
multipartite graphs.  Each block uses its own part size; colors are its part indices. -/

namespace RollerRealization

/-- A multiplicity of identical complete multipartite clique complexes. -/
structure Block where
  copies : ℕ
  parts : ℕ
  size : ℕ
deriving DecidableEq

/-- Each nonempty k-face chooses k of the parts and a vertex in each chosen part. -/
def faceCount (k : ℕ) : List Block → ℕ
  | [] => 0
  | b :: bs => b.copies * b.parts.choose k * b.size ^ k + faceCount k bs

def Admissible (p : ℕ) (b : Block) : Prop :=
  0 < b.copies ∧ 0 < b.parts ∧ b.parts ≤ p ∧ 0 < b.size

private theorem outside {p k : ℕ} {bs : List Block} (h : ∀ b ∈ bs, Admissible p b)
    (hk : p < k) : faceCount k bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := h b (by simp)
    simp only [faceCount, Nat.choose_eq_zero_of_lt (lt_of_le_of_lt hb.2.2.1 hk),
      Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- The realization for positive integral target vectors. -/
theorem realize_nat (p : ℕ) (q : ℕ → ℕ) (hq : ∀ k, 0 < k → k ≤ p → 0 < q k) :
    ∃ (M : ℕ) (bs : List Block), 0 < M ∧ (∀ b ∈ bs, Admissible p b) ∧
      ∀ k, 0 < k → k ≤ p → faceCount k bs = M * q k := by
  induction p generalizing q with
  | zero => exact ⟨1, [], by decide, by simp, fun k hk h => by omega⟩
  | succ p ih =>
    let t := q (p+1)
    let N := t * 2 ^ p + 1
    let L := N ^ (p+1)
    let c : ℕ → ℕ := fun k => t * (p+1).choose k * N^k
    let q' : ℕ → ℕ := fun k => L * q k - c k
    have hN : 0 < N := Nat.succ_pos _
    have ht : 0 < t := hq _ (Nat.succ_pos _) le_rfl
    have hLpos : 0 < L := pow_pos hN _
    have hsmall (k : ℕ) (hk : k ≤ p) : c k < L := by
      have hc : t * (p+1).choose k < N := Nat.lt_succ_of_le
        (Nat.mul_le_mul_left _ (Nat.choose_succ_le_two_pow p k))
      calc
        c k < N * N^k := Nat.mul_lt_mul_of_pos_right hc (pow_pos hN _)
        _ = N ^ (k+1) := (pow_succ' _ _).symm
        _ ≤ L := Nat.pow_le_pow_right hN (by omega)
    have hres (k : ℕ) (hk : 0 < k) (hp : k ≤ p) : c k < L * q k := by
      exact (hsmall k hp).trans_le <| Nat.le_mul_of_pos_right _ (hq k hk (by omega))
    obtain ⟨m, bs, hm, hb, he⟩ := ih q' (fun k hk hp => Nat.sub_pos_of_lt (hres k hk hp))
    refine ⟨m * L, ⟨m*t, p+1, N⟩ :: bs, Nat.mul_pos hm hLpos, ?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | h
      · exact ⟨Nat.mul_pos hm ht, Nat.succ_pos _, le_rfl, hN⟩
      · have b := hb a h
        exact ⟨b.1, b.2.1, b.2.2.1.trans (Nat.le_succ p), b.2.2.2⟩
    · intro k hk hp
      by_cases hkp : k ≤ p
      · rw [faceCount, he k hk hkp]
        change m*t * (p+1).choose k * N^k + m * (L*q k - c k) = m*L*q k
        rw [show m*t * (p+1).choose k * N^k = m * c k by dsimp [c]; ac_rfl,
          ← Nat.mul_add, Nat.add_sub_of_le (hres k hk hkp).le, Nat.mul_assoc]
      · have hkp' : k = p+1 := by omega
        subst k
        simp only [faceCount, Nat.choose_self, Nat.mul_one,
          outside hb (Nat.lt_succ_self p), Nat.add_zero]
        change m * t * L = m * L * t
        ac_rfl

private theorem clear_denominators (p : ℕ) (q : ℕ → ℚ) (hq : ∀ k, 0 < k → k ≤ p → 0 < q k) :
    ∃ (D : ℕ) (a : ℕ → ℕ), 0 < D ∧
      ∀ k, 0 < k → k ≤ p → 0 < a k ∧ (a k : ℚ) = D * q k := by
  classical
  let T := Finset.range (p+1)
  let d := fun i => (q i).den
  let D := ∏ i ∈ T, d i
  let rest := fun k => ∏ i ∈ T.erase k, d i
  let a := fun k => (q k).num.natAbs * rest k
  have hd (s : Finset ℕ) : 0 < ∏ i ∈ s, d i := by
    induction s using Finset.induction with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi]; exact Nat.mul_pos (q i).den_pos ih
  refine ⟨D, a, hd T, ?_⟩
  intro k hk hp
  have hmem : k ∈ T := Finset.mem_range.mpr (by omega)
  have heq : D = d k * rest k := (Finset.mul_prod_erase T d hmem).symm
  have hnum : 0 < (q k).num := Rat.num_pos.mpr (hq k hk hp)
  have ha : 0 < (q k).num.natAbs := Int.natAbs_pos.mpr hnum.ne'
  refine ⟨Nat.mul_pos ha (hd _), ?_⟩
  change (((q k).num.natAbs * rest k : ℕ) : ℚ) = D * q k
  rw [heq, Nat.cast_mul, Nat.cast_mul, Nat.cast_natAbs, abs_of_pos hnum]
  have hq' : (q k).den * q k = ((q k).num : ℚ) := by
    have hh := Rat.num_div_den (q k)
    exact (mul_comm ..).trans ((div_eq_iff (Nat.cast_ne_zero.mpr (q k).den_nz)).mp hh).symm
  change _ = ((q k).den : ℚ) * rest k * q k
  rw [← hq']
  ring

/-- Every strictly positive rational list occurs, after a single integral scaling, as all the
nonempty face counts of disjoint, complete multipartite clique complexes using at most p colors. -/
theorem realize (p : ℕ) (q : ℕ → ℚ) (hq : ∀ k, 0 < k → k ≤ p → 0 < q k) :
    ∃ (M : ℕ) (bs : List Block), 0 < M ∧ (∀ b ∈ bs, Admissible p b) ∧
      ∀ k, 0 < k → k ≤ p → (faceCount k bs : ℚ) = M * q k := by
  obtain ⟨D,a,hD,ha⟩ := clear_denominators p q hq
  obtain ⟨m,bs,hm,hb,he⟩ := realize_nat p a (fun k hk hp => (ha k hk hp).1)
  refine ⟨m*D,bs,Nat.mul_pos hm hD,hb,fun k hk hp => ?_⟩
  rw [he k hk hp, Nat.cast_mul, (ha k hk hp).2, Nat.cast_mul, mul_assoc]

section Cliques

open scoped BigOperators Classical

variable {n N k : ℕ}

abbrev Choice (n N k : ℕ) := Σ s : {s : Finset (Fin n) // s.card = k}, (s.val → Fin N)
abbrev CliqueFace (n N k : ℕ) := {s : Finset (Fin n × Fin N) //
  s.card = k ∧ Set.InjOn Prod.fst (s : Set (Fin n × Fin N))}

private def choiceVerts (s : Finset (Fin n)) (f : s → Fin N) : Finset (Fin n × Fin N) :=
  s.attach.map ⟨fun t : ↥s => (t.val, f t), fun _ _ eq => Subtype.ext (congrArg Prod.fst eq)⟩

@[simp] private theorem mem_choiceVerts (s : Finset (Fin n)) (f : s → Fin N) (v : Fin n × Fin N) :
    v ∈ choiceVerts s f ↔ ∃ h : v.1 ∈ s, f ⟨v.1,h⟩ = v.2 := by
  constructor
  · intro h
    obtain ⟨u, _, he⟩ := Finset.mem_map.mp h
    change (u.val, f u) = v at he
    subst v
    exact ⟨u.property,rfl⟩
  · rintro ⟨h,hf⟩
    refine Finset.mem_map.mpr ⟨⟨v.1,h⟩, Finset.mem_attach .., ?_⟩
    exact Prod.ext rfl hf

private def choiceToFace (t : Choice n N k) : CliqueFace n N k :=
  ⟨choiceVerts t.1.val t.2, by simpa [choiceVerts] using t.1.property, by
    rintro ⟨i,u⟩ hu ⟨j,v⟩ hv e
    change i=j at e
    subst j
    obtain ⟨_, hua⟩ := (mem_choiceVerts ..).mp hu
    obtain ⟨_, hva⟩ := (mem_choiceVerts ..).mp hv
    exact Prod.ext rfl (hua.symm.trans hva)⟩

private theorem parts_of_choice (s : Finset (Fin n)) (f : s → Fin N) :
    (choiceVerts s f).image Prod.fst = s := by
  ext i
  constructor
  · intro h
    obtain ⟨⟨j,u⟩, hj, rfl⟩ := Finset.mem_image.mp h
    exact ((mem_choiceVerts ..).mp hj).choose
  · intro hi
    exact Finset.mem_image.mpr ⟨(i, f ⟨i,hi⟩),(mem_choiceVerts ..).mpr ⟨hi,rfl⟩,rfl⟩

private theorem choice_inj : Function.Injective (@choiceToFace n N k) := by
  rintro ⟨⟨s,hs⟩,f⟩ ⟨⟨t,ht⟩,g⟩ he
  have he' : choiceVerts s f = choiceVerts t g := congrArg Subtype.val he
  have hst := congrArg (Finset.image Prod.fst) he'
  simp only [parts_of_choice] at hst
  subst t
  have hfg : f = g := by
    funext i
    have hm : (i.val, f i) ∈ choiceVerts s f := (mem_choiceVerts ..).mpr ⟨i.property,rfl⟩
    rw [he'] at hm
    exact ((mem_choiceVerts ..).mp hm).choose_spec.symm
  subst g
  rfl

private theorem choice_surj : Function.Surjective (@choiceToFace n N k) := by
  classical
  rintro ⟨v,hk,hi⟩
  let s := v.image Prod.fst
  have hs : s.card = k := (Finset.card_image_of_injOn hi).trans hk
  have existsY (i : s) : ∃ y : Fin N, (i.val,y) ∈ v := by
    obtain ⟨⟨j,y⟩, hy, he⟩ := Finset.mem_image.mp i.property
    exact ⟨y, by simpa only [← he] using hy⟩
  let f : s → Fin N := fun i => (existsY i).choose
  have hf (i : s) : (i.val,f i) ∈ v := (existsY i).choose_spec
  refine ⟨⟨⟨s,hs⟩,f⟩, Subtype.ext ?_⟩
  change choiceVerts s f = v
  ext u
  rw [mem_choiceVerts]
  constructor
  · rintro ⟨h,e⟩
    rw [← Prod.eta u, ←e]
    exact hf ⟨u.1,h⟩
  · intro h
    have hm : u.1 ∈ s := Finset.mem_image.mpr ⟨u,h,rfl⟩
    exact ⟨hm,congrArg Prod.snd (hi (hf ⟨u.1,hm⟩) h rfl)⟩

theorem card_cliqueFace (n N k : ℕ) :
    Fintype.card (CliqueFace n N k) = n.choose k * N^k := by
  classical
  rw [← Fintype.card_congr (Equiv.ofBijective choiceToFace ⟨choice_inj,choice_surj⟩)]
  simp only [Choice, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hc (s : {s : Finset (Fin n) // s.card = k}) : s.val.card = k := s.property
  simp [hc, Fintype.card_finset_len]


/-- A nonempty clique of a disjoint union lies in exactly one component. The summand records
the component index, its copy, and the actual vertex subset on which part indices are injective. -/
def LocatedFace (k : ℕ) : List Block → Type
  | [] => Empty
  | b :: bs => (Fin b.copies × CliqueFace b.parts b.size k) ⊕ LocatedFace k bs

noncomputable instance locatedFaceFintype (k : ℕ) (bs : List Block) : Fintype (LocatedFace k bs) := by
  induction bs with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons b bs ih =>
    change Fintype ((_ × _) ⊕ LocatedFace k bs)
    exact inferInstance

theorem card_locatedFace (k : ℕ) (bs : List Block) :
    Fintype.card (LocatedFace k bs) = faceCount k bs := by
  induction bs with
  | nil => exact Fintype.card_empty
  | cons b bs ih =>
    change Fintype.card ((Fin b.copies × CliqueFace b.parts b.size k) ⊕ LocatedFace k bs) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_cliqueFace, ih, faceCount,
      Nat.mul_assoc]

/-- Duplicate every component in a certificate by the same factor. -/
def repeatBlocks (m : ℕ) : List Block → List Block :=
  List.map (fun b => { b with copies := m * b.copies })

theorem faceCount_repeat (m k : ℕ) (bs : List Block) :
    faceCount k (repeatBlocks m bs) = m * faceCount k bs := by
  induction bs with
  | nil => simp [repeatBlocks, faceCount]
  | cons b bs ih =>
    change m * b.copies * b.parts.choose k * b.size^k + faceCount k (repeatBlocks m bs) =
      m * (b.copies * b.parts.choose k * b.size^k + faceCount k bs)
    rw [ih, Nat.mul_add]; ac_rfl

theorem admissible_repeat {m p : ℕ} (hm : 0 < m) {bs : List Block}
    (h : ∀ b ∈ bs, Admissible p b) : ∀ b ∈ repeatBlocks m bs, Admissible p b := by
  rintro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  have hh := h a ha
  exact ⟨Nat.mul_pos hm hh.1,hh.2⟩

/-- Rational face counts, up to a common scale that can be taken arbitrarily large. -/
theorem realize_above (p bound : ℕ) (q : ℕ → ℚ) (hq : ∀ k, 0 < k → k ≤ p → 0 < q k) :
    ∃ (M : ℕ) (bs : List Block), bound < M ∧ (∀ b ∈ bs, Admissible p b) ∧
      ∀ k, 0 < k → k ≤ p → (Fintype.card (LocatedFace k bs) : ℚ) = M * q k := by
  obtain ⟨m,bs,hm,hb,he⟩ := realize p q hq
  refine ⟨(bound+1)*m,repeatBlocks (bound+1) bs, ?_,
    admissible_repeat (Nat.succ_pos _) hb,fun k hk hp => ?_⟩
  · exact (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_right _ hm)
  · rw [card_locatedFace, faceCount_repeat, Nat.cast_mul, he k hk hp, Nat.cast_mul, mul_assoc]

end Cliques
end RollerRealization
