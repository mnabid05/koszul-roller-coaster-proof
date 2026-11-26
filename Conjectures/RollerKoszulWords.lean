import Conjectures.RollerKoszulFiltration

/-! The usual reduced bar cochains, expressed on words in the augmentation basis,
with the alternating adjacent-product differential. The zero basis product is
represented by a letter on which every homogeneous cochain vanishes. -/
namespace RollerKoszul.BasisGrading
variable {A : Type*} [MonoidWithZero A] [Nontrivial A] (g : BasisGrading A)
variable {K : Type*} [AddCommGroup K]

/-- The bidegree-(n,d) cochain space of the reduced bar construction. -/
def wordCochains (K : Type*) [AddCommGroup K] (n d : ℕ) : AddSubgroup (List g.Atom → K) where
  carrier := {f | ∀ w, f w ≠ 0 →
    0 ∉ w.map Subtype.val ∧ w.length = n ∧ g.wordDegree w = d}
  zero_mem' := by intro w h; exact False.elim (h rfl)
  add_mem' := by
    intro f h hf hh w hsum
    by_cases h' : f w = 0
    · exact hh w (fun hz => hsum (by simp [h',hz]))
    · exact hf w h'
  neg_mem' := by
    intro f hf w h
    exact hf w (fun hz => h (by simp [hz]))

private theorem one_not_positive : (1:A) ∉ g.positive := by
  change ¬ ((1:A) = 0 ∨ 0 < g.degree 1)
  simp [g.one_degree]

/-- The residue-module slot in a normalized cochain is determined by its value at 1. -/
noncomputable def wordEquiv (n d : ℕ) :
    g.cochains K g.positive n d ≃+ g.wordCochains K n d := by
  classical
  let extend (f : g.wordCochains K n d) (a : A) (w : List g.Atom) := if a=1 then f.val w else 0
  exact {
    toFun := fun f => ⟨f.val 1,by
      intro w h
      obtain ⟨_,hz,hw,hd⟩ := f.property 1 w h
      exact ⟨hz,hw,by simpa [g.one_degree] using hd⟩⟩
    invFun := fun f => ⟨extend f,by
      intro a w h
      by_cases ha : a=1
      · subst a
        obtain ⟨hz,hw,hd⟩ := f.property w (by simpa [extend] using h)
        exact ⟨g.one_not_positive,hz,hw,by simp [hd,g.one_degree]⟩
      · exact False.elim (h (by simp [extend,ha]))⟩
    left_inv := by
      intro f
      apply Subtype.ext; funext a w
      by_cases ha : a = 1
      · simp [extend,ha]
      · change (if a=1 then f.val 1 w else 0) = f.val a w
        rw [if_neg ha]; symm
        apply Classical.byContradiction
        intro hn
        have h := (f.property a w hn).1
        exact ha (g.unit_of_degree_zero a (fun hz => h (Or.inl hz))
          (by by_contra hp; exact h (Or.inr (Nat.pos_of_ne_zero hp))))
    right_inv := fun f => Subtype.ext (by funext w; simp [extend])
    map_add' := fun _ _ => rfl }

def reduced (f : List g.Atom → K) : List g.Atom → K
  | [] => 0
  | x::xs => -Bar.internal (fun b t => f (b::t)) x xs

theorem wordEquiv_d (n d : ℕ) (f : g.cochains K g.positive n d) (w : List g.Atom) :
    (g.wordEquiv (n+1) d (g.differential g.positive_closed n d f)).val w =
      g.reduced (g.wordEquiv n d f).val w := by
  cases w with
  | nil => rfl
  | cons x xs =>
    change f.val (1*x.val) xs - _ = -_
    rw [one_mul]
    have hz : f.val x.val xs = 0 := Classical.byContradiction (fun hn =>
      (f.property _ _ hn).1 x.property)
    rw [hz,zero_sub]
    rfl

/-- Every homogeneous reduced-bar cocycle away from the diagonal is zero in
degree zero or has a homogeneous reduced-bar primitive in positive degree. -/
theorem reduced_exact (hk : g.IsKoszul K) (n d : ℕ) (hnd : n≠d)
    (f : g.wordCochains K n d) (hf : ∀ w, g.reduced f.val w = 0) :
    match n, f with
    | 0, f => f = 0
    | t+1, f => ∃ h : g.wordCochains K t d, ∀ w, g.reduced h.val w = f.val w := by
  let e := g.wordEquiv (K := K) n d
  let z := e.symm f
  have he : e z = f := e.apply_symm_apply f
  have hc : (g.barComplex K g.positive g.positive_closed d).d n z = 0 := by
    apply (g.wordEquiv (n+1) d).injective
    rw [map_zero]
    apply Subtype.ext; funext w
    exact (g.wordEquiv_d n d z w).trans (by change g.reduced (e z).val w = 0; rw [he]; exact hf w)
  have hb := hk g.positive_closed n d hnd z hc
  cases n with
  | zero =>
    change z=0 at hb
    change f=0
    exact he.symm.trans ((congrArg e hb).trans (map_zero e))
  | succ t =>
    obtain ⟨h,hh⟩ := hb
    refine ⟨g.wordEquiv t d h,fun w => (g.wordEquiv_d t d h w).symm.trans ?_⟩
    change (e ((g.barComplex K g.positive g.positive_closed d).d t h)).val w = f.val w
    rw [hh,he]

end RollerKoszul.BasisGrading
