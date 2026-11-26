import Conjectures.RollerKoszulContract

/-! The short exact sequence of *actual normalized bar cochains* induced by a colon
step. The left map extends a cochain of the quotient by the larger ideal by zero.
The right map precomposes with multiplication by the degree-one element. -/
namespace RollerKoszul.BasisGrading

variable {A : Type*} [MonoidWithZero A] (g : BasisGrading A)
variable {K : Type*} [AddCommGroup K]

/-- One based linear colon step. The last condition says multiplication identifies
the remaining basis bijectively with the new basis part of the ideal. -/
structure Colon (I J L : Set A) (x : A) : Prop where
  degree_one : g.degree x = 1
  adds : ∀ a, a ∈ I ↔ a ∈ J ∨ ∃ b, x*b=a
  colon : ∀ a, a ∈ L ↔ x*a ∈ J
  cancel : ∀ a b, x*a ∉ J → x*a=x*b → a=b

variable {I J L : Set A} {x : A}
variable (r : g.Colon I J L x)
include r

private theorem restrict_valid {a : A} {ws : List g.Atom} {n d : ℕ}
    (h : g.Valid I n d a ws) : g.Valid J n d a ws :=
  ⟨fun ha => h.1 ((r.adds a).mpr (Or.inl ha)),h.2⟩

private theorem pull_valid (hJ : Closed J) {a : A} {ws : List g.Atom} {n d : ℕ}
    (h : g.Valid J n (d+1) (x*a) ws) : g.Valid L n d a ws := by
  obtain ⟨ha,hz,hl,hd⟩ := h
  have hxa : x*a≠0 := fun e => ha (e ▸ hJ.zero_mem)
  rw [g.product_degree x a hxa,r.degree_one] at hd
  exact ⟨fun h => ha ((r.colon a).mp h),hz,hl,by omega⟩

private theorem push_valid (hJ : Closed J) {a : A} {ws : List g.Atom} {n d : ℕ}
    (h : g.Valid L n d a ws) : g.Valid J n (d+1) (x*a) ws := by
  obtain ⟨ha,hz,hl,hd⟩ := h
  have h' : x*a ∉ J := fun e => ha ((r.colon a).mpr e)
  have hxa : x*a≠0 := fun e => h' (e ▸ hJ.zero_mem)
  exact ⟨h',hz,hl,by rw [g.product_degree x a hxa,r.degree_one]; omega⟩

private def inc (n d : ℕ) : g.cochains K I n d →+ g.cochains K J n d where
  toFun f := ⟨f.val,fun a ws h => restrict_valid g r (f.property a ws h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private def pull (hJ : Closed J) (n d : ℕ) :
    g.cochains K J n (d+1) →+ g.cochains K L n d where
  toFun f := ⟨fun a ws => f.val (x*a) ws,fun a ws h => pull_valid g r hJ (f.property (x*a) ws h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private noncomputable def liftCochain (hJ : Closed J) {n d : ℕ} (f : g.cochains K L n d) :
    g.cochains K J n (d+1) := by
  classical
  let val (a : A) (ws : List g.Atom) : K :=
    if h : ∃ b, x*b=a ∧ a∉J then f.val h.choose ws else 0
  refine ⟨val,?_⟩
  intro a ws h
  by_cases ha : ∃ b, x*b=a ∧ a∉J
  · have h' : f.val ha.choose ws ≠ 0 := by simpa only [val,dif_pos ha] using h
    exact ha.choose_spec.1 ▸ push_valid g r hJ (f.property _ _ h')
  · exact False.elim (h (by simp only [val,dif_neg ha]))

private theorem pull_lift (hJ : Closed J) {n d : ℕ} (f : g.cochains K L n d) :
    pull g r hJ n d (liftCochain g r hJ f) = f := by
  classical
  apply Subtype.ext; funext a ws
  change (if h : ∃ b, x*b=x*a ∧ x*a∉J then f.val h.choose ws else 0) = f.val a ws
  by_cases ha : x*a∈J
  · rw [dif_neg (fun he => he.choose_spec.2 ha)]
    symm
    by_contra hn
    exact (f.property _ _ hn).1 ((r.colon a).mpr ha)
  · have he : ∃ b, x*b=x*a ∧ x*a∉J := ⟨a,rfl,ha⟩
    rw [dif_pos he, ← r.cancel a he.choose ha he.choose_spec.1.symm]

/-- The exact row of homogeneous cochain complexes attached to a single colon step. -/
noncomputable def colon_row (hI : Closed I) (hJ : Closed J) (hL : Closed L) (d : ℕ) :
    ShortExact (g.barComplex K I hI (d+1)) (g.barComplex K J hJ (d+1))
      (g.barComplex K L hL d) where
  i n := inc g r n (d+1)
  p n := pull g r hJ n d
  injective n _ _ h := Subtype.ext (congrArg (fun f : g.cochains K J n (d+1) => f.val) h)
  surjective _ f := ⟨liftCochain g r hJ f,pull_lift g r hJ f⟩
  middle n f := by
    constructor
    · intro hf
      refine ⟨⟨f.val,?_⟩,rfl⟩
      intro a ws h
      obtain ⟨hj,hh⟩ := f.property _ _ h
      refine ⟨?_,hh⟩
      intro hi
      rcases (r.adds a).mp hi with ha | ⟨b,hb⟩
      · exact hj ha
      · subst a
        exact h (congrFun (congrFun (congrArg Subtype.val hf) b) ws)
    · rintro ⟨a,rfl⟩
      apply Subtype.ext; funext b ws
      change a.val (x*b) ws = 0
      exact Classical.byContradiction (fun hn =>
        (a.property (x*b) ws hn).1 ((r.adds _).mpr (Or.inr ⟨b,rfl⟩)))
  di _ _ := rfl
  dp _ f := by
    apply Subtype.ext; funext b ws
    cases ws with
    | nil => rfl
    | cons a l =>
      change f.val (x*(b*a.val)) l - _ = f.val ((x*b)*a.val) l - _
      rw [mul_assoc]
      rfl

omit r

/-- Diagonal exactness in the normalized bar cohomology over the augmentation
module. Its basis after tensoring is the words in positive-degree basis elements. -/
def IsKoszul (K : Type*) [AddCommGroup K] : Prop :=
  ∀ (h : Closed (g.positive : Set A)) (n d : ℕ), n ≠ d →
    AcyclicAt (g.barComplex K g.positive h d) n

theorem positive_closed : Closed (g.positive : Set A) where
  zero_mem := Or.inl rfl
  mul_mem a ha b := by
    by_cases hz : a*b=0
    · exact Or.inl hz
    · have ha' : a≠0 := fun h => hz (h ▸ zero_mul b)
      rcases ha with h|h
      · contradiction
      · exact Or.inr (by rw [g.product_degree a b hz]; omega)

/-- A based Koszul filtration forces diagonal normalized bar cohomology. -/
theorem koszul_of_filtration [Nontrivial A] {ι : Type*} (I : ι → Set A) (size : ι → ℕ)
    (hI : ∀ t, Closed (I t))
    (hstep : ∀ t, I t = {0} ∨ ∃ j k x, size j < size t ∧ g.Colon (I t) (I j) (I k) x)
    (m : ι) (hm : I m = (g.positive : Set A)) : g.IsKoszul K := by
  intro h n d hnd
  rcases lt_or_gt_of_ne hnd with hlt|hgt
  · have hmain := filtration_acyclic (fun t d => g.barComplex K (I t) (hI t) d) size
      (fun t _ hd => g.acyclic_zero (hI t) hd) (by
        intro t
        rcases hstep t with he | ⟨j,k,x,hj,hr⟩
        · left
          intro n d hlt
          have aux (B : Set A) (hB : Closed B) (h : B = {0}) :
              AcyclicAt (g.barComplex K B hB d) n := by
            subst B
            exact g.acyclic_regular _ n d hlt
          exact aux _ _ he
        · exact Or.inr ⟨j,k,hj,fun d => ⟨g.colon_row hr (hI t) (hI j) (hI k) d⟩⟩)
    simpa only [hm] using hmain n m d hlt
  · exact g.above_length h hgt

end RollerKoszul.BasisGrading
