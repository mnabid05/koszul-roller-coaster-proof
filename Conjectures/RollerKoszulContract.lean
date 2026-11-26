import Conjectures.RollerKoszulCochains

/-! Exactness for the regular module, zero cohomological degree for cyclic quotients,
and the lower internal-degree bound. -/
namespace RollerKoszul.BasisGrading
variable {A : Type*} [MonoidWithZero A] (g : BasisGrading A) {K : Type*} [AddCommGroup K]

theorem above_length {I : Set A} (hI : Closed I) {d n : ℕ} (h : d < n) :
    AcyclicAt (g.barComplex K I hI d) n := by
  intro f _
  have hh : ∀ ws : List g.Atom, 0 ∉ ws.map Subtype.val → ws.length ≤ g.wordDegree ws := by
    intro ws
    induction ws with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons,List.mem_cons,not_or,List.length_cons,wordDegree_cons]
      rintro ⟨hx,hxs⟩
      have hp := x.property
      change x.val = 0 ∨ 0 < g.degree x.val at hp
      have hp' : 0 < g.degree x.val := hp.resolve_left (Ne.symm hx)
      have := ih hxs
      omega
  have hz : f = 0 := by
    apply Subtype.ext; funext a ws
    by_contra hn
    have hv := f.property a ws hn
    obtain ⟨_,hw,hl,hd⟩ := hv
    have := hh ws hw
    omega
  cases n with
  | zero => exact hz
  | succ n => exact ⟨0,(map_zero _).trans hz.symm⟩

theorem acyclic_zero {I : Set A} (hI : Closed I) {d : ℕ} (h : 0 < d) :
    AcyclicAt (g.barComplex K I hI d) 0 := by
  intro f hf
  apply Subtype.ext; funext a ws
  by_contra hn
  obtain ⟨_,_,hlen,hd⟩ := f.property a ws hn
  have hws : ws=[] := List.length_eq_zero_iff.mp hlen
  subst ws
  simp only [wordDegree_nil,Nat.add_zero] at hd
  let x : g.Atom := ⟨a, Or.inr (hd ▸ h)⟩
  have hh := congrFun (congrFun (congrArg Subtype.val hf) 1) [x]
  change f.val (1*a) [] - 0 = 0 at hh
  exact hn (by simpa using hh)

private noncomputable def shift (f : A → List g.Atom → K) (a : A) (ws : List g.Atom) : K := by
  classical
  exact if h : a ∈ g.positive then f 1 (⟨a,h⟩::ws) else 0

private theorem shift_atom (f : A → List g.Atom → K) (a : g.Atom) (ws : List g.Atom) :
    g.shift f a.val ws = f 1 (a::ws) := by
  classical
  simp [shift,a.property]

private theorem shift_one [Nontrivial A] (f : A → List g.Atom → K) (ws : List g.Atom) :
    g.shift f 1 ws = 0 := by
  classical
  have hh : (1:A) ∉ g.positive := by
    change ¬ ((1 : A) = 0 ∨ 0 < g.degree 1)
    simp [g.one_degree]
  simp [shift,hh]

private theorem shift_support {n d : ℕ} (f : g.cochains K ({0} : Set A) (n+1) d) :
    g.shift f.val ∈ g.cochains K ({0} : Set A) n d := by
  classical
  intro a ws h
  by_cases ha : a ∈ g.positive
  · rw [shift, dif_pos ha] at h
    obtain ⟨_,hz,hlen,hd⟩ := f.property _ _ h
    simp only [List.map_cons,List.mem_cons,not_or] at hz
    refine ⟨?_,hz.2,by simpa using hlen,?_⟩
    · exact Ne.symm hz.1
    · simpa [g.one_degree] using hd
  · exact False.elim (h (by simp [shift,ha]))

private theorem delta_shift_atom (f : A → List g.Atom → K) (a : g.Atom) (ws : List g.Atom) :
    Bar.delta g.action (g.shift f) a.val ws =
      Bar.internal (fun b tail => f 1 (b::tail)) a ws := by
  cases ws with
  | nil => rfl
  | cons x xs =>
    rw [Bar.delta,Bar.internal]
    change g.shift f (a*x).val xs - _ = _
    rw [g.shift_atom]
    congr 1
    exact congrArg (fun h => Bar.internal h x xs) (funext fun b => funext fun t =>
      g.shift_atom f a (b::t))

/-- Contract the normalized bar cochain complex of the regular module by moving
the positive leading coefficient into the word. -/
theorem acyclic_regular [Nontrivial A] (hI : Closed ({0} : Set A)) (n d : ℕ) (h : n < d) :
    AcyclicAt (g.barComplex K {0} hI d) n := by
  cases n with
  | zero => exact g.acyclic_zero hI h
  | succ n =>
    intro f hf
    refine ⟨⟨g.shift f.val,g.shift_support f⟩,?_⟩
    apply Subtype.ext; funext a ws
    change Bar.delta g.action (g.shift f.val) a ws = f.val a ws
    by_cases ha : a ∈ g.positive
    · let b : g.Atom := ⟨a,ha⟩
      have hz := congrFun (congrFun (congrArg Subtype.val hf) 1) (b::ws)
      change f.val (1*a) ws - Bar.internal (fun c l => f.val 1 (c::l)) b ws = 0 at hz
      rw [one_mul,sub_eq_zero] at hz
      exact (g.delta_shift_atom f.val b ws).trans hz.symm
    · have h1 : a=1 := g.unit_of_degree_zero a (fun hz => ha (Or.inl hz)) (by
        by_contra hn
        exact ha (Or.inr (Nat.pos_of_ne_zero hn)))
      subst a
      cases ws with
      | nil =>
        change 0 = f.val 1 []
        symm
        by_contra hn
        have := (f.property _ _ hn).2.2.1
        simp at this
      | cons x xs =>
        rw [Bar.delta]
        change g.shift f.val (1*x.val) xs -
          Bar.internal (fun b t => g.shift f.val 1 (b::t)) x xs = _
        simp only [one_mul,g.shift_atom,g.shift_one]
        rw [show (fun (_ : g.Atom) (_ : List g.Atom) => (0 : K)) = 0 from rfl,
          Bar.internal_zero,sub_zero]

end RollerKoszul.BasisGrading
