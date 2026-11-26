import Conjectures.RollerKoszulBar

namespace RollerKoszul

namespace Bar

/-- Contract two consecutive entries to their product. -/
inductive Merge {S : Type*} [Mul S] : List S → List S → Prop
  | here (x y : S) (l : List S) : Merge (x::y::l) ((x*y)::l)
  | there (x : S) {l t : List S} : Merge l t → Merge (x::l) (x::t)

theorem Merge.maps {S T : Type*} [Mul S] [Mul T] (v : S → T)
    (h : ∀ a b, v (a*b) = v a*v b) {l t : List S} (m : Merge l t) :
    Merge (l.map v) (t.map v) := by
  induction m with
  | here x y l => simpa only [List.map_cons, h] using Merge.here (v x) (v y) (l.map v)
  | there x m ih => exact Merge.there _ ih

variable {S A : Type*} [Semigroup S] {K : Type*} [AddCommGroup K]

theorem internal_support {f : S → List S → K} {a : S} {l : List S}
    (h : internal f a l ≠ 0) : ∃ b ws, Merge (a::l) (b::ws) ∧ f b ws ≠ 0 := by
  induction l generalizing a f with
  | nil => exact False.elim (h rfl)
  | cons x xs ih =>
    by_cases hf : f (a*x) xs = 0
    · have h' : internal (fun b ws => f a (b::ws)) x xs ≠ 0 := by
        intro hz
        apply h
        simp [internal, hf, hz]
      obtain ⟨b,ws,hm,hb⟩ := ih h'
      exact ⟨a,b::ws,Merge.there a hm,hb⟩
    · exact ⟨a*x,xs,Merge.here a x xs,hf⟩

end Bar

namespace BasisGrading
variable {A : Type*} [MonoidWithZero A] (g : BasisGrading A)
variable {K : Type*} [AddCommGroup K]

def action (a : A) (b : g.Atom) := a * b.val

theorem delta_support {f : A → List g.Atom → K} {a : A} {l : List g.Atom}
    (h : Bar.delta g.action f a l ≠ 0) : ∃ b ws,
    Bar.Merge (a::l.map Subtype.val) (b::ws.map Subtype.val) ∧ f b ws ≠ 0 := by
  cases l with
  | nil => exact False.elim (h rfl)
  | cons x xs =>
    by_cases hf : f (g.action a x) xs = 0
    · have h' : Bar.internal (fun b ws => f a (b::ws)) x xs ≠ 0 := by
        intro hz
        apply h
        simp [Bar.delta, hf, hz]
      obtain ⟨b,ws,hm,hb⟩ := Bar.internal_support h'
      exact ⟨a,b::ws,Bar.Merge.there a (hm.maps Subtype.val (fun _ _ => rfl)),hb⟩
    · exact ⟨g.action a x,xs,Bar.Merge.here a x.val _,hf⟩

private theorem merge_length {l t : List A} (h : Bar.Merge l t) : l.length = t.length+1 := by
  induction h <;> simp_all

private theorem merge_zero {l t : List A} (h : Bar.Merge l t) : 0 ∉ t → 0 ∉ l := by
  induction h with
  | here a b l =>
    simp only [List.mem_cons, not_or]
    rintro ⟨hp,hl⟩
    exact ⟨fun e => hp (by rw [← e,zero_mul]),fun e => hp (by rw [← e,mul_zero]),hl⟩
  | there a m ih => simp only [List.mem_cons,not_or]; exact fun ⟨ha,hz⟩ => ⟨ha,ih hz⟩

private theorem merge_degree {l t : List A} (h : Bar.Merge l t) (ht : 0 ∉ t) :
    (l.map g.degree).sum = (t.map g.degree).sum := by
  induction h with
  | here a b l =>
    have hab : a*b ≠ 0 := by
      intro e
      exact ht (by simp [e])
    simp [g.product_degree a b hab,Nat.add_assoc]
  | there a m ih => simp only [List.mem_cons,not_or] at ht; simpa using ih ht.2

private theorem merge_ideal {I : Set A} (hI : Closed I) {a b : A} {l t : List A}
    (h : Bar.Merge (a::l) (b::t)) (hb : b ∉ I) : a ∉ I := by
  cases h with
  | here a y l => exact fun ha => hb (hI.mul_mem _ ha _)
  | there a hm => exact hb

/-- The basis words in one homogeneous term of the normalized bar resolution for A/I. -/
def Valid (I : Set A) (n d : ℕ) (a : A) (ws : List g.Atom) : Prop :=
  a ∉ I ∧ 0 ∉ ws.map Subtype.val ∧ ws.length = n ∧ g.degree a + g.wordDegree ws = d

theorem valid_transfer {I : Set A} (hI : Closed I) {a b : A} {l ws : List g.Atom}
    {n d : ℕ} (m : Bar.Merge (a::l.map Subtype.val) (b::ws.map Subtype.val))
    (hw : g.Valid I n d b ws) : g.Valid I (n+1) d a l := by
  obtain ⟨hb,hz,hl,hd⟩ := hw
  have hn : 0 ∉ b::ws.map Subtype.val := by
    simp only [List.mem_cons, not_or]
    exact ⟨fun e => hb (e ▸ hI.zero_mem),hz⟩
  have hn' := merge_zero m hn
  have hlen := merge_length m
  have hdeg := g.merge_degree m hn
  simp only [List.map_cons,List.sum_cons,List.map_map] at hdeg
  exact ⟨merge_ideal hI m hb,fun e => hn' (List.mem_cons_of_mem _ e),
    by simpa [hl] using hlen,hdeg.trans hd⟩

/-- Coefficients are extended by zero off their indicated homogeneous basis. -/
def cochains (K : Type*) [AddCommGroup K] (I : Set A) (n d : ℕ) :
    AddSubgroup (A → List g.Atom → K) where
  carrier := {f | ∀ a ws, f a ws ≠ 0 → g.Valid I n d a ws}
  zero_mem' := by intro a ws h; exact False.elim (h rfl)
  add_mem' := by
    intro f h hf hh a ws hsum
    by_cases h' : f a ws = 0
    · apply hh a ws
      intro h''
      exact hsum (by simp [h',h''])
    · exact hf a ws h'
  neg_mem' := by
    intro f hf a ws hsum
    apply hf a ws
    intro h
    exact hsum (by simp [h])

def differential {I : Set A} (hI : Closed I) (n d : ℕ) :
    g.cochains K I n d →+ g.cochains K I (n+1) d where
  toFun f := ⟨Bar.delta g.action f.val, by
    intro a l h
    obtain ⟨b,ws,hm,hb⟩ := g.delta_support h
    exact g.valid_transfer hI hm (f.property b ws hb)⟩
  map_zero' := Subtype.ext (funext fun a => funext fun l => Bar.delta_zero g.action a l)
  map_add' x y := Subtype.ext (funext fun a => funext fun l => Bar.delta_add g.action x.val y.val a l)

def barComplex (K : Type*) [AddCommGroup K] (I : Set A) (hI : Closed I) (d : ℕ) : Complex where
  group n := g.cochains K I n d
  d n := g.differential hI n d
  d_sq _ f := Subtype.ext (funext fun a => funext fun l =>
    Bar.delta_sq g.action (fun a b c => mul_assoc a b.val c.val) f.val a l)

end BasisGrading
end RollerKoszul
