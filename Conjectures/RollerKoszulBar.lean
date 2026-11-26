import Conjectures.RollerKoszulHomology
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Tactic.Abel

/-! The normalized dual bar differential on words in a graded multiplicative basis.
Zero is allowed as a formal letter and all cochains vanish on words containing it. -/

namespace RollerKoszul

universe u v

namespace Bar

variable {S A : Type*} [Semigroup S] {K : Type*} [AddCommGroup K]

/-- The normalized bar differential when the first slot is also an augmentation letter. -/
def internal : (S → List S → K) → S → List S → K
  | _, _, [] => 0
  | f, a, x::xs => f (a*x) xs - internal (fun b ws => f a (b::ws)) x xs

/-- The first multiplication is the action of the first augmentation letter on the module. -/
def delta (act : A → S → A) (f : A → List S → K) (a : A) : List S → K
  | [] => 0
  | x::xs => f (act a x) xs - internal (fun b ws => f a (b::ws)) x xs

private theorem internal_eq_delta (f : S → List S → K) (a : S) (l : List S) :
    internal f a l = delta (·*·) f a l := by cases l <;> rfl

theorem internal_congr (l : List S) (f g : S → List S → K)
    (h : ∀ a ws, ws.length = l.length - 1 → f a ws = g a ws) :
    ∀ a, internal f a l = internal g a l := by
  induction l generalizing f g with
  | nil => simp [internal]
  | cons x xs ih =>
    intro a
    rw [internal, internal, h (a*x) xs (by simp)]
    congr 1
    cases xs with
    | nil => rfl
    | cons y ys =>
      apply ih
      intro b ws hw
      exact h a (b::ws) (by simp_all)

theorem internal_add (l : List S) (f g : S → List S → K) (a : S) :
    internal (f+g) a l = internal f a l + internal g a l := by
  induction l generalizing f g a with
  | nil => simp [internal]
  | cons x xs ih =>
    rw [internal, internal, internal]
    change f (a*x) xs + g (a*x) xs -
      internal ((fun b ws => f a (b::ws))+(fun b ws => g a (b::ws))) x xs = _
    rw [ih]; abel

theorem internal_sub (l : List S) (f g : S → List S → K) (a : S) :
    internal (f-g) a l = internal f a l - internal g a l := by
  induction l generalizing f g a with
  | nil => simp [internal]
  | cons x xs ih =>
    rw [internal, internal, internal]
    change f (a*x) xs - g (a*x) xs -
      internal ((fun b ws => f a (b::ws))-(fun b ws => g a (b::ws))) x xs = _
    rw [ih]; abel

theorem internal_natural (act : A → S → A) (assoc : ∀ a b c, act (act a b) c = act a (b*c))
    (f : A → List S → K) (a : A) (x : S) (l : List S) :
    internal (fun b => f (act a b)) x l = delta act f (act a x) l := by
  cases l with
  | nil => rfl
  | cons y ys => simp only [internal, delta, assoc]

theorem internal_sq (l : List S) (f : S → List S → K) (a : S) :
    internal (internal f) a l = 0 := by
  induction l generalizing f a with
  | nil => rfl
  | cons x xs ih =>
    rw [internal]
    have h : (fun b ws => internal f a (b::ws)) =
        (fun b ws => f (a*b) ws) - internal (fun b ws => f a (b::ws)) := rfl
    rw [h, internal_sub, ih, sub_zero, internal_natural (·*·) mul_assoc f a x xs,
      ← internal_eq_delta, sub_self]

theorem delta_sq (act : A → S → A) (assoc : ∀ a b c, act (act a b) c = act a (b*c))
    (f : A → List S → K) (a : A) (l : List S) : delta act (delta act f) a l = 0 := by
  cases l with
  | nil => rfl
  | cons x xs =>
    rw [delta]
    have h : (fun b ws => delta act f a (b::ws)) =
        (fun b ws => f (act a b) ws) - internal (fun b ws => f a (b::ws)) := rfl
    rw [h, internal_sub, internal_sq, sub_zero]
    exact sub_eq_zero.mpr (internal_natural act assoc f a x xs).symm

theorem delta_add (act : A → S → A) (f g : A → List S → K) (a : A) (l : List S) :
    delta act (f+g) a l = delta act f a l + delta act g a l := by
  cases l with
  | nil => simp [delta]
  | cons x xs =>
    rw [delta, delta, delta]
    change f (act a x) xs + g (act a x) xs -
      internal ((fun b ws => f a (b::ws))+(fun b ws => g a (b::ws))) x xs = _
    rw [internal_add]; abel

theorem internal_zero (a : S) (l : List S) : internal (0 : S → List S → K) a l = 0 := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [internal]
    change 0 - internal (0 : S → List S → K) x xs = 0
    rw [ih,sub_zero]

theorem delta_zero (act : A → S → A) (a : A) (l : List S) :
    delta act (0 : A → List S → K) a l = 0 := by
  cases l with
  | nil => rfl
  | cons x xs =>
    rw [delta]
    change 0 - internal (0 : S → List S → K) x xs = 0
    rw [internal_zero,sub_zero]

end Bar

/-- Degrees on a monoid-with-zero comprising a multiplicative basis and its zero product. -/
structure BasisGrading (A : Type*) [MonoidWithZero A] where
  degree : A → ℕ
  one_degree : degree 1 = 0
  unit_of_degree_zero : ∀ a, a ≠ 0 → degree a = 0 → a = 1
  product_degree : ∀ a b, a*b ≠ 0 → degree (a*b) = degree a + degree b

namespace BasisGrading

variable {A : Type*} [MonoidWithZero A] (g : BasisGrading A)

/-- The augmentation-ideal part of the multiplicative basis, with zero adjoined. -/
def positive : Subsemigroup A where
  carrier := {a | a = 0 ∨ 0 < g.degree a}
  mul_mem' := by
    rintro a b ha hb
    by_cases h : a*b = 0
    · exact Or.inl h
    · have ha' : a ≠ 0 := fun hh => h (hh ▸ zero_mul b)
      have hb' : b ≠ 0 := fun hh => h (hh ▸ mul_zero a)
      rcases ha with hz|ha
      · contradiction
      rcases hb with hz|hb
      · contradiction
      exact Or.inr (by rw [g.product_degree a b h]; omega)

abbrev Atom := ↥g.positive
def zeroAtom : g.Atom := ⟨0,Or.inl rfl⟩

def wordDegree (w : List g.Atom) : ℕ :=
  (w.map (fun a => g.degree a.val)).sum

@[simp] theorem wordDegree_nil : g.wordDegree [] = 0 := rfl
@[simp] theorem wordDegree_cons (a : g.Atom) (l : List g.Atom) :
    g.wordDegree (a::l) = g.degree a.val + g.wordDegree l := rfl

/-- A based right ideal including the zero product. -/
structure Closed (I : Set A) : Prop where
  zero_mem : 0 ∈ I
  mul_mem : ∀ a ∈ I, ∀ b, a*b ∈ I

end BasisGrading
end RollerKoszul
