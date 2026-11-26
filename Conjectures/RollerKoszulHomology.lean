import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Push

/-! The two inductions in the Koszul-filtration argument, carried out directly on
cocycles and coboundaries. The complexes in an exact row may have unrelated
coefficient types. Internal degree is an independent index. -/

namespace RollerKoszul

universe u

/-- Cochain groups, their differentials, and the complex identity. -/
structure Complex where
  group : ℕ → Type u
  [abelian : ∀ i, AddCommGroup (group i)]
  d : ∀ i, group i →+ group (i+1)
  d_sq : ∀ i x, d (i+1) (d i x) = 0

attribute [instance] Complex.abelian

def Boundary (C : Complex) : (i : ℕ) → C.group i → Prop
  | 0, x => x = 0
  | n+1, x => ∃ y, C.d n y = x

/-- Vanishing of cohomology in a single homological degree. -/
def AcyclicAt (C : Complex) (n : ℕ) : Prop :=
  ∀ x, C.d n x = 0 → Boundary C n x

/-- A complex-level short exact sequence, given by injectivity, exactness
in the middle, surjectivity, and the two chain-map identities. -/
structure ShortExact (X Y Z : Complex.{u}) where
  i : ∀ n, X.group n →+ Y.group n
  p : ∀ n, Y.group n →+ Z.group n
  injective : ∀ n, Function.Injective (i n)
  middle : ∀ n y, p n y = 0 ↔ ∃ x, i n x = y
  surjective : ∀ n, Function.Surjective (p n)
  di : ∀ n x, Y.d n (i n x) = i (n+1) (X.d n x)
  dp : ∀ n y, Z.d n (p n y) = p (n+1) (Y.d n y)

private theorem remove_projection {X Y Z : Complex} (s : ShortExact X Y Z)
    (n : ℕ) (y : Y.group n) (hy : Boundary Z n (s.p n y)) :
    ∃ v : Y.group n, s.p n v = 0 ∧ Y.d n v = Y.d n y := by
  cases n with
  | zero => exact ⟨y,hy,rfl⟩
  | succ n =>
    obtain ⟨z,hz⟩ := hy
    obtain ⟨w,hw⟩ := s.surjective n z
    refine ⟨y - Y.d n w, ?_, ?_⟩
    · rw [map_sub, ← s.dp, hw, hz, sub_self]
    · rw [map_sub, Y.d_sq, sub_zero]

/-- The vanishing implication for consecutive terms of the cohomology exact sequence. -/
theorem acyclic_of_shortExact {X Y Z : Complex} (s : ShortExact X Y Z) (n : ℕ)
    (hy : AcyclicAt Y (n+1)) (hz : AcyclicAt Z n) : AcyclicAt X (n+1) := by
  intro x hx
  obtain ⟨y,hdy⟩ := hy (s.i _ x) (by rw [s.di, hx, map_zero])
  have hp : Z.d n (s.p n y) = 0 := by
    rw [s.dp, hdy]
    exact (s.middle _ _).mpr ⟨x,rfl⟩
  obtain ⟨v,hv,hdv⟩ := remove_projection s n y (hz _ hp)
  obtain ⟨w,hw⟩ := (s.middle n v).mp hv
  refine ⟨w, s.injective _ ?_⟩
  rw [← s.di, hw, hdv, hdy]

/-- The rightmost module in each row is shifted up by one in internal degree.
The middle module has a strictly smaller filtration index. -/
theorem filtration_acyclic {ι : Type*} (C : ι → ℕ → Complex.{u}) (size : ι → ℕ)
    (hzero : ∀ t j, 0 < j → AcyclicAt (C t j) 0)
    (hstep : ∀ t, (∀ n j, n < j → AcyclicAt (C t j) n) ∨
      ∃ t' k, size t' < size t ∧ ∀ j, Nonempty (ShortExact (C t (j+1)) (C t' (j+1)) (C k j))) :
    ∀ n t j, n < j → AcyclicAt (C t j) n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have main : ∀ l t j, size t = l → n+1 < j → AcyclicAt (C t j) (n+1) := by
      intro l
      induction l using Nat.strong_induction_on with
      | h l prior =>
        intro t j ht hj
        rcases hstep t with direct | ⟨t', k, hlt, rows⟩
        · exact direct _ _ hj
        · cases j with
          | zero => omega
          | succ j =>
            apply acyclic_of_shortExact (rows j).some n
            · exact prior (size t') (ht ▸ hlt) t' (j+1) rfl hj
            · exact ih k j (by omega)
    exact fun t j hj => main (size t) t j rfl hj

end RollerKoszul
