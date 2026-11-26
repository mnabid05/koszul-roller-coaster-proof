import Conjectures.RollerFaceMonoid
import Conjectures.RollerKoszulBar

/-! Internal degrees on the multiplicative face basis of the idealization. -/
noncomputable section
open scoped Classical
open RollerFaceRing

namespace RollerFaceMonoid
variable {V : Type*} (C : Complex V)

def degree (d : ℕ) : Term C → ℕ
  | .killed => 0
  | .primal s => s.val.card
  | .dual s => d - s.val.card

@[simp] theorem degree_one (d : ℕ) : degree C d 1 = 0 := rfl
@[simp] theorem degree_zero (d : ℕ) : degree C d 0 = 0 := rfl

variable [Fintype V]

theorem degree_mul_of_ne_zero (d : ℕ) (bound : ∀ s : Face C, s.val.card ≤ d)
    (s t : Term C) (hn : s*t ≠ 0) : degree C d (s*t) = degree C d s + degree C d t := by
  have mixed (a b : Face C) (hne : Term.primal a * Term.dual b ≠ (0 : Term C)) :
      degree C d (Term.primal a * Term.dual b) = degree C d (.primal a) + degree C d (.dual b) := by
    rw [primal_mul_dual] at hne ⊢
    split at hne
    next h =>
      rw [if_pos h]
      change d-(b.val \ a.val).card = a.val.card + (d-b.val.card)
      rw [Finset.card_sdiff h]
      have ha := Finset.card_le_card h
      have hb := bound b
      omega
    next => contradiction
  cases s with
  | killed => exact False.elim (hn (zero_mul t))
  | primal a =>
    cases t with
    | killed => exact False.elim (hn (mul_zero _))
    | primal b =>
      rw [primal_mul_primal] at hn ⊢
      split at hn
      next h =>
        rw [dif_pos h]
        exact Finset.card_union_of_disjoint h.1
      next => contradiction
    | dual b => exact mixed _ _ hn
  | dual a =>
    cases t with
    | killed => exact False.elim (hn (mul_zero _))
    | primal b =>
      rw [mul_comm] at hn ⊢
      exact (mixed _ _ hn).trans (Nat.add_comm ..)
    | dual b => exact False.elim (hn (dual_mul_dual ..))

/-- The internal grading used by the normalized bar construction. -/
def barGrading (d : ℕ) (bound : ∀ s : Face C, s.val.card < d) :
    RollerKoszul.BasisGrading (Term C) where
  degree := degree C d
  one_degree := degree_one C d
  product_degree := degree_mul_of_ne_zero C d (fun s => (bound s).le)
  unit_of_degree_zero a ha hd := by
    cases a with
    | killed => exact False.elim (ha rfl)
    | primal s =>
      change s.val.card = 0 at hd
      exact congrArg Term.primal (Subtype.ext (Finset.card_eq_zero.mp hd))
    | dual s =>
      change d-s.val.card=0 at hd
      have := bound s
      omega

end RollerFaceMonoid
