import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The symmetrized Pascal columns contributed by a nonempty face after colored
whiskering and Artinian reduction can realize every ordering in the first half.
Indices in this file start at zero, so row k refers to Hilbert degree k+1. -/
namespace RollerOrder

open Finset
open scoped BigOperators

def entry (p k i : ℕ) : ℚ := (i.choose k : ℚ) + (i.choose (p-1-k) : ℚ)

def profile (p : ℕ) (w : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ i ∈ range p, w i * entry p k i

private def halfSum : ℕ → ℕ → ℚ
  | 0, _ => 0
  | p+1, k => 2 * halfSum p k + p.choose k

private lemma halfSum_sub (p k : ℕ) :
    halfSum p k - halfSum p (k+1) = p.choose (k+1) := by
  induction p with
  | zero => simp [halfSum]
  | succ p ih =>
    simp only [halfSum, Nat.choose_succ_succ, Nat.cast_add]
    linarith

private lemma halfSum_eq (p k : ℕ) :
    (∑ i ∈ range p, (2:ℚ)^(p-1-i) * i.choose k) = halfSum p k := by
  induction p with
  | zero => simp [halfSum]
  | succ p ih =>
    rw [sum_range_succ, halfSum, ← ih, mul_sum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [show p-i=(p-1-i)+1 by omega, pow_succ]
    ring

private lemma profile_flat_aux (p k : ℕ) :
    profile p (fun i => (2:ℚ)^(p-1-i)) k = halfSum p k + halfSum p (p-1-k) := by
  simp only [profile, entry, mul_add, sum_add_distrib, halfSum_eq]

/-- Positive integer weights make every interior entry equal. -/
theorem flat (p k : ℕ) (hk : k < p) :
    profile p (fun i => (2:ℚ)^(p-1-i)) k =
      profile p (fun i => (2:ℚ)^(p-1-i)) 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih (by omega)]
    simp only [profile_flat_aux]
    have a := halfSum_sub p k
    have b := halfSum_sub p (p-1-(k+1))
    have ind : p-1-(k+1)+1 = p-1-k := by omega
    rw [ind] at b
    have sym := Nat.choose_symm (show k+1≤p by omega)
    rw [show p-1-k=p-(k+1) by omega, sym] at b
    rw [show p-(k+1)=p-1-k by omega] at b
    linarith

private def block (p : ℕ) : Matrix (Fin ((p+1)/2)) (Fin ((p+1)/2)) ℚ :=
  fun k i => entry p k i

private theorem block_unit (p : ℕ) : IsUnit (block p) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_of_upperTriangular]
  · apply isUnit_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    change (k.val.choose k.val : ℚ) + (k.val.choose (p-1-k.val) : ℚ) ≠ 0
    rw [Nat.choose_self]
    positivity
  · intro i j hji
    change j.val < i.val at hji
    have hi := i.isLt
    change (j.val.choose i.val : ℚ) + (j.val.choose (p-1-i.val) : ℚ) = 0
    rw [Nat.choose_eq_zero_of_lt hji, Nat.choose_eq_zero_of_lt (show j.val<p-1-i.val by omega)]
    norm_num

private lemma signed_solution (p : ℕ) (y : Fin ((p+1)/2) → ℚ) :
    ∃ w : ℕ → ℚ, ∀ k : Fin ((p+1)/2), profile p w k = y k := by
  obtain ⟨v,hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr (block_unit p) y
  let w (i : ℕ) : ℚ := if h : i < (p+1)/2 then v ⟨i,h⟩ else 0
  refine ⟨w,?_⟩
  intro k
  have he := congrFun hv k
  change (∑ j : Fin ((p+1)/2), entry p k j * v j) = y k at he
  unfold profile
  have hmp : (p+1)/2 ≤ p := by omega
  rw [← he, ← Finset.sum_subset (s₁ := range ((p+1)/2)) (s₂ := range p)
    (Finset.range_mono hmp) (by
      intro i _ hi
      simp [w, Finset.mem_range] at hi ⊢
      omega)]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [w, i.isLt, mul_comm]

/-- For any prescribed rational entries there are strictly positive rational
weights giving those entries up to addition of the same constant in every row. -/
theorem positive_profile (p : ℕ) (y : Fin ((p+1)/2) → ℚ) :
    ∃ (w : ℕ → ℚ) (c : ℚ), (∀ i < p, 0 < w i) ∧
      ∀ k : Fin ((p+1)/2), profile p w k = c + y k := by
  obtain ⟨v,hv⟩ := signed_solution p y
  let B : ℚ := 1 + ∑ j ∈ range p, |v j|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let u (i : ℕ) : ℚ := (2:ℚ)^(p-1-i)
  refine ⟨fun i => B*u i+v i, B*profile p u 0, ?_, ?_⟩
  · intro i hi
    have hle : |v i| ≤ ∑ j ∈ range p, |v j| :=
      single_le_sum (fun j _ => abs_nonneg (v j)) (mem_range.mpr hi)
    have hOne : (1:ℚ) ≤ u i := one_le_pow₀ (by norm_num)
    have hProd := mul_le_mul_of_nonneg_left hOne hB
    have hAbs := neg_abs_le (v i)
    change 0 < B*u i+v i
    dsimp [B] at hProd ⊢
    linarith
  · intro k
    simp only [profile, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    change B * profile p u k + profile p v k = B * profile p u 0 + y k
    rw [hv, flat p k (by have := k.isLt; omega)]

end RollerOrder
