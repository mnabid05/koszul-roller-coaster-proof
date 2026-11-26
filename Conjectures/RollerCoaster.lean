import Conjectures.RollerRealization
import Conjectures.RollerOrder

/-! Hilbert coefficients of the Artinian reduction for a colored whiskering.
The identification with the shellable-complex algebra is the published theorem
of D'Alì and Venturello used in the accompanying proof. -/
namespace RollerCoaster

open Finset RollerRealization

/-- Count k-faces after colored whiskering. With i unused colors, a face of
size p-i extends to size k by omitting exactly p-k of those unused colors. -/
def whiskeredFaces (p : ℕ) (bs : List Block) (k : ℕ) : ℕ :=
  if k ≤ p then p.choose k +
    ∑ i ∈ range p, faceCount (p-i) bs * i.choose (p-k) else 0

/-- The symmetrized face count in Hilbert degree k. -/
def hilbert (p : ℕ) (bs : List Block) (k : ℕ) : ℕ :=
  whiskeredFaces p bs k + whiskeredFaces p bs (p+1-k)

theorem hilbert_eq_profile (p k : ℕ) (bs : List Block) (hk : k<p) :
    (hilbert p bs (k+1) : ℚ) = (p+1).choose (k+1) +
      RollerOrder.profile p (fun i => faceCount (p-i) bs) k := by
  rw [hilbert, show p+1-(k+1)=p-k by omega]
  simp only [whiskeredFaces, if_pos (show k+1≤p by omega), if_pos (Nat.sub_le p k),
    Nat.sub_sub_self (show k≤p by omega), Nat.choose_symm (show k≤p by omega),
    Nat.choose_succ_succ, Nat.cast_add, Nat.cast_sum, Nat.cast_mul,
    RollerOrder.profile, RollerOrder.entry, mul_add, sum_add_distrib]
  rw [show p-1-k=p-(k+1) by omega]
  ring

/-- Every permutation is realized by the symmetrized face counts of an
admissible finite multipartite construction in the indicated socle degree. -/
theorem every_order (d : ℕ) (hd : 3≤d) (π : Equiv.Perm (Fin (d/2))) :
    ∃ bs : List Block, (∀ b ∈ bs, Admissible (d-1) b) ∧
      StrictMono (fun k : Fin (d/2) => hilbert (d-1) bs ((π k).val+1)) := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  simp only [Nat.succ_sub_one]
  let stretch : ℚ := (2:ℕ)^(p+1)
  let y (k : Fin ((p+1)/2)) : ℚ := stretch * (π.symm k).val
  obtain ⟨w,c,hw,he⟩ := RollerOrder.positive_profile p y
  obtain ⟨M,bs,hM,hbs,hq⟩ := realize p (fun s => w (p-s))
    (fun s hs hsp => hw _ (by omega))
  have hface (i : ℕ) (hi : i<p) :
      (faceCount (p-i) bs : ℚ) = M * w i := by
    simpa only [Nat.sub_sub_self hi.le] using hq (p-i) (by omega) (by omega)
  have value (k : Fin ((p+1)/2)) : (hilbert p bs ((π k).val+1) : ℚ) =
      (p+1).choose ((π k).val+1) + M * (c + stretch*k.val) := by
    have hrow := (π k).isLt
    rw [hilbert_eq_profile _ _ _ (by omega)]
    congr 1
    calc
      _ = (∑ i ∈ range p, (M:ℚ) * (w i * RollerOrder.entry p (π k) i)) := by
          apply sum_congr rfl
          intro i hi
          change (faceCount (p-i) bs : ℚ) * _ = _
          rw [hface i (mem_range.mp hi), mul_assoc]
      _ = M * RollerOrder.profile p w (π k) := by rw [← mul_sum]; rfl
      _ = _ := by rw [he]; simp [y]
  refine ⟨bs,hbs,?_⟩
  intro i j hij
  have step : (i.val:ℚ) + 1 ≤ j.val := by
    exact_mod_cast (show i.val+1 ≤ j.val from hij)
  have hpos : (1:ℚ) ≤ M := by exact_mod_cast hM
  have hs : 0 ≤ stretch := by dsimp [stretch]; positivity
  have gap := mul_le_mul_of_nonneg_left step hs
  have biggap := mul_le_mul_of_nonneg_left gap (show (0:ℚ) ≤ M by positivity)
  have gap_one := mul_le_mul_of_nonneg_right hpos hs
  have hbound : ((p+1).choose ((π i).val+1) : ℚ) < stretch := by
    dsimp [stretch]
    exact_mod_cast Nat.choose_le_two_pow (p+1) ((π i).val+1) (Nat.succ_pos _)
  have hlo : (0:ℚ) ≤ (p+1).choose ((π j).val+1) := by positivity
  suffices (hilbert p bs ((π i).val+1) : ℚ) < hilbert p bs ((π j).val+1) by
    exact_mod_cast this
  rw [value i, value j]
  nlinarith only [biggap, gap_one, hbound, hlo]

end RollerCoaster
