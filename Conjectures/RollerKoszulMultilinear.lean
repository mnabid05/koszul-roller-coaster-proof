import Conjectures.RollerKoszulWords
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

/-! Coordinate functions on words are literally the duals of tensor powers:
they extend uniquely to multilinear maps on the augmentation ideal. -/
noncomputable section
open scoped Classical BigOperators
namespace RollerKoszul

variable {K U T : Type*} [Field K] [AddCommGroup U] [Module K U] [Fintype T]

/-- Extend values on all tuples of basis vectors by multilinearity. -/
def multilinearExtension (n : ℕ) (b : Basis T K U) (f : (Fin n → T) → K) :
    MultilinearMap K (fun _ : Fin n => U) K :=
  ∑ v : Fin n → T, (MultilinearMap.mkPiRing K (Fin n) (f v)).compLinearMap
    (fun i => b.coord (v i))

theorem multilinearExtension_apply (n : ℕ) (b : Basis T K U) (f : (Fin n → T) → K)
    (v : Fin n → T) : multilinearExtension n b f (fun j => b (v j)) = f v := by
  classical
  simp only [multilinearExtension,MultilinearMap.sum_apply,MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply,Basis.coord_apply,Basis.repr_self_apply]
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ h
    obtain ⟨j,hj⟩ : ∃ j, w j ≠ v j := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (Ne.symm hj)),zero_smul]
  · simp

/-- Prescribing a homogeneous word cochain on a basis gives one and only one
multilinear form on the underlying module in this homological degree. -/
theorem existsUnique_multilinear (n : ℕ) (b : Basis T K U) (f : (Fin n → T) → K) :
    ∃! F : MultilinearMap K (fun _ : Fin n => U) K, ∀ v, F (fun j => b (v j)) = f v :=
  ⟨multilinearExtension n b f,multilinearExtension_apply n b f,fun _ h =>
    b.ext_multilinear (fun v => (h v).trans (multilinearExtension_apply n b f v).symm)⟩

namespace BasisGrading
variable {S : Type*} [MonoidWithZero S] (g : BasisGrading S)

/-- Index type for an actual basis of the augmentation ideal, omitting the zero letter. -/
abbrev PositiveIndex := {s : S // s≠0 ∧ 0<g.degree s}

def toAtom (s : g.PositiveIndex) : g.Atom := ⟨s.val,Or.inr s.property.2⟩

def indexWord {n : ℕ} (v : Fin n → g.PositiveIndex) : List g.Atom := List.ofFn (g.toAtom ∘ v)

private theorem every_word {n : ℕ} (w : List g.Atom) (hw : w.length=n) (hz : 0 ∉ w.map Subtype.val) :
    ∃ v : Fin n → g.PositiveIndex, g.indexWord v = w := by
  subst n
  let v (i : Fin w.length) : g.PositiveIndex := by
    let a := w.get i
    have ha : a.val ≠ 0 := by
      intro h
      exact hz (h ▸ List.mem_map_of_mem (f:=Subtype.val) (w.get_mem i))
    exact ⟨a.val,ha,(show a.val = 0 ∨ 0 < g.degree a.val from a.property).resolve_left ha⟩
  exact ⟨v,(show List.ofFn w.get=w from List.ofFn_get w)⟩

theorem word_ext {n d : ℕ} {f h : g.wordCochains K n d}
    (H : ∀ v : Fin n → g.PositiveIndex, f.val (g.indexWord v) = h.val (g.indexWord v)) : f=h := by
  apply Subtype.ext; funext w
  by_cases hw : w.length=n ∧ 0 ∉ w.map Subtype.val
  · obtain ⟨v,rfl⟩ := g.every_word w hw.1 hw.2
    exact H v
  · have vanish (z : g.wordCochains K n d) : z.val w=0 := by
      by_contra hn
      obtain ⟨hz,hl,_⟩ := z.property w hn
      exact hw ⟨hl,hz⟩
    rw [vanish f,vanish h]

/-- A reduced homogeneous bar cochain with coefficients in the ground field is
uniquely realized as a multilinear form on any module with the indicated positive basis. -/
theorem existsUnique_form [Fintype g.PositiveIndex] (b : Basis g.PositiveIndex K U)
    {n d : ℕ} (f : g.wordCochains K n d) :
    ∃! F : MultilinearMap K (fun _ : Fin n => U) K,
      ∀ v, F (fun j => b (v j)) = f.val (g.indexWord v) :=
  existsUnique_multilinear n b _

theorem indexWord_injective {n : ℕ} :
    Function.Injective (g.indexWord (n := n)) := by
  intro a b h
  have hm := List.ofFn_injective h
  exact funext fun i => Subtype.ext (congrArg (fun x : g.Atom => x.val) (congrFun hm i))

/-- Forms of internal degree d have support on tuples whose degrees sum to d. -/
def formSpace [Fintype g.PositiveIndex] (b : Basis g.PositiveIndex K U) (n d : ℕ) :=
  {F : MultilinearMap K (fun _ : Fin n => U) K //
    ∀ v, F (fun i => b (v i)) ≠ 0 → g.wordDegree (g.indexWord v) = d}

private theorem indexWord_noZero {n : ℕ} (v : Fin n → g.PositiveIndex) :
    0 ∉ (g.indexWord v).map Subtype.val := by
  intro h
  obtain ⟨a,ha,he⟩ := List.mem_map.mp h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact (v i).property.1 he

/-- Isomorphism of underlying types between the normalized homogeneous bar cochains
and *all* homogeneous multilinear forms. -/
noncomputable def formEquiv [Fintype g.PositiveIndex] (b : Basis g.PositiveIndex K U) (n d : ℕ) :
    g.wordCochains K n d ≃ g.formSpace b n d := by
  classical
  let extend (f : g.wordCochains K n d) : g.formSpace b n d :=
    ⟨multilinearExtension n b (fun v => f.val (g.indexWord v)), by
      intro v h
      rw [multilinearExtension_apply] at h
      exact (f.property _ h).2.2⟩
  let restrict (F : g.formSpace b n d) (w : List g.Atom) :=
    if h : ∃ v : Fin n → g.PositiveIndex, g.indexWord v = w
    then F.val (fun i => b (h.choose i)) else 0
  have hr (F : g.formSpace b n d) (v : Fin n → g.PositiveIndex) :
      restrict F (g.indexWord v) = F.val (fun i => b (v i)) := by
    have he : ∃ v' : Fin n → g.PositiveIndex, g.indexWord v' = g.indexWord v := ⟨v,rfl⟩
    simp only [restrict,dif_pos he,g.indexWord_injective he.choose_spec]
  refine {
    toFun := extend
    invFun := fun F => ⟨restrict F,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro w h
    by_cases he : ∃ v : Fin n → g.PositiveIndex, g.indexWord v = w
    · obtain ⟨v,rfl⟩ := he
      rw [hr] at h
      exact ⟨g.indexWord_noZero v,by simp [indexWord],F.property v h⟩
    · exact False.elim (h (by simp only [restrict,dif_neg he]))
  · intro f
    apply g.word_ext
    intro v
    exact (hr (extend f) v).trans (multilinearExtension_apply n b _ v)
  · intro F
    apply Subtype.ext
    apply b.ext_multilinear
    intro v
    exact (multilinearExtension_apply n b _ v).trans (hr F v)

theorem formEquiv_apply [Fintype g.PositiveIndex] (b : Basis g.PositiveIndex K U) {n d : ℕ}
    (f : g.wordCochains K n d) (v : Fin n → g.PositiveIndex) :
    (g.formEquiv b n d f).val (fun i => b (v i)) = f.val (g.indexWord v) :=
  multilinearExtension_apply n b _ v

end BasisGrading
end RollerKoszul
