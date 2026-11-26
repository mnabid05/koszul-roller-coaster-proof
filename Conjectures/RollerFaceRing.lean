import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.StdBasis

/-! The squarefree face algebra, as an ordinary quotient of a polynomial ring.
Its monomial basis is indexed by the actual faces, including the empty face. -/

noncomputable section
open scoped BigOperators Classical
open MvPolynomial

namespace RollerFaceRing

structure Complex (V : Type*) where
  face : Finset V → Prop
  empty : face ∅
  downward : ∀ {s t}, s ⊆ t → face t → face s

variable {V : Type*} (K : Type*) [Field K] (C : Complex V)

abbrev Face := {s : Finset V // C.face s}
abbrev FaceAt (k : ℕ) := {s : Finset V // C.face s ∧ s.card = k}

def exponent (s : Finset V) : V →₀ ℕ := Finsupp.indicator s (fun _ _ => 1)

@[simp] theorem exponent_apply [DecidableEq V] (s : Finset V) (v : V) :
    exponent s v = if v ∈ s then 1 else 0 := by simp [exponent]

@[simp] theorem support_exponent (s : Finset V) : (exponent s).support = s := by
  classical
  ext v
  simp only [Finsupp.mem_support_iff, exponent_apply]
  split <;> simp_all

theorem exponent_injective : Function.Injective (exponent (V := V)) := by
  intro s t h
  simpa using congrArg Finsupp.support h

@[simp] theorem degree_exponent (s : Finset V) : (exponent s).degree = s.card := by
  classical
  simp [Finsupp.degree]

def Standard (e : V →₀ ℕ) : Prop := (∀ v, e v ≤ 1) ∧ C.face e.support

theorem standard_downward {e f : V →₀ ℕ} (hef : e ≤ f) (hf : Standard C f) :
    Standard C e := by
  refine ⟨fun v => (hef v).trans (hf.1 v), C.downward ?_ hf.2⟩
  intro v hv
  exact Finsupp.mem_support_iff.mpr (fun h => (Finsupp.mem_support_iff.mp hv)
    (Nat.le_zero.mp (h ▸ hef v)))

theorem standard_exponent {s : Finset V} (hs : C.face s) : Standard C (exponent s) := by
  refine ⟨fun v => ?_, by simpa using hs⟩
  rw [exponent_apply]
  split <;> decide

theorem exponent_support_of_standard {e : V →₀ ℕ} (h : Standard C e) :
    exponent e.support = e := by
  ext v
  simp only [exponent_apply, Finsupp.mem_support_iff]
  have := h.1 v
  split <;> omega

/-- All nonsquarefree monomials and all monomials supported on a nonface vanish. -/
def definingIdeal : Ideal (MvPolynomial V K) :=
  Ideal.span ((fun e => monomial e (1 : K)) '' {e | ¬Standard C e})

theorem mem_definingIdeal_iff (p : MvPolynomial V K) :
    p ∈ definingIdeal K C ↔ ∀ e, Standard C e → coeff e p = 0 := by
  rw [definingIdeal, mem_ideal_span_monomial_image]
  constructor
  · intro h e he
    by_contra hn
    obtain ⟨f, hf, hfe⟩ := h e (mem_support_iff.mpr hn)
    exact hf (standard_downward C hfe he)
  · intro h e he
    exact ⟨e, fun h' => (mem_support_iff.mp he) (h e h'), le_rfl⟩

abbrev Ring := MvPolynomial V K ⧸ definingIdeal K C

def faceMonomial (s : Face C) : Ring K C :=
  Ideal.Quotient.mk _ (monomial (exponent s.val) 1)

def piece (k : ℕ) : Submodule K (Ring K C) :=
  (homogeneousSubmodule V K k).map (Ideal.Quotient.mkₐ K (definingIdeal K C)).toLinearMap

theorem mem_piece_faceMonomial (s : Face C) :
    faceMonomial K C s ∈ piece K C s.val.card :=
  ⟨_, isHomogeneous_monomial _ (degree_exponent _), rfl⟩

def emptyFace : Face C := ⟨∅, C.empty⟩

@[simp] theorem faceMonomial_empty : faceMonomial K C (emptyFace C) = 1 := by
  have he : exponent (∅ : Finset V) = 0 := by ext v; simp
  simp [faceMonomial, emptyFace, he]

theorem monomial_zero_of_not_standard {e : V →₀ ℕ} (h : ¬Standard C e) :
    Ideal.Quotient.mk (definingIdeal K C) (monomial e 1) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e, h, rfl⟩)

theorem exponent_union {s t : Finset V} (h : Disjoint s t) :
    exponent (s ∪ t) = exponent s + exponent t := by
  ext v
  have hv : v ∈ s → v ∉ t := fun hs => Finset.disjoint_left.mp h hs
  by_cases hs : v ∈ s <;> by_cases ht : v ∈ t <;> simp_all

/-- Products of face monomials are determined by disjoint union. -/
theorem faceMonomial_mul (s t : Face C) :
    faceMonomial K C s * faceMonomial K C t =
      if h : Disjoint s.val t.val ∧ C.face (s.val ∪ t.val) then
        faceMonomial K C ⟨s.val ∪ t.val, h.2⟩ else 0 := by
  simp only [faceMonomial, ← map_mul, monomial_mul, one_mul]
  split
  next h => rw [exponent_union h.1]
  next h =>
    apply monomial_zero_of_not_standard
    rintro ⟨hs, ht⟩
    have hd : Disjoint s.val t.val := Finset.disjoint_left.mpr (by
      intro v vs vt
      have hv := hs v
      simp [vs,vt] at hv)
    exact h ⟨hd, by simpa only [← exponent_union hd, support_exponent] using ht⟩

theorem coeff_eq_of_project_eq {p q : MvPolynomial V K}
    (he : Ideal.Quotient.mk (definingIdeal K C) p = Ideal.Quotient.mk _ q)
    {e : V →₀ ℕ} (hs : Standard C e) : coeff e p = coeff e q := by
  have hh := (mem_definingIdeal_iff K C _).mp (Ideal.Quotient.eq.mp he) e hs
  simpa only [coeff_sub, sub_eq_zero] using hh

variable [Fintype V]

instance faceFintype : Fintype (Face C) := Fintype.ofFinite _
instance faceAtFintype (k : ℕ) : Fintype (FaceAt C k) := Fintype.ofFinite _

private def representative : (Face C → K) →ₗ[K] MvPolynomial V K :=
  ∑ s : Face C, (monomial (exponent s.val)).comp (LinearMap.proj s)

private theorem representative_eq (f : Face C → K) :
    representative K C f = ∑ s : Face C, monomial (exponent s.val) (f s) := by
  simp [representative, LinearMap.sum_apply]

private theorem representative_coeff (f : Face C → K) (s : Face C) :
    coeff (exponent s.val) (representative K C f) = f s := by
  rw [representative_eq, coeff_sum, Finset.sum_eq_single s]
  · simp
  · intro a _ ha
    rw [coeff_monomial, if_neg (fun e => ha (Subtype.ext (exponent_injective e)))]
  · simp

private def fromCoordinates : (Face C → K) →ₗ[K] Ring K C :=
  (Ideal.Quotient.mkₐ K (definingIdeal K C)).toLinearMap.comp (representative K C)

def coordinates : Ring K C ≃ₗ[K] (Face C → K) := by
  refine (LinearEquiv.ofBijective (fromCoordinates K C) ⟨?_, ?_⟩).symm
  · intro f g h
    funext s
    simpa only [representative_coeff] using
      coeff_eq_of_project_eq K C h (standard_exponent C s.property)
  · intro v
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective v
    refine ⟨fun s => coeff (exponent s.val) p, Ideal.Quotient.eq.mpr ?_⟩
    apply (mem_definingIdeal_iff K C _).mpr
    intro e he
    have h := representative_coeff K C (fun s => coeff (exponent s.val) p)
      ⟨e.support, he.2⟩
    simpa only [coeff_sub, sub_eq_zero, exponent_support_of_standard C he] using h

theorem coordinates_mk (p : MvPolynomial V K) (s : Face C) :
    coordinates K C (Ideal.Quotient.mk _ p) s = coeff (exponent s.val) p := by
  have h : fromCoordinates K C (coordinates K C (Ideal.Quotient.mk _ p)) =
    Ideal.Quotient.mk _ p := (coordinates K C).symm_apply_apply _
  simpa only [representative_coeff] using coeff_eq_of_project_eq K C h
    (standard_exponent C s.property)

@[simp] theorem coordinates_faceMonomial (s t : Face C) :
    coordinates K C (faceMonomial K C s) t = if s = t then 1 else 0 := by
  rw [faceMonomial, coordinates_mk, coeff_monomial]
  simp [exponent_injective.eq_iff, Subtype.ext_iff]

def basis : Basis (Face C) K (Ring K C) := (Pi.basisFun K (Face C)).map (coordinates K C).symm

@[simp] theorem basis_apply (s : Face C) : basis K C s = faceMonomial K C s := by
  apply (coordinates K C).injective
  ext t
  simp [basis, Pi.basisFun_apply, Pi.single_apply, eq_comm]

end RollerFaceRing
