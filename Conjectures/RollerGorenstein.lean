import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.Basic

/-! The idealization of a commutative algebra by its vector-space dual. -/
namespace RollerGorenstein

noncomputable section

variable (K B : Type*) [Field K] [CommRing B] [Algebra K B]

/-- The regular dual action is precomposition with multiplication in the algebra. -/
private def dualModule : Module B (Module.Dual K B) where
  smul b f := f.comp (LinearMap.mulLeft K b)
  one_smul f := by ext c; change f (1*c) = f c; rw [one_mul]
  mul_smul a b f := by ext c; change f ((a*b)*c) = f (b*(a*c)); rw [mul_assoc,mul_left_comm]
  smul_add a f g := by ext c; rfl
  smul_zero a := by ext c; rfl
  add_smul a b f := by ext c; change f ((a+b)*c) = f (a*c) + f (b*c); rw [add_mul,map_add]
  zero_smul f := by ext c; change f (0*c) = 0; rw [zero_mul,map_zero]

attribute [local instance] dualModule

private instance dualOpModule : Module Bᵐᵒᵖ (Module.Dual K B) :=
  Module.compHom _ (RingEquiv.toOpposite B).symm.toRingHom

private instance dualCentral : IsCentralScalar B (Module.Dual K B) := ⟨fun _ _ => rfl⟩

private instance dualTower : IsScalarTower K B (Module.Dual K B) where
  smul_assoc t b f := by
    ext c
    change f ((t • b)*c) = t • f (b*c)
    rw [smul_mul_assoc,map_smul]

private instance dualOpTower : IsScalarTower K Bᵐᵒᵖ (Module.Dual K B) where
  smul_assoc t b f := by
    ext c
    change f ((t • b.unop)*c) = t • f (b.unop*c)
    rw [smul_mul_assoc,map_smul]

/-- The idealization B ⋉ B*, with the regular dual B-action on its square-zero summand. -/
def Idealization := TrivSqZeroExt B (Module.Dual K B)

instance : CommRing (Idealization K B) := inferInstanceAs (CommRing (TrivSqZeroExt B (Module.Dual K B)))
instance : Algebra K (Idealization K B) := inferInstanceAs (Algebra K (TrivSqZeroExt B (Module.Dual K B)))

/-- Forget multiplication to recover the direct sum of the algebra and its dual. -/
def coordinates : Idealization K B ≃ₗ[K] B × Module.Dual K B where
  __ := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two components of multiplication, evaluated on a test vector in the dual component. -/
theorem mul_fst (x y : Idealization K B) : (x*y).1 = x.1*y.1 := rfl

theorem mul_snd (x y : Idealization K B) (b : B) :
    (x*y).2 b = y.2 (x.1*b) + x.2 (y.1*b) := rfl

/-- The functional reads the dual component at the multiplicative identity. -/
def trace : Idealization K B →ₗ[K] K where
  toFun x := x.2 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trace_mul (x y : Idealization K B) :
    trace K B (x*y) = y.2 x.1 + x.2 y.1 := by
  change (x*y).2 1 = _
  simp [mul_snd]

/-- The functional applied to a product, as a linear map into the vector-space dual. -/
def pairing : Idealization K B →ₗ[K] Module.Dual K (Idealization K B) where
  toFun x := (trace K B).comp (LinearMap.mulLeft K x)
  map_add' x y := by ext z; simp [add_mul]
  map_smul' t x := by ext z; simp [smul_mul_assoc]

theorem pairing_injective : Function.Injective (pairing K B) := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro x hx
  have h (y : Idealization K B) : y.2 x.1+x.2 y.1 = 0 := by
    rw [← trace_mul]
    exact LinearMap.congr_fun hx y
  have hf : x.1=0 := (Module.forall_dual_apply_eq_zero_iff K x.1).mp fun f => by
    simpa using h (0,f)
  have hs : x.2=0 := by
    ext b
    simpa using h (b,0)
  exact Prod.ext hf hs

instance [FiniteDimensional K B] : FiniteDimensional K (Idealization K B) :=
  Module.Finite.equiv (coordinates K B).symm

theorem finrank_idealization [FiniteDimensional K B] :
    Module.finrank K (Idealization K B) = 2 * Module.finrank K B := by
  rw [(coordinates K B).finrank_eq,Module.finrank_prod,Subspace.dual_finrank_eq,two_mul]

/-- The Frobenius pairing is perfect over every field. -/
def frobeniusEquiv [FiniteDimensional K B] :
    Idealization K B ≃ₗ[K] Module.Dual K (Idealization K B) :=
  LinearEquiv.ofBijective (pairing K B) ⟨pairing_injective K B,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K:=K) (V:=Idealization K B)).symm).1 (pairing_injective K B)⟩

theorem frobeniusEquiv_apply [FiniteDimensional K B] (x y : Idealization K B) :
    frobeniusEquiv K B x y = trace K B (x*y) := rfl

instance [FiniteDimensional K B] : IsArtinianRing (Idealization K B) :=
  isArtinian_of_tower K inferInstance

/-- Projection of the idealization to its algebra summand. -/
def projection : Idealization K B →ₐ[K] B :=
  TrivSqZeroExt.fstHom K B (Module.Dual K B)

theorem isUnit_iff_fst (x : Idealization K B) : IsUnit x ↔ IsUnit x.1 :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst

instance [Nontrivial B] : Nontrivial (Idealization K B) :=
  inferInstanceAs (Nontrivial (TrivSqZeroExt B (Module.Dual K B)))

instance [IsLocalRing B] : IsLocalRing (Idealization K B) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    have e := congrArg (projection K B) h
    change a.1+b.1=(1:B) at e
    exact (IsLocalRing.isUnit_or_isUnit_of_add_one e).imp
      (isUnit_iff_fst K B a).mpr (isUnit_iff_fst K B b).mpr

end
end RollerGorenstein
