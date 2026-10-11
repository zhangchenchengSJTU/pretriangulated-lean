import PretriangulatedV2.FiniteModuleCategory
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
Actual vector-space duals of finite modules, with the contragredient action
of the commutative coefficient algebra. Scalar actions and transpose maps
are proved explicitly, before using duality to construct injective objects.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

namespace PretriangulatedV2.FiniteModuleCategory

universe u

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [FiniteDimensional k A]

/-- A type synonym to install the contragredient algebra action. -/
def Dual (M : FGModuleCat.{u} A) := Module.Dual k M

instance dualFunLike (M : FGModuleCat.{u} A) : FunLike (Dual (k := k) M) M k :=
  inferInstanceAs (FunLike (Module.Dual k M) M k)

omit [FiniteDimensional k A] in
@[ext]
theorem dual_ext {M : FGModuleCat.{u} A} {φ ψ : Dual (k := k) M}
    (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h

instance dualAddCommGroup (M : FGModuleCat.{u} A) : AddCommGroup (Dual (k := k) M) :=
  inferInstanceAs (AddCommGroup (Module.Dual k M))

instance dualFieldModule (M : FGModuleCat.{u} A) : Module k (Dual (k := k) M) :=
  inferInstanceAs (Module k (Module.Dual k M))

/-- Precompose a functional with multiplication by an algebra element. -/
def dualSmul (M : FGModuleCat.{u} A) (a : A) (φ : Dual (k := k) M) :
    Dual (k := k) M := φ.comp (DistribSMul.toLinearMap k M a)

instance dualAlgebraModule (M : FGModuleCat.{u} A) : Module A (Dual (k := k) M) where
  smul := dualSmul M
  one_smul φ := by ext x; change φ ((1 : A) • x) = φ x; rw [one_smul]
  mul_smul a b φ := by
    ext x
    change φ ((a * b) • x) = φ (b • (a • x))
    rw [mul_comm a b, mul_smul]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by
    ext x
    change φ ((a + b) • x) = φ (a • x) + φ (b • x)
    rw [add_smul, φ.map_add]
  zero_smul φ := by ext x; change φ ((0 : A) • x) = 0; rw [zero_smul, φ.map_zero]

omit [FiniteDimensional k A] in
@[simp]
theorem dual_smul_apply (M : FGModuleCat.{u} A) (a : A) (φ : Dual (k := k) M) (x : M) :
    (a • φ) x = φ (a • x) := rfl

instance dualScalarTower (M : FGModuleCat.{u} A) :
    IsScalarTower k A (Dual (k := k) M) where
  smul_assoc r a φ := by
    ext x
    change φ ((r • a) • x) = r • φ (a • x)
    rw [smul_assoc, (φ : Module.Dual k M).map_smul]

instance dualFiniteField (M : FGModuleCat.{u} A) : FiniteDimensional k (Dual (k := k) M) :=
  inferInstanceAs (FiniteDimensional k (Module.Dual k M))

instance dualFiniteAlgebra (M : FGModuleCat.{u} A) : Module.Finite A (Dual (k := k) M) :=
  Module.Finite.of_restrictScalars_finite k A _

/-- The actual finite dual module as an object of the original module category. -/
@[reducible] def dualObj (M : FGModuleCat.{u} A) : FGModuleCat.{u} A :=
  FGModuleCat.of A (Dual (k := k) M)

/-- The transpose is linear for the actual contragredient algebra action. -/
def dualMap {M N : FGModuleCat.{u} A} (f : M ⟶ N) :
    Dual (k := k) N →ₗ[A] Dual (k := k) M where
  toFun φ := φ.comp (f.hom.hom.restrictScalars k)
  map_add' φ ψ := by ext x; rfl
  map_smul' a φ := by
    ext x
    change φ (a • f.hom.hom x) = φ (f.hom.hom (a • x))
    rw [f.hom.hom.map_smul]

omit [FiniteDimensional k A] in
@[simp]
theorem dualMap_apply {M N : FGModuleCat.{u} A} (f : M ⟶ N)
    (φ : Dual (k := k) N) (x : M) : dualMap (k := k) f φ x = φ (f.hom.hom x) := rfl

/-- A separate carrier keeps the canonical restricted scalar action on the
regular module distinct from the ambient algebra's native scalar instance. -/
def RegularCarrier (A : Type u) := A

instance regularCarrierCommRing : CommRing (RegularCarrier A) :=
  inferInstanceAs (CommRing A)

instance regularCarrierModule : Module A (RegularCarrier A) :=
  inferInstanceAs (Module A A)

instance regularCarrierFieldModule : Module k (RegularCarrier A) :=
  Module.restrictScalars k A (RegularCarrier A)

instance regularCarrierScalarTower : IsScalarTower k A (RegularCarrier A) :=
  IsScalarTower.restrictScalars k A (RegularCarrier A)

instance regularCarrierFinite : Module.Finite A (RegularCarrier A) :=
  inferInstanceAs (Module.Finite A A)

instance regularCarrierFiniteField : FiniteDimensional k (RegularCarrier A) :=
  Module.Finite.trans A (RegularCarrier A)

/-- The actual regular finite module with canonical restricted scalars. -/
abbrev regular : FGModuleCat.{u} A := FGModuleCat.of A (RegularCarrier A)

/-- Multiplication is linear from the canonical scalar restriction on the
regular module; its scalar structure is kept explicit. -/
def scalarMultiplication (M : FGModuleCat.{u} A) (x : M) :
    (regular (A := A)) →ₗ[k] M where
  toFun a := (show A from a) • x
  map_add' a b := add_smul (show A from a) (show A from b) x
  map_smul' r a := by
    change ((algebraMap k A r) * (show A from a)) • x = r • ((show A from a) • x)
    rw [mul_smul, algebraMap_smul]

/-- Currying a functional gives an actual morphism to the dual regular module. -/
def coinducedHom {M : FGModuleCat.{u} A} (φ : Module.Dual k M) :
    M ⟶ dualObj (k := k) (regular (A := A)) :=
  FGModuleCat.ofHom {
    toFun x := φ.comp (scalarMultiplication M x)
    map_add' x y := by
      ext a
      change φ ((show A from a) • (x + y)) =
        φ ((show A from a) • x) + φ ((show A from a) • y)
      rw [smul_add, φ.map_add]
    map_smul' a x := by
      ext b
      change φ ((show A from b) • (a • x)) = φ ((a * (show A from b)) • x)
      rw [← mul_smul, mul_comm] }

@[simp]
theorem coinducedHom_apply {M : FGModuleCat.{u} A} (φ : Module.Dual k M) (x : M)
    (a : regular (A := A)) :
    (coinducedHom (A := A) φ).hom.hom x a = φ ((show A from a) • x) := rfl

/-- Evaluation at one recovers the functional from an actual module morphism. -/
def coinducedFunctional {M : FGModuleCat.{u} A}
    (f : M ⟶ dualObj (k := k) (regular (A := A))) : Module.Dual k M where
  toFun x := f.hom.hom x 1
  map_add' x y := by rw [f.hom.hom.map_add]; rfl
  map_smul' r x := by
    rw [← algebraMap_smul A r x, f.hom.hom.map_smul]
    change (f.hom.hom x) ((algebraMap k A r) * (1 : A)) = r • (f.hom.hom x) 1
    rw [mul_one]
    have h := LinearMap.map_smul (f.hom.hom x) r (1 : regular (A := A))
    change (f.hom.hom x) ((algebraMap k A r) * (1 : A)) = r • (f.hom.hom x) 1 at h
    simpa only [mul_one] using h

@[simp]
theorem coinducedFunctional_coinducedHom {M : FGModuleCat.{u} A} (φ : Module.Dual k M) :
    coinducedFunctional (coinducedHom (A := A) φ) = φ := by
  ext x
  change φ ((1 : A) • x) = φ x
  rw [one_smul]

@[simp]
theorem coinducedHom_coinducedFunctional {M : FGModuleCat.{u} A}
    (f : M ⟶ dualObj (k := k) (regular (A := A))) :
    coinducedHom (A := A) (coinducedFunctional f) = f := by
  apply FGModuleCat.hom_ext
  ext x a
  change (f.hom.hom ((show A from a) • x)) 1 = f.hom.hom x a
  rw [f.hom.hom.map_smul]
  change (f.hom.hom x) ((show A from a) * (1 : A)) = f.hom.hom x a
  rw [mul_one]

/-- The dual of the regular module is genuinely injective: extend a functional
across the actual underlying injective linear map and curry it back. -/
instance dualRegular_injective :
    Injective (dualObj (k := k) (regular (A := A))) where
  factors g i _ := by
    have : IsNoetherianRing A := IsNoetherianRing.of_finite k A
    let F := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
    have : Mono (F.map i) := (Functor.mono_map_iff_mono F i).mpr inferInstance
    have hi : Function.Injective (i.hom.hom.restrictScalars k) :=
      (ModuleCat.mono_iff_injective (F.map i)).mp inferInstance
    obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective hi (coinducedFunctional g)
    refine ⟨coinducedHom (A := A) ψ, ?_⟩
    rw [← coinducedHom_coinducedFunctional g]
    apply FGModuleCat.hom_ext
    ext x a
    change ψ ((show A from a) • i.hom.hom x) =
      coinducedFunctional g ((show A from a) • x)
    rw [← i.hom.hom.map_smul]
    exact congrArg (fun ℓ : Module.Dual k _ => ℓ ((show A from a) • x)) hψ

/-- An actual finite function power in the original finite-module category. -/
abbrev functionPower (J : FGModuleCat.{u} A) (n : ℕ) : FGModuleCat.{u} A :=
  FGModuleCat.of A (Fin n → J)

/-- The actual coordinate projection of a finite function power. -/
def functionPowerProjection (J : FGModuleCat.{u} A) (n : ℕ) (j : Fin n) :
    functionPower J n ⟶ J := FGModuleCat.ofHom (LinearMap.proj j)

/-- Coordinatewise injective lifting proves injectivity of actual finite
function powers; no product-identification hypothesis is needed. -/
instance functionPower_injective (J : FGModuleCat.{u} A) [Injective J] (n : ℕ) :
    Injective (functionPower J n) where
  factors g i _ := by
    let lifts (j : Fin n) := Injective.factorThru (g ≫ functionPowerProjection J n j) i
    refine ⟨FGModuleCat.ofHom (LinearMap.pi (fun j => (lifts j).hom.hom)), ?_⟩
    apply FGModuleCat.hom_ext
    ext x j
    exact congrArg (fun f => f.hom.hom x)
      (Injective.comp_factorThru (g ≫ functionPowerProjection J n j) i)

/-- Every basis coordinate functional curries to a map to the dual regular
module, giving an actual finite coinduced embedding. -/
def coinducedEmbedding (M : FGModuleCat.{u} A) :
    M ⟶ functionPower (dualObj (k := k) (regular (A := A))) (Module.finrank k M) :=
  FGModuleCat.ofHom (LinearMap.pi (fun j =>
    (coinducedHom (A := A) ((Module.finBasis k M).coord j)).hom.hom))

theorem coinducedEmbedding_coordinate (M : FGModuleCat.{u} A)
    (x : M) (j : Fin (Module.finrank k M)) :
    (coinducedEmbedding (k := k) M).hom.hom x j 1 =
      (Module.finBasis k M).equivFun x j := by
  change (Module.finBasis k M).coord j ((1 : A) • x) = _
  simp only [one_smul]
  rfl

/-- Evaluation at one recovers all basis coordinates, proving the actual
coinduced map is a monomorphism. -/
instance coinducedEmbedding_mono (M : FGModuleCat.{u} A) :
    Mono (coinducedEmbedding (k := k) M) := by
  apply Functor.mono_of_mono_map (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y h
  apply (Module.finBasis k M).equivFun.injective
  funext j
  have h' := congrArg (fun z => z j 1) h
  change (coinducedEmbedding (k := k) M).hom.hom x j 1 =
    (coinducedEmbedding (k := k) M).hom.hom y j 1 at h'
  exact (coinducedEmbedding_coordinate (k := k) M x j).symm.trans
    (h'.trans (coinducedEmbedding_coordinate (k := k) M y j))

include k in
/-- Actual finite modules have enough injectives, constructed from the dual
regular module and finite basis coordinates. -/
theorem enoughInjectives : EnoughInjectives (FGModuleCat.{u} A) where
  presentation M := ⟨{
    J := functionPower (dualObj (k := k) (regular (A := A))) (Module.finrank k M)
    f := coinducedEmbedding (k := k) M }⟩

end PretriangulatedV2.FiniteModuleCategory
