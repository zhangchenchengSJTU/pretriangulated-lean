import PretriangulatedV2.FiniteModuleFrobenius
import PretriangulatedV2.StableSerreDuality
import PretriangulatedV2.StableTriangulationLinear
import Mathlib.LinearAlgebra.Contraction

/-!
# Genuine Serre pairings for projectives over a symmetric finite algebra

The relative trace is contraction through the finite-projective Hom--tensor
equivalence. This construction works for projectives without a free basis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat TensorProduct

namespace PretriangulatedV2.FiniteModuleCategory.SymmetricSerre

universe u

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [FiniteDimensional k A]

local instance (P : FGModuleCat.{u} A) [CategoryTheory.Projective P] :
    Module.Projective A P := moduleProjective_of_projective P

local instance :
    (CategoryTheory.Equivalence.refl (C := FGModuleCat.{u} A)).functor.Additive := by
  change (𝟭 (FGModuleCat.{u} A)).Additive
  infer_instance

local instance : Functor.Linear k
    (CategoryTheory.Equivalence.refl (C := FGModuleCat.{u} A)).functor := by
  change Functor.Linear k (𝟭 (FGModuleCat.{u} A))
  infer_instance

/-- The actual finite-module Hom linear equivalence. -/
def homLinearEquiv (P Q : FGModuleCat.{u} A) :
    (P ⟶ Q) ≃ₗ[k] (P →ₗ[A] Q) :=
  InducedCategory.homLinearEquiv.trans ModuleCat.homLinearEquiv

/-- The actual projective trace obtained by Hom--tensor contraction. -/
def traceLinear (t : SymmetricTrace k A) (P : FGModuleCat.{u} A)
    [CategoryTheory.Projective P] : (P →ₗ[A] P) →ₗ[k] k :=
  (t.trace.comp ((contractLeft A P).restrictScalars k)).comp
    ((dualTensorHomEquiv A P P).symm.toLinearMap.restrictScalars k)

omit [FiniteDimensional k A] in
@[simp]
theorem traceLinear_rankone (t : SymmetricTrace k A) (P : FGModuleCat.{u} A)
    [CategoryTheory.Projective P] (φ : Module.Dual A P) (p : P) :
    traceLinear t P (dualTensorHom A P P (φ ⊗ₜ[A] p)) = t.trace (φ p) := by
  have h : (dualTensorHomEquiv A P P).symm
      (dualTensorHom A P P (φ ⊗ₜ[A] p)) = φ ⊗ₜ[A] p := by
    change (dualTensorHomEquiv A P P).symm
      ((dualTensorHomEquiv A P P) (φ ⊗ₜ[A] p)) = _
    exact (dualTensorHomEquiv A P P).symm_apply_apply _
  change t.trace (contractLeft A P ((dualTensorHomEquiv A P P).symm _)) = _
  rw [h, contractLeft_apply]

omit [FiniteDimensional k A] in
/-- Cyclicity is proved on genuine tensor generators, so no freeness of the
projective modules is assumed. -/
theorem traceLinear_comp_comm (t : SymmetricTrace k A)
    (P Q : FGModuleCat.{u} A) [CategoryTheory.Projective P] [CategoryTheory.Projective Q]
    (f : P →ₗ[A] Q) (g : Q →ₗ[A] P) :
    traceLinear t P (g.comp f) = traceLinear t Q (f.comp g) := by
  obtain ⟨z, rfl⟩ := (dualTensorHomEquiv A P Q).surjective f
  change traceLinear t P (g.comp (dualTensorHom A P Q z)) =
    traceLinear t Q ((dualTensorHom A P Q z).comp g)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ q =>
    have hg : g.comp (dualTensorHom A P Q (φ ⊗ₜ[A] q)) =
        dualTensorHom A P P (φ ⊗ₜ[A] g q) := by ext x; simp
    have hf : (dualTensorHom A P Q (φ ⊗ₜ[A] q)).comp g =
        dualTensorHom A Q Q ((φ.comp g) ⊗ₜ[A] q) := by ext x; simp
    rw [hg, hf, traceLinear_rankone, traceLinear_rankone]
    rfl
  | add x y hx hy =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp]
    rw [hx, hy]

local instance (P Q : FGModuleCat.{u} A) : FiniteDimensional k (P →ₗ[A] Q) :=
  Module.Finite.of_injective (homLinearEquiv (k := k) P Q).symm.toLinearMap
    (homLinearEquiv (k := k) P Q).symm.injective

/-- The projective Hom pairing is linear in both variables. -/
def homDualMap (t : SymmetricTrace k A) (P Q : FGModuleCat.{u} A)
    [CategoryTheory.Projective P] :
    (Q →ₗ[A] P) →ₗ[k] Module.Dual k (P →ₗ[A] Q) where
  toFun a := {
    toFun f := traceLinear t P (a.comp f)
    map_add' f g := by simp [LinearMap.comp_add]
    map_smul' r f := by simp [LinearMap.comp_smul] }
  map_add' a b := by ext f; simp [LinearMap.add_comp]
  map_smul' r a := by ext f; simp [LinearMap.smul_comp]

omit [FiniteDimensional k A] in
/-- Rank-one testing and nondegeneracy of the original multiplication
pairing separate every actual projective-valued morphism. -/
theorem homDualMap_injective (t : SymmetricTrace k A) (P Q : FGModuleCat.{u} A)
    [CategoryTheory.Projective P] : Function.Injective (homDualMap t P Q) := by
  intro a b h
  have hz : homDualMap t P Q (a - b) = 0 := by rw [map_sub, h, sub_self]
  apply sub_eq_zero.mp
  ext q
  change (a - b) q = 0
  apply (Module.evalEquiv A P).injective
  ext φ
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, map_zero]
  change φ ((a - b) q) = 0
  apply t.nondegenerate
  intro c
  have ht := congrArg (fun ℓ => ℓ (dualTensorHom A P Q ((c • φ) ⊗ₜ[A] q))) hz
  change traceLinear t P ((a - b).comp
    (dualTensorHom A P Q ((c • φ) ⊗ₜ[A] q))) = 0 at ht
  have hr : (a - b).comp (dualTensorHom A P Q ((c • φ) ⊗ₜ[A] q)) =
      dualTensorHom A P P ((c • φ) ⊗ₜ[A] (a - b) q) := by ext x; simp
  rw [hr, traceLinear_rankone] at ht
  simpa only [LinearMap.smul_apply, smul_eq_mul, mul_comm] using ht

/-- Both nondegenerate projective pairings force equality of the actual
finite-dimensional Hom dimensions, and hence the full Serre duality. -/
def dualityNative (t : SymmetricTrace k A) (P Q : FGModuleCat.{u} A)
    [CategoryTheory.Projective P] [CategoryTheory.Projective Q] :
    (Q →ₗ[A] P) ≃ₗ[k] Module.Dual k (P →ₗ[A] Q) := by
  have h₁ : Module.finrank k (Q →ₗ[A] P) ≤ Module.finrank k (P →ₗ[A] Q) := by
    simpa only [Subspace.dual_finrank_eq] using
      LinearMap.finrank_le_finrank_of_injective (homDualMap_injective t P Q)
  have h₂ : Module.finrank k (P →ₗ[A] Q) ≤ Module.finrank k (Q →ₗ[A] P) := by
    simpa only [Subspace.dual_finrank_eq] using
      LinearMap.finrank_le_finrank_of_injective (homDualMap_injective t Q P)
  exact LinearMap.linearEquivOfInjective (homDualMap t P Q)
    (homDualMap_injective t P Q)
    (by rw [Subspace.dual_finrank_eq]; exact Nat.le_antisymm h₁ h₂)

section Noetherian

variable [IsNoetherianRing A]

/-- The genuine identity Serre pairing on all actual finite projectives over
the original symmetric algebra. Naturality follows from the proved cyclic
relative trace, including projectives that are not free. -/
def projectiveDuality (t : SymmetricTrace k A) :
    ProjectiveSerreDuality k (FGModuleCat.{u} A) (𝟭 (FGModuleCat.{u} A)) where
  duality P Q := ((homLinearEquiv Q P).trans (dualityNative t P Q)).trans
    (homLinearEquiv P Q).dualMap
  naturality_source := by
    intro P P' Q _ _ _ f g a
    change traceLinear t P ((f.hom.hom.comp a.hom.hom).comp g.hom.hom) =
      traceLinear t P' (a.hom.hom.comp (g.hom.hom.comp f.hom.hom))
    simpa only [LinearMap.comp_assoc] using
      (traceLinear_comp_comm t P' P f.hom.hom (a.hom.hom.comp g.hom.hom)).symm
  naturality_target := by
    intro P Q Q' _ _ _ f g a
    change traceLinear t P (a.hom.hom.comp (f.hom.hom.comp g.hom.hom)) =
      traceLinear t P ((a.hom.hom.comp f.hom.hom).comp g.hom.hom)
    rfl

end Noetherian

/-- The original symmetric trace supplies actual stable Serre duality,
including the actual finite-module Frobenius structure internally. -/
def stableSerre (t : SymmetricTrace k A) :
    letI := IsNoetherianRing.of_finite k A
    letI := frobeniusAbelian t
    SerreDuality k (StableCategory.projectiveStableCategory (FGModuleCat.{u} A)) := by
  letI := IsNoetherianRing.of_finite k A
  have := frobeniusAbelian t
  exact StableCategory.StableSerreDuality.serreDuality
    (CategoryTheory.Equivalence.refl (C := FGModuleCat.{u} A)) (projectiveDuality t)

section StableComparisons

variable [IsNoetherianRing A] [FrobeniusAbelian (FGModuleCat.{u} A)]

/-- The actual stable descent of the identity is naturally the identity. -/
def stableIdentityIso :
    StableCategory.stableFunctor (𝟭 (FGModuleCat.{u} A)) ≅
      𝟭 (StableCategory.projectiveStableCategory (FGModuleCat.{u} A)) :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨f, rfl⟩ := (StableCategory.projectiveStableQuotient
      (C := FGModuleCat.{u} A)).map_surjective f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The actual inverse cosyzygy is naturally the canonical negative shift. -/
def omegaIsoShift :
    (StableCategory.Cosyzygy.equivalence (C := FGModuleCat.{u} A)).inverse ≅
      shiftFunctor (StableCategory.projectiveStableCategory (FGModuleCat.{u} A)) (-1 : ℤ) :=
  Iso.isoInverseOfIsoFunctor
    (G := StableCategory.Cosyzygy.equivalence (C := FGModuleCat.{u} A))
    (G' := shiftEquiv (StableCategory.projectiveStableCategory (FGModuleCat.{u} A)) (1 : ℤ))
    (StableCategory.cosyzygyIsoShift (C := FGModuleCat.{u} A))

end StableComparisons

/-- The symmetric trace proves the genuine stable Serre functor is Omega,
with no stable Serre identification as a hypothesis. -/
def stableSerreIsoOmega (t : SymmetricTrace k A) :
    letI := IsNoetherianRing.of_finite k A
    letI := frobeniusAbelian t
    (stableSerre t).equivalence.functor ≅
      (StableCategory.Cosyzygy.equivalence (C := FGModuleCat.{u} A)).inverse := by
  letI := IsNoetherianRing.of_finite k A
  have := frobeniusAbelian t
  exact StableCategory.StableSerreDuality.serreIsoOmega
      (CategoryTheory.Equivalence.refl (C := FGModuleCat.{u} A)) (projectiveDuality t) ≪≫
    Functor.isoWhiskerRight (stableIdentityIso (A := A)) _ ≪≫ Functor.leftUnitor _

/-- The actual stable finite-module category over the original symmetric
algebra has Serre functor naturally the canonical shift by minus one. -/
def stableSerreIsoMinusOne (t : SymmetricTrace k A) :
    letI := IsNoetherianRing.of_finite k A
    letI := frobeniusAbelian t
    (stableSerre t).equivalence.functor ≅
      shiftFunctor (StableCategory.projectiveStableCategory (FGModuleCat.{u} A)) (-1 : ℤ) := by
  letI := IsNoetherianRing.of_finite k A
  have := frobeniusAbelian t
  exact stableSerreIsoOmega t ≪≫ omegaIsoShift (A := A)

/-- Transport the proved stable pairings to the literal canonical shift by
minus one. Thus the Serre autoequivalence can be chosen to be the standard
triangle shift itself, rather than requiring a Serre-exactness theorem. -/
def minusOneSerre (t : SymmetricTrace k A) :
    letI := IsNoetherianRing.of_finite k A
    letI := frobeniusAbelian t
    SerreDuality k (StableCategory.projectiveStableCategory (FGModuleCat.{u} A)) := by
  letI := IsNoetherianRing.of_finite k A
  have := frobeniusAbelian t
  let R := stableSerre t
  let e := stableSerreIsoMinusOne t
  let pair (X Y : StableCategory.projectiveStableCategory (FGModuleCat.{u} A)) :
      (Y ⟶ (shiftFunctor _ (-1 : ℤ)).obj X) ≃ₗ[k] Module.Dual k (X ⟶ Y) := {
    toFun a := R.duality X Y (a ≫ e.inv.app X)
    invFun ℓ := (R.duality X Y).symm ℓ ≫ e.hom.app X
    left_inv a := by simp
    right_inv ℓ := by
      simp only [Category.assoc, e.hom_inv_id_app]
      change R.duality X Y ((R.duality X Y).symm ℓ ≫ 𝟙 _) = ℓ
      rw [Category.comp_id]
      exact (R.duality X Y).apply_symm_apply ℓ
    map_add' a b := by simp [Preadditive.add_comp]
    map_smul' r a := by simp }
  exact {
    equivalence := shiftEquiv _ (-1 : ℤ)
    functor_additive := by change (shiftFunctor _ (-1 : ℤ)).Additive; infer_instance
    functor_linear := by change Functor.Linear k (shiftFunctor _ (-1 : ℤ)); infer_instance
    duality := pair
    naturality_source := by
      intro X X' Y f g a
      change R.duality X Y ((a ≫ (shiftFunctor _ (-1 : ℤ)).map f) ≫ e.inv.app X) g =
        R.duality X' Y (a ≫ e.inv.app X') (f ≫ g)
      rw [Category.assoc, e.inv.naturality, ← Category.assoc]
      exact R.naturality_source f g (a ≫ e.inv.app X')
    naturality_target := by
      intro X Y Y' f g a
      change R.duality X Y ((f ≫ a) ≫ e.inv.app X) g =
        R.duality X Y' (a ≫ e.inv.app X) (g ≫ f)
      rw [Category.assoc]
      exact R.naturality_target f g (a ≫ e.inv.app X) }

/-- The chosen stable Serre autoequivalence is literally the canonical
negative shift, so its Calabi--Yau comparison is the identity. -/
def minusOneSerreIso (t : SymmetricTrace k A) :
    letI := IsNoetherianRing.of_finite k A
    letI := frobeniusAbelian t
    (minusOneSerre t).equivalence.functor ≅
      shiftFunctor (StableCategory.projectiveStableCategory (FGModuleCat.{u} A)) (-1 : ℤ) :=
  Iso.refl _

end PretriangulatedV2.FiniteModuleCategory.SymmetricSerre
