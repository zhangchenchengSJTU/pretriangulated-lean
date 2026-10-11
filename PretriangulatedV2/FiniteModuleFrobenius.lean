import PretriangulatedV2.FiniteModuleDuality
import PretriangulatedV2.Frobenius

/-!
# Frobenius finite-module categories from an actual symmetric trace

The input is a linear trace with nondegenerate multiplication pairing.
Injectivity, projectivity and the Frobenius category structure are derived.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

namespace PretriangulatedV2.FiniteModuleCategory

universe u

/-- The original symmetric-algebra data: a linear trace whose multiplication
pairing has trivial radical. No categorical Frobenius conclusion is a field. -/
structure SymmetricTrace (k A : Type u) [Field k] [CommRing A] [Algebra k A] where
  trace : A →ₗ[k] k
  nondegenerate : ∀ a : A, (∀ b : A, trace (a * b) = 0) → a = 0

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [FiniteDimensional k A]

/-- The actual identity between canonical regular scalars and the native
algebra scalars; its linearity is proved rather than identified by defeq. -/
def regularToAlgebra : regular (A := A) →ₗ[k] A where
  toFun a := a
  map_add' a b := rfl
  map_smul' r a := by
    change (algebraMap k A r) * (show A from a) = r • (show A from a)
    exact (Algebra.smul_def r (show A from a)).symm

/-- The trace multiplication map into the actual contragredient dual. -/
def traceRegularMap (t : SymmetricTrace k A) :
    regular (A := A) →ₗ[A] Dual (k := k) (regular (A := A)) :=
  (coinducedHom (t.trace.comp (regularToAlgebra (k := k) (A := A)))).hom.hom

@[simp]
theorem traceRegularMap_apply (t : SymmetricTrace k A)
    (a b : regular (A := A)) :
    traceRegularMap t a b = t.trace ((show A from b) * (show A from a)) := rfl

theorem traceRegularMap_injective (t : SymmetricTrace k A) :
    Function.Injective (traceRegularMap t) := by
  intro a b h
  apply sub_eq_zero.mp
  apply t.nondegenerate (show A from a - b)
  intro c
  have h' := congrArg (fun φ => φ (show regular (A := A) from c)) h
  change t.trace (c * (show A from a)) = t.trace (c * (show A from b)) at h'
  simpa only [mul_sub, t.trace.map_sub, mul_comm] using sub_eq_zero.mpr h'

/-- Nondegeneracy and actual finite-dimensional duality give the original
regular module's isomorphism with its dual. -/
def regularIsoDual (t : SymmetricTrace k A) :
    regular (A := A) ≅ dualObj (k := k) (regular (A := A)) := by
  have hs : Function.Surjective (traceRegularMap t) := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (traceRegularMap t).restrictScalars k) ?_).mp
        (traceRegularMap_injective t)
    change Module.finrank k (regular (A := A)) =
      Module.finrank k (Module.Dual k (regular (A := A)))
    exact (Subspace.dual_finrank_eq (K := k) (V := regular (A := A))).symm
  exact (LinearEquiv.ofBijective (traceRegularMap t)
    ⟨traceRegularMap_injective t, hs⟩).toFGModuleCatIso

/-- The symmetric trace derives genuine injectivity of the regular module. -/
theorem regular_injective (t : SymmetricTrace k A) : Injective (regular (A := A)) :=
  Injective.of_iso (regularIsoDual t).symm inferInstance

/-- An actual isomorphism induces its pointwise isomorphism on finite powers. -/
def functionPowerIso {J K : FGModuleCat.{u} A} (e : J ≅ K) (n : ℕ) :
    functionPower J n ≅ functionPower K n :=
  (LinearEquiv.piCongrRight (fun _ : Fin n => FGModuleCat.isoToLinearEquiv e)).toFGModuleCatIso

/-- The separate regular carrier represents the actual finite free module. -/
def functionPowerRegularIso (n : ℕ) :
    functionPower (regular (A := A)) n ≅ FGModuleCat.of A (Fin n → A) :=
  (LinearEquiv.refl A (Fin n → A)).toFGModuleCatIso

/-- A symmetric multiplication pairing makes every actual finite free module
injective. -/
theorem finiteFree_injective (t : SymmetricTrace k A) (n : ℕ) :
    Injective (FGModuleCat.of A (Fin n → A)) := by
  have := regular_injective t
  exact Injective.of_iso (functionPowerRegularIso (A := A) n) inferInstance

/-- Projective finite modules split an actual finite free cover, and hence
inherit the derived injectivity of that cover. -/
theorem injective_of_projective (t : SymmetricTrace k A) (P : FGModuleCat.{u} A)
    [Projective P] : Injective P := by
  obtain ⟨n, f, hf⟩ := exists_finiteFree_presentation P
  have := finiteFree_injective t n
  exact (⟨Projective.factorThru (𝟙 P) f, f,
    Projective.factorThru_comp (𝟙 P) f⟩ :
      Retract P (FGModuleCat.of A (Fin n → A))).injective

/-- The actual coinduced presentation of an injective object splits. Its
target is finite free via the symmetric trace, so the object is projective. -/
theorem projective_of_injective (t : SymmetricTrace k A) (J : FGModuleCat.{u} A)
    [Injective J] : Projective J := by
  let e := functionPowerIso (regularIsoDual t).symm (Module.finrank k J) ≪≫
    functionPowerRegularIso (A := A) (Module.finrank k J)
  have : Projective (functionPower (dualObj (k := k) (regular (A := A)))
      (Module.finrank k J)) :=
    Projective.of_iso e.symm (finiteFree_projective (Module.finrank k J))
  exact (⟨coinducedEmbedding (k := k) J,
    Injective.factorThru (𝟙 J) (coinducedEmbedding (k := k) J),
    Injective.comp_factorThru (𝟙 J) (coinducedEmbedding (k := k) J)⟩ :
      Retract J (functionPower (dualObj (k := k) (regular (A := A)))
        (Module.finrank k J))).projective

/-- The actual finitely generated module category is Frobenius from the
original symmetric trace. No categorical Frobenius hypothesis is assumed. -/
theorem frobeniusAbelian (t : SymmetricTrace k A) :
    letI := IsNoetherianRing.of_finite k A
    FrobeniusAbelian (FGModuleCat.{u} A) := by
  let := IsNoetherianRing.of_finite k A
  exact {
    enoughProjectives := inferInstance
    enoughInjectives := enoughInjectives (k := k) (A := A)
    projective_iff_injective := fun P =>
      ⟨fun h => by have := h; exact injective_of_projective t P,
       fun h => by have := h; exact projective_of_injective t P⟩ }

/-- Actual categorical projectivity supplies module-theoretic projectivity
through a split finite free cover. It is not assumed to be preserved by the
full finite-module inclusion. -/
theorem moduleProjective_of_projective (P : FGModuleCat.{u} A) [Projective P] :
    Module.Projective A P := by
  obtain ⟨n, f, hf⟩ := exists_finiteFree_presentation P
  let r : Retract P (FGModuleCat.of A (Fin n → A)) :=
    ⟨Projective.factorThru (𝟙 P) f, f, Projective.factorThru_comp (𝟙 P) f⟩
  let F := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
  have : Projective (F.obj (FGModuleCat.of A (Fin n → A))) :=
    ModuleCat.projective_of_free (Pi.basisFun A (Fin n))
  have hP : Projective (F.obj P) := (r.map F).projective
  change Projective P.obj at hP
  have := hP
  exact ModuleCat.projective_of_module_projective P.obj

end PretriangulatedV2.FiniteModuleCategory
