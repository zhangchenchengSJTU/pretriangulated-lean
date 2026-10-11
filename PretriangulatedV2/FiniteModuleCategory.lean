import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Artinian.Module

/-!
The concrete finite-module category used by the counterexample. Its objects
are actual finitely generated modules, with the canonical scalar restriction
from the coefficient field. Finite free covers are constructed explicitly.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

namespace PretriangulatedV2.FiniteModuleCategory

universe u

section HomFinite

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [FiniteDimensional k A]

/-- Every finite `A`-module is an actual finite-dimensional `k`-space. -/
instance finiteOverField (M : FGModuleCat.{u} A) : FiniteDimensional k M :=
  Module.Finite.trans A M

/-- The canonical map from actual module-category Hom to `k`-linear maps. -/
def homRestriction (M N : FGModuleCat.{u} A) :
    (M ⟶ N) →ₗ[k] (M →ₗ[k] N) where
  toFun f := f.hom.hom.restrictScalars k
  map_add' f g := by ext x; rfl
  map_smul' r f := by ext x; rfl

omit [FiniteDimensional k A] in
theorem homRestriction_injective (M N : FGModuleCat.{u} A) :
    Function.Injective (homRestriction (k := k) M N) := by
  intro f g h
  apply FGModuleCat.hom_ext
  ext x
  exact congrArg (fun a : M →ₗ[k] N => a x) h

/-- All actual Hom spaces in the finite-module category are finite dimensional. -/
instance homFinite (M N : FGModuleCat.{u} A) : FiniteDimensional k (M ⟶ N) :=
  Module.Finite.of_injective (homRestriction (k := k) M N)
    (homRestriction_injective (k := k) M N)

end HomFinite

section Projectives

variable {A : Type u} [Ring A]

/-- A finite free module is projective in the finite-module category. -/
theorem finiteFree_projective (n : ℕ) :
    Projective (FGModuleCat.of A (Fin n → A)) := by
  apply (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).projective_of_map_projective
  change Projective (ModuleCat.of A (Fin n → A))
  exact ModuleCat.projective_of_free (Pi.basisFun A (Fin n))

/-- An actual finite free projective presentation of every finite module. -/
theorem exists_finiteFree_presentation (M : FGModuleCat.{u} A) :
    ∃ (n : ℕ) (f : FGModuleCat.of A (Fin n → A) ⟶ M), Epi f := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  refine ⟨n, FGModuleCat.ofHom f, ?_⟩
  apply Functor.epi_of_epi_map (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))
  exact (ModuleCat.epi_iff_surjective _).mpr hf

instance enoughProjectives : EnoughProjectives (FGModuleCat.{u} A) where
  presentation M := by
    obtain ⟨n, f, hf⟩ := exists_finiteFree_presentation M
    exact ⟨{
      p := FGModuleCat.of A (Fin n → A)
      projective := finiteFree_projective n
      f := f
      epi := hf }⟩

end Projectives

end PretriangulatedV2.FiniteModuleCategory
