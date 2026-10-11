import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Serre duality data and its nondegenerate pairing

The data consist only of a linear autoequivalence and a bifunctorially natural
linear duality. The duality is written as `Hom(Y, S X) ≃ D Hom(X, Y)`, the
transpose of the usual convention in the Hom-finite setting. No almost-split
or almost-vanishing existence is included in the definition.
-/

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Category

namespace PretriangulatedV2

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C]

/-- A linear Serre autoequivalence with its natural duality pairing. -/
structure SerreDuality where
  equivalence : C ≌ C
  functor_additive : equivalence.functor.Additive
  functor_linear : Functor.Linear k equivalence.functor
  duality (X Y : C) :
    (Y ⟶ equivalence.functor.obj X) ≃ₗ[k] Module.Dual k (X ⟶ Y)
  naturality_source {X X' Y : C} (f : X' ⟶ X) (g : X ⟶ Y)
      (a : Y ⟶ equivalence.functor.obj X') :
    duality X Y (a ≫ equivalence.functor.map f) g = duality X' Y a (f ≫ g)
  naturality_target {X Y Y' : C} (f : Y ⟶ Y') (g : X ⟶ Y)
      (a : Y' ⟶ equivalence.functor.obj X) :
    duality X Y (f ≫ a) g = duality X Y' a (g ≫ f)

attribute [instance] SerreDuality.functor_additive SerreDuality.functor_linear

namespace SerreDuality

variable {k C} (D : SerreDuality k C)

/-- The usual Hom-finite convention for Serre duality, obtained by dualizing
the given pairing and using finite-dimensional biduality. -/
def homDuality (X Y : C) [FiniteDimensional k (X ⟶ Y)] :
    (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ D.equivalence.functor.obj X) :=
  (Module.evalEquiv k (X ⟶ Y)).trans (D.duality X Y).dualMap

@[simp]
lemma homDuality_apply {X Y : C} [FiniteDimensional k (X ⟶ Y)]
    (f : X ⟶ Y) (a : Y ⟶ D.equivalence.functor.obj X) :
    D.homDuality X Y f a = D.duality X Y a f := rfl

lemma homDuality_naturality_source {X X' Y : C}
    [FiniteDimensional k (X ⟶ Y)] [FiniteDimensional k (X' ⟶ Y)]
    (f : X' ⟶ X) (g : X ⟶ Y) (a : Y ⟶ D.equivalence.functor.obj X') :
    D.homDuality X' Y (f ≫ g) a =
      D.homDuality X Y g (a ≫ D.equivalence.functor.map f) :=
  (D.naturality_source f g a).symm

lemma homDuality_naturality_target {X Y Y' : C}
    [FiniteDimensional k (X ⟶ Y)] [FiniteDimensional k (X ⟶ Y')]
    (f : Y ⟶ Y') (g : X ⟶ Y) (a : Y' ⟶ D.equivalence.functor.obj X) :
    D.homDuality X Y' (g ≫ f) a = D.homDuality X Y g (f ≫ a) :=
  (D.naturality_target f g a).symm

/-- The trace supplied by a Serre pairing. -/
def trace (X : C) : (X ⟶ D.equivalence.functor.obj X) →ₗ[k] k :=
  (LinearMap.applyₗ (𝟙 X)).comp (D.duality X X).toLinearMap

@[simp]
lemma trace_apply {X : C} (a : X ⟶ D.equivalence.functor.obj X) :
    D.trace X a = D.duality X X a (𝟙 X) := rfl

/-- The pairing is determined by composing and taking the Serre trace. -/
lemma pairing_eq_trace {X Y : C} (a : Y ⟶ D.equivalence.functor.obj X) (f : X ⟶ Y) :
    D.duality X Y a f = D.trace X (f ≫ a) := by
  simpa using (D.naturality_target f (𝟙 X) a).symm

/-- Nondegeneracy in the first Hom variable follows from dual separation. -/
lemma hom_eq_zero_of_pairings_eq_zero {X Y : C} (f : X ⟶ Y)
    (h : ∀ a : Y ⟶ D.equivalence.functor.obj X, D.duality X Y a f = 0) : f = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff k f).mp
  intro ℓ
  obtain ⟨a, rfl⟩ := (D.duality X Y).surjective ℓ
  exact h a

/-- Nondegeneracy in the Serre Hom variable is injectivity of the duality. -/
lemma serreHom_eq_zero_of_pairings_eq_zero {X Y : C}
    (a : Y ⟶ D.equivalence.functor.obj X)
    (h : ∀ f : X ⟶ Y, D.duality X Y a f = 0) : a = 0 := by
  apply (D.duality X Y).injective
  ext f
  simpa using h f

/-- Serre cyclicity under an endomorphism of the source. -/
lemma pairing_serre_map {X : C} (a : X ⟶ D.equivalence.functor.obj X) (f : X ⟶ X) :
    D.duality X (D.equivalence.functor.obj X) (D.equivalence.functor.map f) a =
      D.duality X X a f := by
  rw [← Category.id_comp (D.equivalence.functor.map f), D.naturality_source]
  simpa using (D.naturality_target a f (𝟙 (D.equivalence.functor.obj X))).symm

end SerreDuality

end PretriangulatedV2
