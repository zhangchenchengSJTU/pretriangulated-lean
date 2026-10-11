import PretriangulatedV2.CoherentFunctors
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Canonical linear structures on coherent additive presheaves

The action comes from the central scalar endomorphisms of the original linear
category.  The module structures and finite-dimensionality below are derived
from this action and from the genuine representable presentations.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open CategoryTheory.Limits Opposite

namespace PretriangulatedV2.CoherentFunctors

variable {k : Type w} [Field k]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- The central scalar endomorphism of any group-valued presheaf. -/
def scalarNat (F : Presheaf C) (r : k) : F ⟶ F where
  app X := F.map ((r • 𝟙 X.unop).op)
  naturality := by
    intro X Y f
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    simp

@[simp]
lemma scalarNat_one (F : Presheaf C) : scalarNat F (1 : k) = 𝟙 F := by
  ext X x
  simp [scalarNat]

@[simp]
lemma scalarNat_zero (F : Presheaf C) [F.Additive] : scalarNat F (0 : k) = 0 := by
  ext X x
  simp [scalarNat]

lemma scalarNat_add (F : Presheaf C) [F.Additive] (r s : k) :
    scalarNat F (r + s) = scalarNat F r + scalarNat F s := by
  ext X x
  simp [scalarNat, add_smul, op_add, Functor.map_add]

lemma scalarNat_mul (F : Presheaf C) (r s : k) :
    scalarNat F r ≫ scalarNat F s = scalarNat F (r * s) := by
  apply NatTrans.ext
  funext X
  dsimp [scalarNat]
  rw [← F.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp [smul_smul]

lemma scalarNat_comm {F G : Presheaf C} (α : F ⟶ G) (r : k) :
    scalarNat F r ≫ α = α ≫ scalarNat G r := by
  apply NatTrans.ext
  funext X
  exact α.naturality ((r • 𝟙 X.unop).op)

instance valueSMul (F : Presheaf C) (X : Cᵒᵖ) : SMul k (F.obj X) where
  smul r x := F.map ((r • 𝟙 X.unop).op) x

instance valueModule (F : Presheaf C) [F.Additive] (X : Cᵒᵖ) :
    Module k (F.obj X) where
  toSMul := valueSMul F X
  one_smul x := by change F.map ((1 • 𝟙 X.unop).op) x = x; simp
  mul_smul r s x := by
    change F.map (((r * s) • 𝟙 X.unop).op) x =
      F.map ((r • 𝟙 X.unop).op) (F.map ((s • 𝟙 X.unop).op) x)
    have h := congrArg (fun α : F ⟶ F => α.app X x) (scalarNat_mul F s r)
    simpa [scalarNat, mul_comm] using h.symm
  smul_zero r := by change F.map _ 0 = 0; simp
  smul_add r x y := by change F.map _ (x + y) = F.map _ x + F.map _ y; simp
  zero_smul x := by change F.map ((0 • 𝟙 X.unop).op) x = 0; simp
  add_smul r s x := by
    have h := congrArg (fun α : F ⟶ F => α.app X x) (scalarNat_add F r s)
    exact h

instance homSMul (F G : Presheaf C) : SMul k (F ⟶ G) where
  smul r α := α ≫ scalarNat G r

instance homModule (F G : Presheaf C) [G.Additive] : Module k (F ⟶ G) where
  toSMul := homSMul F G
  one_smul α := by change α ≫ scalarNat G (1 : k) = α; simp
  mul_smul r s α := by
    change α ≫ scalarNat G (r * s) = (α ≫ scalarNat G s) ≫ scalarNat G r
    rw [Category.assoc, scalarNat_mul, mul_comm]
  smul_zero r := by change (0 : F ⟶ G) ≫ scalarNat G r = 0; simp
  smul_add r α β := by
    change (α + β) ≫ scalarNat G r = α ≫ scalarNat G r + β ≫ scalarNat G r
    simp [add_comp]
  zero_smul α := by change α ≫ scalarNat G (0 : k) = 0; simp
  add_smul r s α := by
    change α ≫ scalarNat G (r + s) = α ≫ scalarNat G r + α ≫ scalarNat G s
    simp [scalarNat_add, comp_add]

@[simp]
lemma hom_smul_app {F G : Presheaf C} (r : k) (α : F ⟶ G) (X : Cᵒᵖ) (x : F.obj X) :
    (r • α).app X x = r • α.app X x := rfl

lemma hom_smul_comp {F G H : Presheaf C} (r : k) (α : F ⟶ G) (β : G ⟶ H) :
    (r • α) ≫ β = r • (α ≫ β) := by
  change (α ≫ scalarNat G r) ≫ β = (α ≫ β) ≫ scalarNat H r
  rw [Category.assoc, scalarNat_comm, Category.assoc]

lemma hom_comp_smul {F G H : Presheaf C} (α : F ⟶ G) (r : k) (β : G ⟶ H) :
    α ≫ (r • β) = r • (α ≫ β) := (Category.assoc _ _ _).symm

/-- The actual coherent-functor category inherits the canonical action. -/
instance modLinear : Linear k (Mod C) where
  homModule F G := InducedCategory.homAddEquiv.module k
  smul_comp F G H r α β := by
    ext X x
    exact congrArg (fun γ : F.obj ⟶ H.obj => γ.app X x) (hom_smul_comp r α.hom β.hom)
  comp_smul F G H α r β := by
    ext X x
    exact congrArg (fun γ : F.obj ⟶ H.obj => γ.app X x) (hom_comp_smul α.hom r β.hom)

/-- The full-subcategory hom comparison is linear for this canonical action. -/
def modHomLinearEquiv (F G : Mod C) : (F ⟶ G) ≃ₗ[k] (F.obj ⟶ G.obj) :=
  InducedCategory.homAddEquiv.linearEquiv k

instance yoneda_linear : Functor.Linear k (yoneda (C := C)) where
  map_smul := by
    intro X Y f r
    ext W g
    change g ≫ (r • f) = (r • 𝟙 W.unop) ≫ (g ≫ f)
    simp

instance autoequivalence_functor_linear (e : C ≌ C) [e.functor.Additive]
    [Functor.Linear k e.functor] : Functor.Linear k (autoequivalence e).functor where
  map_smul := by
    intro F G α r
    ext W x
    change G.obj.map ((r • 𝟙 (e.inverse.obj W.unop)).op)
      (α.hom.app (op (e.inverse.obj W.unop)) x) =
        G.obj.map ((e.inverse.map (r • 𝟙 W.unop)).op)
          (α.hom.app (op (e.inverse.obj W.unop)) x)
    rw [e.inverse.map_smul, e.inverse.map_id]

/-- Naturality makes each component of a transformation linear for the
canonical actions on values. -/
def appLinearMap {F G : Presheaf C} [F.Additive] [G.Additive]
    (α : F ⟶ G) (X : Cᵒᵖ) : F.obj X →ₗ[k] G.obj X where
  toFun := α.app X
  map_add' := by intro x y; exact (α.app X).hom.map_add x y
  map_smul' := by
    intro r x
    change α.app X (F.map ((r • 𝟙 X.unop).op) x) =
      G.map ((r • 𝟙 X.unop).op) (α.app X x)
    exact congrArg (fun f => f x) (α.naturality ((r • 𝟙 X.unop).op))

/-- The additive Yoneda equivalence respects the canonical scalar action. -/
def yonedaLinearEquiv {F : Presheaf C} [F.Additive] (X : C) :
    (preadditiveYoneda.obj X ⟶ F) ≃ₗ[k] F.obj (op X) where
  toEquiv := yonedaEquiv X
  map_add' := by intro α β; rfl
  map_smul' := by intro r α; rfl

namespace Presentation

variable {F : Presheaf C} [F.Additive] (P : Presentation C F)

/-- A presentation component is linear from the original hom space. -/
def projectionLinearMap (X : C) : (X ⟶ P.generators) →ₗ[k] F.obj (op X) where
  toFun := P.projection.app (op X)
  map_add' := by intro f g; exact (P.projection.app (op X)).hom.map_add f g
  map_smul' := by
    intro r f
    change P.projection.app (op X) (r • f) =
      F.map ((r • 𝟙 X).op) (P.projection.app (op X) f)
    have h := congrArg (fun a => a f) (P.projection.naturality ((r • 𝟙 X).op))
    dsimp [preadditiveYoneda, preadditiveYonedaObj] at h
    simpa using h

theorem projectionLinearMap_surjective (X : C) :
    Function.Surjective (P.projectionLinearMap (k := k) X) :=
  (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

variable [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

include P in
/-- Coherent values are finite dimensional, by the genuine presentation epi. -/
theorem finiteDimensional_value (X : Cᵒᵖ) : FiniteDimensional k (F.obj X) :=
  Module.Finite.of_surjective (P.projectionLinearMap (k := k) X.unop)
    (P.projectionLinearMap_surjective X.unop)

end Presentation

variable [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

instance modValueFiniteDimensional (F : Mod C) (X : Cᵒᵖ) :
    FiniteDimensional k (F.obj.obj X) :=
  F.property.some.finiteDimensional_value X

/-- Precomposition with a presentation epi is an injective linear map on
natural transformations. -/
def presentationHomLinearMap {F G : Presheaf C} [G.Additive]
    (P : Presentation C F) : (F ⟶ G) →ₗ[k] (preadditiveYoneda.obj P.generators ⟶ G) where
  toFun α := P.projection ≫ α
  map_add' := by intro α β; simp [comp_add]
  map_smul' := by intro r α; exact hom_comp_smul P.projection r α

omit [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
lemma presentationHomLinearMap_injective {F G : Presheaf C} [G.Additive]
    (P : Presentation C F) : Function.Injective (presentationHomLinearMap (k := k) (G := G) P) := by
  intro α β h
  exact (cancel_epi P.projection).mp h

instance modRawHomFiniteDimensional (F G : Mod C) :
    FiniteDimensional k (F.obj ⟶ G.obj) := by
  let P := F.property.some
  have hrep : FiniteDimensional k (preadditiveYoneda.obj P.generators ⟶ G.obj) :=
    FiniteDimensional.of_injective (yonedaLinearEquiv (F := G.obj) P.generators).toLinearMap
      (yonedaLinearEquiv (F := G.obj) P.generators).injective
  exact FiniteDimensional.of_injective (presentationHomLinearMap (G := G.obj) P)
    (presentationHomLinearMap_injective P)

/-- `mod(C)` is Hom finite whenever the original linear category is. -/
instance modHomFiniteDimensional (F G : Mod C) : FiniteDimensional k (F ⟶ G) :=
  FiniteDimensional.of_injective (modHomLinearEquiv (k := k) F G).toLinearMap
    (modHomLinearEquiv (k := k) F G).injective

section Suspension

variable [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

instance projectiveInjectiveYoneda_linear :
    Functor.Linear k (projectiveInjectiveYoneda (C := C)) where
  map_smul := by
    intro X Y f r
    ext W g
    change g ≫ (r • f) = (r • 𝟙 W.unop) ≫ (g ≫ f)
    simp

instance projectiveInjectiveEquivalence_functor_linear [IsIdempotentComplete C] :
    Functor.Linear k (projectiveInjectiveEquivalence (C := C)).functor := by
  change Functor.Linear k (projectiveInjectiveYoneda (C := C))
  infer_instance

variable [Functor.Linear k (shiftFunctor C (1 : ℤ))]

instance suspension_functor_additive : (suspension (C := C)).functor.Additive := by
  have : (shiftEquiv C (1 : ℤ)).functor.Additive := by
    change (shiftFunctor C (1 : ℤ)).Additive
    infer_instance
  change (autoequivalence (shiftEquiv C (1 : ℤ))).functor.Additive
  infer_instance

/-- The original linear suspension has a linear extension to coherent functors. -/
instance suspension_functor_linear : Functor.Linear k (suspension (C := C)).functor := by
  have : Functor.Linear k (shiftEquiv C (1 : ℤ)).functor := by
    change Functor.Linear k (shiftFunctor C (1 : ℤ))
    infer_instance
  have : (shiftEquiv C (1 : ℤ)).functor.Additive := by
    change (shiftFunctor C (1 : ℤ)).Additive
    infer_instance
  change Functor.Linear k (autoequivalence (shiftEquiv C (1 : ℤ))).functor
  infer_instance

end Suspension

end PretriangulatedV2.CoherentFunctors
