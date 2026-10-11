import PretriangulatedV2.SerreDuality

/-!
# Constructing a Serre functor from natural representing objects

Naturality of a nondegenerate right pairing in its second variable determines
all maps of the representing functor. Finite-dimensional biduality proves
that this functor is fully faithful. Objectwise essential surjectivity then
supplies the autoequivalence required by the raw Serre definition.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

open CategoryTheory CategoryTheory.Category

namespace PretriangulatedV2.SerreFunctorConstruction

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C]

/-- Representing objects for right Serre duality, natural in the tested object. -/
structure RightPairing where
  obj : C → C
  duality (X Y : C) : (Y ⟶ obj X) ≃ₗ[k] Module.Dual k (X ⟶ Y)
  naturality_target {X Y Y' : C} (f : Y ⟶ Y') (g : X ⟶ Y) (a : Y' ⟶ obj X) :
    duality X Y (f ≫ a) g = duality X Y' a (g ≫ f)

namespace RightPairing

variable {k C} (D : RightPairing k C)

/-- Yoneda determines the representing morphism of a source map. -/
def mapHom {X Y : C} (f : X ⟶ Y) : D.obj X ⟶ D.obj Y :=
  (D.duality Y (D.obj X)).symm {
    toFun g := D.duality X (D.obj X) (𝟙 (D.obj X)) (f ≫ g)
    map_add' g h := by simp [Preadditive.comp_add]
    map_smul' r g := by simp }

@[simp]
lemma mapHom_pair {X Y : C} (f : X ⟶ Y) (g : Y ⟶ D.obj X) :
    D.duality Y (D.obj X) (D.mapHom f) g =
      D.duality X (D.obj X) (𝟙 (D.obj X)) (f ≫ g) := by
  exact congrArg (fun ℓ : Module.Dual k (Y ⟶ D.obj X) ↦ ℓ g)
    ((D.duality Y (D.obj X)).apply_symm_apply _)

lemma pairing_eq_trace {X Y : C} (f : X ⟶ Y) (g : Y ⟶ D.obj X) :
    D.duality X Y g f = D.duality X (D.obj X) (𝟙 (D.obj X)) (f ≫ g) := by
  simpa using D.naturality_target g f (𝟙 (D.obj X))

/-- The previously absent source naturality is forced by the representing pairing. -/
lemma naturality_source {X X' Y : C} (f : X' ⟶ X) (g : X ⟶ Y) (a : Y ⟶ D.obj X') :
    D.duality X Y (a ≫ D.mapHom f) g = D.duality X' Y a (f ≫ g) := by
  rw [D.naturality_target, mapHom_pair, D.pairing_eq_trace (f ≫ g) a]
  simp only [Category.assoc]

@[simp]
lemma mapHom_id (X : C) : D.mapHom (𝟙 X) = 𝟙 (D.obj X) := by
  apply (D.duality X (D.obj X)).injective
  ext g
  simp

@[simp]
lemma mapHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.mapHom (f ≫ g) = D.mapHom f ≫ D.mapHom g := by
  apply (D.duality Z (D.obj X)).injective
  ext h
  rw [mapHom_pair, D.naturality_source, mapHom_pair]
  simp only [Category.assoc]

@[simp]
lemma mapHom_add {X Y : C} (f g : X ⟶ Y) : D.mapHom (f + g) = D.mapHom f + D.mapHom g := by
  apply (D.duality Y (D.obj X)).injective
  ext h
  simp [Preadditive.add_comp]

@[simp]
lemma mapHom_smul {X Y : C} (r : k) (f : X ⟶ Y) : D.mapHom (r • f) = r • D.mapHom f := by
  apply (D.duality Y (D.obj X)).injective
  ext h
  simp

/-- The actual functor determined by the representing objects. -/
def functor : C ⥤ C where
  obj := D.obj
  map := D.mapHom
  map_id := D.mapHom_id
  map_comp := D.mapHom_comp

instance functor_additive : D.functor.Additive where
  map_add := by
    intro X Y f g
    exact D.mapHom_add f g

instance functor_linear : Functor.Linear k D.functor where
  map_smul f r := D.mapHom_smul r f

section HomFinite

variable [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Finite biduality explicitly inverts the representing functor's Hom map. -/
def mapEquiv (X Y : C) : (X ⟶ Y) ≃ₗ[k] (D.obj X ⟶ D.obj Y) :=
  ((Module.evalEquiv k (X ⟶ Y)).trans (D.duality X Y).dualMap).trans
    (D.duality Y (D.obj X)).symm

@[simp]
lemma mapEquiv_apply {X Y : C} (f : X ⟶ Y) : D.mapEquiv X Y f = D.mapHom f := by
  apply (D.duality Y (D.obj X)).injective
  ext g
  simp only [mapEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.dualMap_apply, Module.evalEquiv_apply, Module.Dual.eval_apply, mapHom_pair]
  exact D.pairing_eq_trace f g

instance functor_full : D.functor.Full where
  map_surjective := by
    intro X Y f
    obtain ⟨g, hg⟩ := (D.mapEquiv X Y).surjective f
    exact ⟨g, (D.mapEquiv_apply g).symm.trans hg⟩

instance functor_faithful : D.functor.Faithful where
  map_injective := by
    intro X Y f g h
    apply (D.mapEquiv X Y).injective
    change D.mapHom f = D.mapHom g at h
    simpa only [mapEquiv_apply] using h

/-- Once the representing objects cover every isomorphism class, they form a
genuine linear Serre autoequivalence. -/
def serreDuality (hobj : ∀ Y : C, ∃ X : C, Nonempty (D.obj X ≅ Y)) : SerreDuality k C := by
  have : D.functor.EssSurj := ⟨hobj⟩
  have : D.functor.IsEquivalence := {}
  exact {
    equivalence := D.functor.asEquivalence
    functor_additive := by change D.functor.Additive; infer_instance
    functor_linear := by change Functor.Linear k D.functor; infer_instance
    duality := D.duality
    naturality_source := D.naturality_source
    naturality_target := D.naturality_target }

end HomFinite

end RightPairing

end PretriangulatedV2.SerreFunctorConstruction
