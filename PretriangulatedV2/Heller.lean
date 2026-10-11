import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace PretriangulatedV2

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

abbrev cube (F : C ⥤ C) : C ⥤ C := (F ⋙ F) ⋙ F

/-- The data in Definition 3.1, with the stable category presented abstractly as a
preadditive category.

`S ⋙ F` denotes the mathematical composite `F ∘ S`; thus `sigma` represents
`F S ≅ S F` in the notation of the paper. -/
structure HellerParameter (F S : C ⥤ C) (sigma : S ⋙ F ≅ F ⋙ S) where
  delta : S ≅ cube F
  commutes (X : C) :
    (show F.obj (S.obj X) ⟶ F.obj ((cube F).obj X) from F.map (delta.hom.app X)) +
      (show F.obj (S.obj X) ⟶ F.obj ((cube F).obj X) from
        sigma.hom.app X ≫ delta.hom.app (F.obj X)) = 0

/-- An invertible element of the triangle centre, retaining precisely the
commutation with the cosyzygy functor used in Lemma 3.7. -/
structure TriangleCenterUnit (F : C ⥤ C) where
  iso : 𝟭 C ≅ 𝟭 C
  commutes (X : C) : F.map (iso.hom.app X) = iso.hom.app (F.obj X)

namespace TriangleCenterUnit

variable {F S : C ⥤ C}

/-- Whiskering a central unit gives the `S u` occurring in Lemma 3.7. -/
def whisker (u : TriangleCenterUnit F) : S ≅ S :=
  Functor.isoWhiskerRight u.iso S

omit [Preadditive C] in
@[simp]
lemma whisker_hom_app (u : TriangleCenterUnit F) (X : C) :
    (u.whisker (S := S)).hom.app X = S.map (u.iso.hom.app X) := rfl

end TriangleCenterUnit

namespace HellerParameter

variable {F S : C ⥤ C} {sigma : S ⋙ F ≅ F ⋙ S}

/-- Lemma 3.7: precomposing a Heller parameter with `S u` is again a
Heller parameter. -/
def twist (p : HellerParameter F S sigma) (u : TriangleCenterUnit F) :
    HellerParameter F S sigma where
  delta := u.whisker (S := S) ≪≫ p.delta
  commutes X := by
    simp only [Iso.trans_hom, NatTrans.comp_app,
      TriangleCenterUnit.whisker_hom_app, Functor.map_comp]
    have hsigma := sigma.hom.naturality (u.iso.hom.app X)
    simp only [Functor.comp_map, Functor.id_obj] at hsigma
    rw [u.commutes X] at hsigma
    rw [← Category.assoc, ← hsigma]
    rw [Category.assoc, ← Preadditive.comp_add, p.commutes]
    simp

@[simp]
lemma twist_delta_hom_app (p : HellerParameter F S sigma) (u : TriangleCenterUnit F) (X : C) :
    (p.twist u).delta.hom.app X =
      S.map (u.iso.hom.app X) ≫ p.delta.hom.app X := rfl

/-- The component equation extracted from the comparison in Lemma 4.1.

This records only its stable-category algebra; constructing the comparison map
between the two acyclic complexes is outside the scope of this helper. -/
def TwistComparison (p : HellerParameter F S sigma) (u : TriangleCenterUnit F)
    {M N : C} (f g : M ⟶ N) : Prop :=
  p.delta.hom.app M ≫ (cube F).map g =
    S.map f ≫ (p.twist u).delta.hom.app N

/-- The comparison equation says that its two maps differ exactly by the
central unit.  This is the cancellation-and-faithfulness part of Lemma 4.1. -/
lemma comparison_eq_comp_unit [(cube F).Faithful]
    (p : HellerParameter F S sigma) (u : TriangleCenterUnit F) {M N : C}
    {f g : M ⟶ N} (h : TwistComparison p u f g) :
    g = f ≫ u.iso.hom.app N := by
  apply (cube F).map_injective
  apply (cancel_epi (p.delta.hom.app M)).1
  calc
    p.delta.hom.app M ≫ (cube F).map g =
        S.map f ≫ (p.twist u).delta.hom.app N := h
    _ = S.map f ≫ (S.map (u.iso.hom.app N) ≫ p.delta.hom.app N) := by rfl
    _ = S.map (f ≫ u.iso.hom.app N) ≫ p.delta.hom.app N := by
      rw [← Category.assoc, ← Functor.map_comp]
    _ = p.delta.hom.app M ≫ (cube F).map (f ≫ u.iso.hom.app N) :=
      p.delta.hom.naturality (f ≫ u.iso.hom.app N)

/-- Naturality converts the right-component formulation of the comparison
into the source-component formulation used in the paper. -/
lemma comparison_eq_unit_comp [(cube F).Faithful]
    (p : HellerParameter F S sigma) (u : TriangleCenterUnit F) {M N : C}
    {f g : M ⟶ N} (h : TwistComparison p u f g) :
    g = u.iso.hom.app M ≫ f := by
  rw [comparison_eq_comp_unit p u h]
  simpa only [Functor.id_map] using u.iso.hom.naturality f

/-- If the comparison map is invertible, the source component of the central
unit is recovered from it. -/
lemma unit_source_eq_comparison_comp_inv [(cube F).Faithful]
    (p : HellerParameter F S sigma) (u : TriangleCenterUnit F) {M N : C}
    {f g : M ⟶ N} [IsIso f] (h : TwistComparison p u f g) :
    u.iso.hom.app M = g ≫ inv f := by
  rw [comparison_eq_unit_comp p u h]
  simp

/-- Equivalent target-component form of the preceding reconstruction. -/
lemma unit_target_eq_inv_comp_comparison [(cube F).Faithful]
    (p : HellerParameter F S sigma) (u : TriangleCenterUnit F) {M N : C}
    {f g : M ⟶ N} [IsIso f] (h : TwistComparison p u f g) :
    u.iso.hom.app N = inv f ≫ g := by
  rw [comparison_eq_comp_unit p u h]
  simp

/-- Twisting by a fixed central unit is injective.  In fact this only uses
the inverse of `S u`; no faithfulness hypothesis is needed. -/
lemma twist_injective (u : TriangleCenterUnit F) :
    Function.Injective (fun p : HellerParameter F S sigma => p.twist u) := by
  intro p q h
  have hdelta : p.delta = q.delta := by
    have h' := congrArg
      (fun d : S ≅ cube F => (u.whisker (S := S)).symm ≪≫ d)
      (congrArg HellerParameter.delta h)
    simpa [twist] using h'
  cases p
  cases q
  cases hdelta
  rfl

end HellerParameter

end PretriangulatedV2
