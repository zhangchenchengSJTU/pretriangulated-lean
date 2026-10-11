import PretriangulatedV2.StableCategory
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!
An additive functor preserving projective objects descends to the additive
stable quotient. This is part of the functorial foundation needed in Section 3
of arXiv:2608.09777v2; it does not construct the cosyzygy or a triangulation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasBinaryBiproducts C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects]

omit [Abelian C] [HasBinaryBiproducts C] [Abelian D] [HasBinaryBiproducts D] [F.Additive] in
theorem map_factorsThrough_projective {X Y : C} {f : X ⟶ Y}
    (hf : FactorsThrough (projectiveObjects : C → Prop) f) :
    FactorsThrough (projectiveObjects : D → Prop) (F.map f) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  exact ⟨F.obj P, F.projective_obj_of_projective hP, F.map a, F.map b,
    by rw [← F.map_comp, hab]⟩

theorem map_respects_projective_relation {X Y : C} (f g : X ⟶ Y)
    (h : factorRelation (projectiveObjects : C → Prop) f g) :
    (projectiveStableQuotient (C := D)).map (F.map f) =
      (projectiveStableQuotient (C := D)).map (F.map g) := by
  apply sub_eq_zero.mp
  rw [← Functor.map_sub, ← F.map_sub, functor_map_eq_zero_iff]
  exact map_factorsThrough_projective F h

/-- The induced functor on stable additive quotients. -/
def stableFunctor : projectiveStableCategory C ⥤ projectiveStableCategory D :=
  CategoryTheory.Quotient.lift (factorRelation (projectiveObjects : C → Prop))
    (F ⋙ projectiveStableQuotient (C := D))
    (fun _ _ f g h => map_respects_projective_relation F f g h)

@[simp]
theorem stableFunctor_obj (X : C) :
    (stableFunctor F).obj ((projectiveStableQuotient (C := C)).obj X) =
      (projectiveStableQuotient (C := D)).obj (F.obj X) := rfl

@[simp]
theorem stableFunctor_map {X Y : C} (f : X ⟶ Y) :
    (stableFunctor F).map ((projectiveStableQuotient (C := C)).map f) =
      (projectiveStableQuotient (C := D)).map (F.map f) := rfl

/-- The descended functor commutes with the quotient functors. -/
theorem stableFunctor_spec :
    projectiveStableQuotient (C := C) ⋙ stableFunctor F =
      F ⋙ projectiveStableQuotient (C := D) :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance stableFunctor_additive : (stableFunctor F).Additive := by
  have : (projectiveStableQuotient (C := C) ⋙ stableFunctor F).Additive := by
    rw [stableFunctor_spec F]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp
    (projectiveStableQuotient (C := C)) (stableFunctor F)

end PretriangulatedV2.StableCategory
