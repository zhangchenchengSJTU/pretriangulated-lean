import PretriangulatedV2.CoherentLinear
import PretriangulatedV2.Cosyzygy
import PretriangulatedV2.StableFunctor
import Mathlib.CategoryTheory.Quotient.Linear

/-!
# Linear and Hom-finite structures on actual stable quotients

The ideal of maps through projectives is closed under scalars. Mathlib's
quotient construction therefore supplies an actual linear category; its full
quotient functor supplies finite dimensionality. Cosyzygy is linear because
any scalar multiple of a chosen extension is another valid extension.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v v' u u'

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Preadditive

namespace PretriangulatedV2.IdealQuotient

variable {k : Type w} [Field k]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [HasBinaryBiproducts C]
  (B : C → Prop)

omit [HasBinaryBiproducts C] in
lemma factorsThrough_smul {X Y : C} {f : X ⟶ Y} (hf : FactorsThrough B f) (r : k) :
    FactorsThrough B (r • f) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  exact ⟨P, hP, r • a, b, by simp [hab]⟩

variable [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]

lemma factorRelation_smul (r : k) {X Y : C} (f g : X ⟶ Y)
    (h : factorRelation B f g) : factorRelation B (r • f) (r • g) := by
  change FactorsThrough B (r • f - r • g)
  rw [← smul_sub]
  exact factorsThrough_smul B h r

instance quotient_linear : Linear k (category B) :=
  CategoryTheory.Quotient.linear k (factorRelation B) (factorRelation_smul B)

instance functor_linear : Functor.Linear k (functor B) :=
  CategoryTheory.Quotient.linear_functor k (factorRelation B) (factorRelation_smul B)

instance quotientHomFiniteDimensional [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (X Y : category B) : FiniteDimensional k (X ⟶ Y) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  exact FiniteDimensional.of_surjective ((functor B).mapLinearMap k)
    (functor B).map_surjective

end PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory

variable {k : Type w} [Field k]
  {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C] [Linear k C]

instance projectiveStableCategory_linear : Linear k (projectiveStableCategory C) :=
  inferInstanceAs (Linear k (PretriangulatedV2.IdealQuotient.category
    (projectiveObjects : C → Prop)))

instance projectiveStableQuotient_linear : Functor.Linear k (projectiveStableQuotient (C := C)) :=
  inferInstanceAs (Functor.Linear k (PretriangulatedV2.IdealQuotient.functor
    (projectiveObjects : C → Prop)))

instance projectiveStableHomFiniteDimensional
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (X Y : projectiveStableCategory C) : FiniteDimensional k (X ⟶ Y) :=
  PretriangulatedV2.IdealQuotient.quotientHomFiniteDimensional (projectiveObjects : C → Prop) X Y

instance stableFunctor_linear
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasBinaryBiproducts D] [Linear k D]
    (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects] [Functor.Linear k F] :
    Functor.Linear k (stableFunctor F) := by
  have : Functor.Linear k (projectiveStableQuotient (C := C) ⋙ stableFunctor F) := by
    rw [stableFunctor_spec F]
    infer_instance
  exact Functor.linear_of_full_essSurj_comp (projectiveStableQuotient (C := C))
    (stableFunctor F)

namespace Cosyzygy

variable [FrobeniusAbelian C]

/-- Scalar multiples of a chosen extension induce the required scalar map
after taking its unique stable class. -/
theorem stable_map_smul {X Y : C} (f : X ⟶ Y) (r : k) :
    (projectiveStableQuotient (C := C)).map (map (r • f)) =
      r • (projectiveStableQuotient (C := C)).map (map f) := by
  rw [stable_map_eq (r • f) (r • extension f) (by simp)]
  rw [← Functor.map_smul]
  congr 1
  apply (cancel_epi (cokernel.π (Injective.ι X))).mp
  simp [map, cokernel.map]

instance toStable_linear : Functor.Linear k (toStable (C := C)) where
  map_smul f r := stable_map_smul f r

instance functor_linear : Functor.Linear k (functor (C := C)) := by
  have : Functor.Linear k (projectiveStableQuotient (C := C) ⋙ functor) := by
    rw [functor_spec]
    infer_instance
  exact Functor.linear_of_full_essSurj_comp (projectiveStableQuotient (C := C)) functor

end Cosyzygy

end PretriangulatedV2.StableCategory
