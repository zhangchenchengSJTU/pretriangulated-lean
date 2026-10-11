import PretriangulatedV2.IdealQuotient

universe v u

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2

namespace IdealQuotient

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

variable (B : C → Prop) [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]

/-- The ideal quotient has a zero object, represented by the image of the zero object of `C`. -/
noncomputable instance quotient_hasZeroObject : HasZeroObject (category B) :=
  Functor.hasZeroObject_of_additive (functor B)

/-- The ideal quotient has binary biproducts, represented by images of binary biproducts in `C`. -/
noncomputable instance quotient_hasBinaryBiproducts : HasBinaryBiproducts (category B) where
  has_binary_biproduct := by
    intro X Y
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    let _ : PreservesFiniteBiproducts (functor B) := inferInstance
    let _ : PreservesBiproductsOfShape WalkingPair (functor B) := inferInstance
    let _ : PreservesBinaryBiproducts (functor B) :=
      preservesBinaryBiproducts_of_preservesBiproducts (functor B)
    exact Functor.hasBinaryBiproduct_of_preserves (functor B) X Y

end IdealQuotient

end PretriangulatedV2
