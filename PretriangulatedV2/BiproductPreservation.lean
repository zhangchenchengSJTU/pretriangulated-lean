import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
Turn the existing additive-functor preservation theorem into the binary
biproduct instance needed by truncated cones. This removes an interface-only
extra premise when the suspension is already assumed additive.
-/

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

instance (priority := 100) preservesBinaryBiproducts_of_additive
    (F : C ⥤ D) [F.Additive] : PreservesBinaryBiproducts F := by
  have : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  constructor
  intro X Y
  exact preservesBinaryBiproduct_of_preservesBiproduct F X Y

end PretriangulatedV2
