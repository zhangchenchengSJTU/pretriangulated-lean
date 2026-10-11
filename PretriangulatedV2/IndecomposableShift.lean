import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
Indecomposability is invariant under shifts in an additive category.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The image of a binary biproduct under an additive endofunctor. -/
private def additiveMapBiprod (F : C ⥤ C) [F.Additive] (Y Z : C) :
    F.obj (Y ⊞ Z) ≅ F.obj Y ⊞ F.obj Z where
  hom := biprod.lift (F.map biprod.fst) (F.map biprod.snd)
  inv := biprod.desc (F.map biprod.inl) (F.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp, ← F.map_add,
      biprod.total, F.map_id]
  inv_hom_id := by
    ext <;> simp [← F.map_comp]

variable [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]

/-- A shift of an indecomposable object is indecomposable. -/
theorem indecomposable_shift (X : C) (n : ℤ) (hX : Indecomposable X) :
    Indecomposable (X⟦n⟧) := by
  constructor
  · intro h
    apply hX.1
    exact IsZero.of_iso ((shiftFunctor C (-n)).map_isZero h) (shiftShiftNeg X n).symm
  · intro Y Z e
    let F := shiftFunctor C (-n)
    have h := hX.2 (F.obj Y) (F.obj Z)
      ((shiftShiftNeg X n).symm ≪≫ F.mapIso e ≪≫ additiveMapBiprod F Y Z)
    rcases h with hY | hZ
    · left
      exact IsZero.of_iso ((shiftFunctor C n).map_isZero hY) (shiftNegShift Y n).symm
    · right
      exact IsZero.of_iso ((shiftFunctor C n).map_isZero hZ) (shiftNegShift Z n).symm

end PretriangulatedV2
