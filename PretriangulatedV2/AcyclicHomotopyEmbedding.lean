import PretriangulatedV2.AcyclicShiftComparison
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
The actual homotopy category of acyclic projective complexes embeds fully
faithfully in mathlib's ambient cochain homotopy category. Both quotients use
actual cochain homotopies, so no identification of morphisms is added here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace PretriangulatedV2.StableCategory.AcyclicHomotopyEmbedding

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- Inclusion of the actual complexes followed by the ambient actual
cochain-homotopy quotient. -/
def rawInclusion : StableCocycles.AcyclicProjectiveComplex C ⥤
    HomotopyCategory C (ComplexShape.up ℤ) :=
  (StableCocycles.acyclicProjectiveComplexes (C := C)).ι ⋙
    HomotopyCategory.quotient C (ComplexShape.up ℤ)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem rawInclusion_homotopy {P R : StableCocycles.AcyclicProjectiveComplex C}
    (f g : P ⟶ R) (h : StableCocycles.acyclicHomotopyRelation f g) :
    rawInclusion.map f = rawInclusion.map g :=
  HomotopyCategory.eq_of_homotopy _ _ h.some

/-- The genuine inclusion of `K_ac(P)` in the ambient homotopy category. -/
def inclusion : StableCocycles.AcyclicProjectiveHomotopyCategory C ⥤
    HomotopyCategory C (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift StableCocycles.acyclicHomotopyRelation rawInclusion
    (fun _ _ f g h => rawInclusion_homotopy f g h)

instance inclusion_full : (inclusion (C := C)).Full where
  map_surjective {P R} f := by
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
    exact ⟨(CategoryTheory.Quotient.functor StableCocycles.acyclicHomotopyRelation).map
      (ObjectProperty.homMk g), hg⟩

instance inclusion_faithful : (inclusion (C := C)).Faithful where
  map_injective {P R} f g h := by
    obtain ⟨a, ha⟩ := (CategoryTheory.Quotient.functor
      (StableCocycles.acyclicHomotopyRelation (C := C))).map_surjective f
    obtain ⟨b, hb⟩ := (CategoryTheory.Quotient.functor
      (StableCocycles.acyclicHomotopyRelation (C := C))).map_surjective g
    rw [← ha, ← hb] at h ⊢
    apply CategoryTheory.Quotient.sound
    exact ⟨HomotopyCategory.homotopyOfEq _ _ h⟩

instance rawInclusion_additive : (rawInclusion (C := C)).Additive := by
  dsimp only [rawInclusion]
  infer_instance

instance inclusion_additive : (inclusion (C := C)).Additive := by
  have : ((CategoryTheory.Quotient.functor
      (StableCocycles.acyclicHomotopyRelation (C := C))) ⋙ inclusion).Additive := by
    change (rawInclusion (C := C)).Additive
    infer_instance
  exact Functor.additive_of_full_essSurj_comp
    (CategoryTheory.Quotient.functor (StableCocycles.acyclicHomotopyRelation (C := C))) inclusion

instance rawInclusion_commShift : (rawInclusion (C := C)).CommShift ℤ := by
  dsimp only [rawInclusion]
  infer_instance

/-- The ambient embedding respects the actual integer cochain shifts with
their full addition and unit coherence. -/
instance inclusion_commShift : (inclusion (C := C)).CommShift ℤ := by
  change (CategoryTheory.Quotient.lift StableCocycles.acyclicHomotopyRelation rawInclusion
    (fun _ _ f g h => rawInclusion_homotopy f g h)).CommShift ℤ
  infer_instance

/-- The actual zero complex belongs to the actual acyclic projective
subcategory. -/
instance acyclicProjectiveComplexes_containsZero :
    (StableCocycles.acyclicProjectiveComplexes (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    refine ⟨?_, ?_⟩
    · intro n
      exact ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_isZero
        (isZero_zero _)).projective
    · intro n
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact (homologyFunctor C (ComplexShape.up ℤ) n).map_isZero (isZero_zero _)⟩

instance acyclicHomotopy_hasZeroObject :
    HasZeroObject (StableCocycles.AcyclicProjectiveHomotopyCategory C) :=
  (CategoryTheory.Quotient.functor
    (StableCocycles.acyclicHomotopyRelation (C := C))).hasZeroObject_of_additive

/-- Every actual integer shift on `K_ac(P)` is additive. -/
instance acyclicHomotopy_shift_additive (n : ℤ) :
    (shiftFunctor (StableCocycles.AcyclicProjectiveHomotopyCategory C) n).Additive := by
  have : (shiftFunctor (StableCocycles.AcyclicProjectiveHomotopyCategory C) n ⋙
      inclusion).Additive :=
    Functor.additive_of_iso ((inclusion (C := C)).commShiftIso n).symm
  exact Functor.additive_of_comp_faithful _ inclusion

end PretriangulatedV2.StableCategory.AcyclicHomotopyEmbedding
