import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import PretriangulatedV2.StableCategory

/-!
The zeroth-cycle functor on actual complexes of projective objects descends
through actual cochain homotopy to the projective stable category.  The descent
uses the degree -1 homotopy component to exhibit the difference of cycle maps
as a factorization through a projective object.

For a Frobenius abelian category, `AcyclicStableEquivalence` constructs the
zero-cycle equivalence on acyclic projective complexes. `AcyclicShiftComparison`
constructs its comparison with the canonical integer shifts.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory.StableCocycles

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]

/-- Homotopic maps induce the same stable map on zero cycles whenever the
target's degree -1 term is projective. -/
theorem cyclesMap_stable_eq_of_homotopy
    {P R : CochainComplex C ℤ} {f g : P ⟶ R} (H : Homotopy f g)
    [Projective (R.X (-1))] :
    (projectiveStableQuotient (C := C)).map (cyclesMap f 0) =
      (projectiveStableQuotient (C := C)).map (cyclesMap g 0) := by
  apply sub_eq_zero.mp
  rw [← Functor.map_sub, functor_map_eq_zero_iff]
  refine ⟨R.X (-1), inferInstance, P.iCycles 0 ≫ H.hom 0 (-1),
    R.toCycles (-1) 0, ?_⟩
  apply (cancel_mono (R.iCycles 0)).mp
  rw [Category.assoc, HomologicalComplex.toCycles_i, Preadditive.sub_comp,
    HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i,
    ← Preadditive.comp_sub]
  rw [Preadditive.comp_sub, H.comm]
  rw [Preadditive.comp_add, Preadditive.comp_add]
  rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel (0 : ℤ) 1 by
    change 0 + 1 = (1 : ℤ)
    norm_num)]
  rw [prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 by
    change -1 + 1 = (0 : ℤ)
    norm_num)]
  simp

/-- The genuine object property of having projective terms in every degree. -/
def projectiveComplexes : ObjectProperty (CochainComplex C ℤ) :=
  fun P => ∀ n : ℤ, Projective (P.X n)

/-- Actual cochain complexes of projectives, with all ambient cochain maps. -/
abbrev ProjectiveComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  (projectiveComplexes (C := C)).FullSubcategory

/-- The actual zero-cycle functor before passing to homotopy. -/
def cyclesToStable : ProjectiveComplex C ⥤ projectiveStableCategory C :=
  (projectiveComplexes (C := C)).ι ⋙
    HomologicalComplex.cyclesFunctor C (ComplexShape.up ℤ) 0 ⋙
    projectiveStableQuotient

instance cyclesFunctor_additive (i : ℤ) :
    (HomologicalComplex.cyclesFunctor C (ComplexShape.up ℤ) i).Additive where
  map_add {P R} f g := by
    change cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i
    apply (cancel_mono (R.iCycles i)).mp
    simp [cyclesMap_i, Preadditive.add_comp, Preadditive.comp_add]

instance cyclesToStable_additive : (cyclesToStable (C := C)).Additive := by
  dsimp only [cyclesToStable]
  infer_instance

/-- Equality up to an actual ambient cochain homotopy. -/
def homotopyRelation : HomRel (ProjectiveComplex C) :=
  fun {_ _} f g => Nonempty (Homotopy f.hom g.hom)

instance homotopyRelation_congruence : Congruence (homotopyRelation (C := C)) where
  equivalence :=
    { refl := fun f => ⟨Homotopy.refl f.hom⟩
      symm := fun ⟨H⟩ => ⟨H.symm⟩
      trans := fun ⟨H⟩ ⟨H'⟩ => ⟨H.trans H'⟩ }
  comp_left := fun _ _ _ ⟨H⟩ => ⟨H.compLeft _⟩
  comp_right := fun _ ⟨H⟩ => ⟨H.compRight _⟩

/-- The homotopy category of the actual degreewise-projective complexes. -/
abbrev ProjectiveHomotopyCategory (C : Type u) [Category.{v} C] [Abelian C] :=
  CategoryTheory.Quotient (homotopyRelation (C := C))

instance projectiveHomotopy_preadditive : Preadditive (ProjectiveHomotopyCategory C) :=
  CategoryTheory.Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨H⟩ ⟨H'⟩
    exact ⟨Homotopy.add H H'⟩)

instance projectiveHomotopy_quotient_additive :
    (CategoryTheory.Quotient.functor (homotopyRelation (C := C))).Additive where

/-- Taking zero cycles is well-defined on the cochain-homotopy quotient. -/
def stableCycles : ProjectiveHomotopyCategory C ⥤ projectiveStableCategory C :=
  CategoryTheory.Quotient.lift (homotopyRelation (C := C)) cyclesToStable
    (by
      intro P R f g h
      obtain ⟨H⟩ := h
      change (projectiveStableQuotient (C := C)).map (cyclesMap f.hom 0) =
        (projectiveStableQuotient (C := C)).map (cyclesMap g.hom 0)
      have : Projective (R.obj.X (-1)) := R.property (-1)
      exact cyclesMap_stable_eq_of_homotopy H)

/-- The descended functor agrees with the genuine zero-cycle functor. -/
theorem stableCycles_spec :
    CategoryTheory.Quotient.functor (homotopyRelation (C := C)) ⋙ stableCycles =
      cyclesToStable :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance stableCycles_additive : (stableCycles (C := C)).Additive := by
  have : (CategoryTheory.Quotient.functor (homotopyRelation (C := C)) ⋙
      stableCycles).Additive := by
    rw [stableCycles_spec]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp
    (CategoryTheory.Quotient.functor (homotopyRelation (C := C))) stableCycles

/-- Acyclic complexes with actual projective terms. -/
def acyclicProjectiveComplexes : ObjectProperty (CochainComplex C ℤ) :=
  fun P => (∀ n : ℤ, Projective (P.X n)) ∧ P.Acyclic

abbrev AcyclicProjectiveComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  (acyclicProjectiveComplexes (C := C)).FullSubcategory

def acyclicCyclesToStable :
    AcyclicProjectiveComplex C ⥤ projectiveStableCategory C :=
  (acyclicProjectiveComplexes (C := C)).ι ⋙
    HomologicalComplex.cyclesFunctor C (ComplexShape.up ℤ) 0 ⋙
    projectiveStableQuotient

instance acyclicCyclesToStable_additive : (acyclicCyclesToStable (C := C)).Additive := by
  dsimp only [acyclicCyclesToStable]
  infer_instance

def acyclicHomotopyRelation : HomRel (AcyclicProjectiveComplex C) :=
  fun {_ _} f g => Nonempty (Homotopy f.hom g.hom)

instance acyclicHomotopyRelation_congruence :
    Congruence (acyclicHomotopyRelation (C := C)) where
  equivalence :=
    { refl := fun f => ⟨Homotopy.refl f.hom⟩
      symm := fun ⟨H⟩ => ⟨H.symm⟩
      trans := fun ⟨H⟩ ⟨H'⟩ => ⟨H.trans H'⟩ }
  comp_left := fun _ _ _ ⟨H⟩ => ⟨H.compLeft _⟩
  comp_right := fun _ ⟨H⟩ => ⟨H.compRight _⟩

/-- The actual homotopy category `K_ac(P)` appearing in Section 4. -/
abbrev AcyclicProjectiveHomotopyCategory
    (C : Type u) [Category.{v} C] [Abelian C] :=
  CategoryTheory.Quotient (acyclicHomotopyRelation (C := C))

instance acyclicProjectiveHomotopy_preadditive :
    Preadditive (AcyclicProjectiveHomotopyCategory C) :=
  CategoryTheory.Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨H⟩ ⟨H'⟩
    exact ⟨Homotopy.add H H'⟩)

instance acyclicProjectiveHomotopy_quotient_additive :
    (CategoryTheory.Quotient.functor (acyclicHomotopyRelation (C := C))).Additive where

/-- Actual zero cycles on `K_ac(P)` descend to the genuine stable quotient. -/
def acyclicStableCycles :
    AcyclicProjectiveHomotopyCategory C ⥤ projectiveStableCategory C :=
  CategoryTheory.Quotient.lift (acyclicHomotopyRelation (C := C)) acyclicCyclesToStable
    (by
      intro P R f g h
      obtain ⟨H⟩ := h
      change (projectiveStableQuotient (C := C)).map (cyclesMap f.hom 0) =
        (projectiveStableQuotient (C := C)).map (cyclesMap g.hom 0)
      have : Projective (R.obj.X (-1)) := R.property.1 (-1)
      exact cyclesMap_stable_eq_of_homotopy H)

theorem acyclicStableCycles_spec :
    CategoryTheory.Quotient.functor (acyclicHomotopyRelation (C := C)) ⋙
      acyclicStableCycles = acyclicCyclesToStable :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance acyclicStableCycles_additive : (acyclicStableCycles (C := C)).Additive := by
  have : (CategoryTheory.Quotient.functor (acyclicHomotopyRelation (C := C)) ⋙
      acyclicStableCycles).Additive := by
    rw [acyclicStableCycles_spec]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp
    (CategoryTheory.Quotient.functor (acyclicHomotopyRelation (C := C))) acyclicStableCycles

end PretriangulatedV2.StableCategory.StableCocycles
