import PretriangulatedV2.HellerRecovery
import PretriangulatedV2.PeriodicTriangleExactness

/-! Actual periodic realizations of arbitrary stable objects. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PretriangulatedV2.StableCategory.HellerPeriodicRealization

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]
variable (S : C ≌ C) [S.functor.Additive]
open PeriodicTriangleConstruction

/-- Splice the genuine three exact rows into cyclic three-term data. -/
abbrev extensionThreeTerm {M : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) : ThreeTerm S :=
  PeriodicTriangleExactness.ofExtension S E

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[simp] theorem period_three_inv (D : ThreeTerm S) : (D.period 3).inv = 𝟙 _ :=
  PeriodicTriangleExactness.period_three_inv S D

/-- Its true periodic complex has exactly the original δ-exact truncation. -/
theorem extension_deltaExact (p : HellerExactness.Parameter S) {M : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M))
    (hE : HellerExactness.DeltaExact S p E) :
    HellerExactness.DeltaExactTruncation S p
      ((extensionThreeTerm S E).complex.d 0 1)
      ((extensionThreeTerm S E).complex.d 1 2)
      ((extensionThreeTerm S E).complex.d 2 3 ≫ ((extensionThreeTerm S E).period 3).inv) :=
  PeriodicTriangleExactness.truncation_of_threeTerm S p (extensionThreeTerm S E)
    (HellerExactness.deltaExactTruncation_of_extension S p E hE)

/-- The initial object is isomorphic to the actual zero cycles by the
proved kernel universal property of the genuine first exact row. -/
def extensionCycleIso {M : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    M ≅ (extensionThreeTerm S E).complex.cycles 0 :=
  PeriodicTriangleExactness.zeroCycleIso S E

/-- A periodic δ-exact complex on every ambient object, obtained from the
actual chosen first two injective presentations and the prescribed boundary. -/
def realization (p : HellerExactness.Parameter S) (M : C) : ThreeTerm S :=
  extensionThreeTerm S (HellerClassification.completeMorphism S p
    (HellerRecovery.chosenDifferential M).hom)

/-- Its actual zero cycles are isomorphic to the prescribed object. -/
def realizationCycleIso (p : HellerExactness.Parameter S) (M : C) :
    M ≅ (realization S p M).complex.cycles 0 :=
  HellerRecovery.chosenKernelIso M ≪≫ extensionCycleIso S _

theorem realization_deltaExact (p : HellerExactness.Parameter S) (M : C) :
    HellerExactness.DeltaExactTruncation S p ((realization S p M).complex.d 0 1)
      ((realization S p M).complex.d 1 2)
      ((realization S p M).complex.d 2 3 ≫ ((realization S p M).period 3).inv) :=
  extension_deltaExact S p _ (HellerClassification.completeMorphism_deltaExact S p _)

end PretriangulatedV2.StableCategory.HellerPeriodicRealization
