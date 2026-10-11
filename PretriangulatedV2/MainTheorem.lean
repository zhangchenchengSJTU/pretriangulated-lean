import PretriangulatedV2.GemstoneNonTriangulated
import PretriangulatedV2.PerturbedYonedaTransport

/-!
Theorem 1.1 / Theorem 6.4 of the authoritative v2: a gemstone in the actual
stable category of coherent functors produces a pretriangulation failing TR4
on the original category with its original integer suspension.

The baseline parameter is recovered from the original triangulation. The
supported perturbation is an actual Heller parameter, and TR4 is reflected
through the proved additive Yoneda equivalence. No replacement category,
classification axiom, or non-triangulatedness premise is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2.MainTheorem

universe w v u

variable {k : Type w} [Field k]
  (D : Type u) [Category.{v} D] [Preadditive D] [Linear k D]
  [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [IsIdempotentComplete D]
  [∀ Y Z : D, FiniteDimensional k (Y ⟶ Z)]

abbrev StableCoherent := StableCategory.projectiveStableCategory (CoherentFunctors.Mod D)
abbrev P := HellerClassification.Projectives (C := CoherentFunctors.Mod D)

local instance projectiveShift : HasShift (P D) ℤ :=
  YonedaHellerTransport.yonedaHasShift D

local instance projectiveShiftAdditive (n : ℤ) : (shiftFunctor (P D) n).Additive :=
  YonedaHellerTransport.shifted_additive D n

local instance : ∀ n : ℤ, (shiftFunctor (P D) n).Additive := projectiveShiftAdditive D

local instance projectiveBinaryBiproducts : HasBinaryBiproducts (P D) := by
  let : HasBinaryProducts (P D) :=
    Adjunction.hasLimitsOfShape_of_equivalence (YonedaHellerTransport.yonedaEquivalence D).inverse
  exact HasBinaryBiproducts.of_hasBinaryProducts

variable {X : StableCoherent D} (G : Gemstone X)

/-- The explicit supported perturbation of the recovered original parameter. -/
def perturbedParameter : StableCategory.FrobeniusCommutation.StableHellerParameter
    (CoherentFunctors.suspension (C := D)) :=
  (HellerRecovery.coherentBaselineParameter D).twist
    (StableCategory.gemstoneCentreUnit (k := k) G)

/-- The new actual pretriangulation retains the source category's given shift. -/
@[instance_reducible]
def perturbedStructure : Pretriangulated D :=
  PerturbedYonedaTransport.pretriangulated D (perturbedParameter (k := k) D G)

/-- The constructed source structure fails the octahedral axiom. -/
theorem perturbedStructure_not_isTriangulated :
    letI := perturbedStructure (k := k) D G
    ¬ IsTriangulated D := by
  have hp := HellerRecoveryEquivalence.coherentBaselineIsTriangulated D
  have hbad := StableCategory.GemstoneNonTriangulated.theorem_6_2_generic (k := k)
    (CoherentFunctors.suspension (C := D))
    (YonedaHellerTransport.transportedShiftOneIso D)
    (HellerRecovery.coherentBaselineParameter D) G hp
  intro hD
  exact hbad (PerturbedYonedaTransport.projective_isTriangulated_of_transported
    D (perturbedParameter (k := k) D G) hD)

include k G in
/-- Theorem 1.1 / Theorem 6.4, with precisely the original category and shift. -/
theorem theorem_1_1 :
    ∃ (p : Pretriangulated D), letI := p; ¬ IsTriangulated D :=
  ⟨perturbedStructure (k := k) D G, perturbedStructure_not_isTriangulated (k := k) D G⟩

include k G in
/-- The equivalent formulation numbered Theorem 6.4 in the body. -/
theorem theorem_6_4 :
    ∃ (p : Pretriangulated D), letI := p; ¬ IsTriangulated D :=
  theorem_1_1 (k := k) D G

include k in
/-- The assumption that the stable coherent-functor category admits a gemstone
can be expressed without choosing its object or gemstone data in the theorem. -/
theorem theorem_1_1_of_exists_gemstone
    (hG : ∃ X : StableCoherent D, Nonempty (Gemstone X)) :
    ∃ (p : Pretriangulated D), letI := p; ¬ IsTriangulated D := by
  obtain ⟨X, ⟨G⟩⟩ := hG
  exact theorem_1_1 (k := k) D G

end PretriangulatedV2.MainTheorem
