import PretriangulatedV2.HellerRecoveryEquivalence

/-!
Transport any actual Heller pretriangulation back through additive Yoneda,
while retaining the original integer shifts on the source category.
The original and reconstructed projective shifts are compared through the
proved Yoneda action, rather than identified by definitional equality.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2.PerturbedYonedaTransport

universe v u

variable (D : Type u) [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsIdempotentComplete D]

abbrev P := HellerClassification.Projectives (C := CoherentFunctors.Mod D)

local instance projectiveShift : HasShift (P D) ℤ :=
  YonedaHellerTransport.yonedaHasShift D

local instance projectiveShiftAdditive (n : ℤ) : (shiftFunctor (P D) n).Additive :=
  YonedaHellerTransport.shifted_additive D n

local instance : ∀ n : ℤ, (shiftFunctor (P D) n).Additive := projectiveShiftAdditive D

local instance yonedaCommShift : (YonedaHellerTransport.yonedaEquivalence D).functor.CommShift ℤ :=
  YonedaHellerTransport.yonedaCommShift D

local instance inverseCommShift : (YonedaHellerTransport.yonedaEquivalence D).inverse.CommShift ℤ :=
  (YonedaHellerTransport.yonedaEquivalence D).commShiftInverse ℤ

local instance equivalenceCommShift : (YonedaHellerTransport.yonedaEquivalence D).CommShift ℤ :=
  (YonedaHellerTransport.yonedaEquivalence D).commShift_of_functor ℤ

local instance inverseAdditive : (YonedaHellerTransport.yonedaEquivalence D).symm.functor.Additive := by
  change (YonedaHellerTransport.yonedaEquivalence D).inverse.Additive
  infer_instance

variable (p : StableCategory.FrobeniusCommutation.StableHellerParameter
  (CoherentFunctors.suspension (C := D)))

/-- The actual parameter pretriangulation for the Yoneda-transported shift. -/
@[instance_reducible]
def projectivePretriangulated : Pretriangulated (P D) :=
  HellerClassification.pretriangulated (CoherentFunctors.suspension (C := D)) p
    (YonedaHellerTransport.transportedShiftOneIso D)

/-- The resulting pretriangulation on the original category, with its original
integer shift action. All axioms come from the proved equivalence transport. -/
@[instance_reducible]
def pretriangulated : Pretriangulated D := by
  letI := projectivePretriangulated D p
  exact YonedaHellerTransport.EquivalenceTransport.pretriangulated (P D)
    (YonedaHellerTransport.yonedaEquivalence D).symm

/-- Distinguished triangles are exactly those whose actual Yoneda images are
distinguished for the parameter. -/
theorem distinguished_iff (T : Triangle D) :
    (pretriangulated D p).distinguishedTriangles T ↔
      (projectivePretriangulated D p).distinguishedTriangles
        ((YonedaHellerTransport.yonedaEquivalence D).functor.mapTriangle.obj T) := Iff.rfl

/-- If the transported source structure had octahedra, the actual parameter
structure would have octahedra too. This is the reflection used in the final
non-triangulated conclusion. -/
theorem projective_isTriangulated_of_transported :
    letI := projectivePretriangulated D p
    letI := pretriangulated D p
    IsTriangulated D → IsTriangulated (P D) := by
  let Y := YonedaHellerTransport.yonedaEquivalence D
  let := projectivePretriangulated D p
  let := pretriangulated D p
  intro hD
  have : IsTriangulated D := hD
  have hY : Y.functor.IsTriangulated := ⟨fun _ hT => hT⟩
  have : Y.symm.IsTriangulated := Equivalence.IsTriangulated.mk'' Y.symm hY
  exact IsTriangulated.of_fully_faithful_triangulated_functor Y.inverse

end PretriangulatedV2.PerturbedYonedaTransport
