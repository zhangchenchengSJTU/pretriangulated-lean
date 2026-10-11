import PretriangulatedV2.AutoequivalenceShift
import PretriangulatedV2.FrobeniusOctahedra

/-!
# The actual canonical triangulation of the Frobenius stable quotient

The integer shift is constructed from the proved cosyzygy autoequivalence.
The distinguished triangles are the isomorphism closure of the stable images
of ambient short exact sequences. Every pretriangulation axiom and the full
octahedron axiom were proved from ambient universal properties in the imported
triangle modules; this file installs those structures on the actual quotient.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace PretriangulatedV2.StableCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- The coherent integer shift on the actual stable quotient, constructed
from cosyzygy without assuming the existence of a shift. -/
instance projectiveStableCategory_hasShift : HasShift (projectiveStableCategory C) ℤ :=
  AutoequivalenceShift.hasShift (Cosyzygy.equivalence (C := C))

/-- All shifts of the stable quotient are additive. -/
instance projectiveStableCategory_shift_additive (n : ℤ) :
    (shiftFunctor (projectiveStableCategory C) n).Additive := by
  have : (Cosyzygy.equivalence (C := C)).functor.Additive := by
    change (Cosyzygy.functor (C := C)).Additive
    infer_instance
  exact AutoequivalenceShift.shift_additive (Cosyzygy.equivalence (C := C)) n

/-- The constructed shift by one is the genuine cosyzygy functor. -/
def cosyzygyIsoShift : Cosyzygy.functor (C := C) ≅
    shiftFunctor (projectiveStableCategory C) (1 : ℤ) :=
  (AutoequivalenceShift.shiftOneIso (Cosyzygy.equivalence (C := C))).symm

/-- The canonical pretriangulation of the actual projective stable quotient. -/
instance projectiveStableCategory_pretriangulated :
    CategoryTheory.Pretriangulated (projectiveStableCategory C) :=
  FrobeniusTriangles.pretriangulated (cosyzygyIsoShift (C := C))

/-- The canonical pretriangulation satisfies the full octahedron axiom. -/
instance projectiveStableCategory_isTriangulated :
    CategoryTheory.IsTriangulated (projectiveStableCategory C) :=
  FrobeniusTriangles.isTriangulated (cosyzygyIsoShift (C := C))

/-- The canonical triangle induced by an actual ambient short exact sequence. -/
def shortExactTriangle {S : ShortComplex C} (hS : S.ShortExact) :
    Triangle (projectiveStableCategory C) :=
  FrobeniusTriangles.triangle (cosyzygyIsoShift (C := C)) hS

/-- Ambient short exact sequences give distinguished triangles in the actual
canonical triangulation. -/
theorem shortExactTriangle_distinguished {S : ShortComplex C} (hS : S.ShortExact) :
    shortExactTriangle hS ∈ distTriang (projectiveStableCategory C) :=
  ⟨S, hS, ⟨Iso.refl _⟩⟩

/-- This describes the canonical distinguished class without a triangulation
or distinguished-triangle assumption on the ambient category. -/
theorem distinguished_iff_shortExact (T : Triangle (projectiveStableCategory C)) :
    T ∈ distTriang (projectiveStableCategory C) ↔
      ∃ (S : ShortComplex C) (hS : S.ShortExact), Nonempty (T ≅ shortExactTriangle hS) :=
  Iff.rfl

end PretriangulatedV2.StableCategory
