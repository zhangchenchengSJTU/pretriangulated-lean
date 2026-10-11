import PretriangulatedV2.FrobeniusTriangulation
import PretriangulatedV2.StableLinear
import PretriangulatedV2.ShiftLinear

/-! The canonical Frobenius suspension is linear because it is naturally
isomorphic to the actual linear cosyzygy, rather than by an extra hypothesis. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.StableCategory

universe w v u

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Abelian C] [HasBinaryBiproducts C] [FrobeniusAbelian C] [Linear k C]

instance projectiveStableCategory_shift_one_linear :
    Functor.Linear k (shiftFunctor (projectiveStableCategory C) (1 : ℤ)) :=
  Functor.linear_of_iso k (cosyzygyIsoShift (C := C))

instance (priority := 100) projectiveStableCategory_shift_linear (n : ℤ) :
    Functor.Linear k (shiftFunctor (projectiveStableCategory C) n) :=
  shift_linear_of_one n

end PretriangulatedV2.StableCategory
