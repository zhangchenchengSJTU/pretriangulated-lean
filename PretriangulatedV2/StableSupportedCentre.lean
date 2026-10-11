import PretriangulatedV2.StableTriangulationLinear
import PretriangulatedV2.StableIdempotents
import PretriangulatedV2.SupportedCentre
import PretriangulatedV2.TriangleCentreTransport

/-!
The gemstone-supported centre unit on the actual Frobenius stable quotient.
Hom finiteness, split idempotents and a linear canonical suspension are proved
by the imported constructions; they are not hypotheses on a replacement
stable category. Its commutation is transported to the actual cosyzygy used
in Heller parameters.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.StableCategory

universe w v u

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Abelian C] [HasBinaryBiproducts C] [FrobeniusAbelian C] [Linear k C]
  [∀ Y Z : C, FiniteDimensional k (Y ⟶ Z)]
  {X : projectiveStableCategory C} (G : Gemstone X)

/-- The actual global supported unit, commuting with actual cosyzygy. -/
def gemstoneCentreUnit : TriangleCenterUnit (Cosyzygy.functor (C := C)) := by
  have := projectiveStableCategory_isIdempotentComplete (k := k) (C := C)
  exact TriangleCenterUnit.ofNatIso (cosyzygyIsoShift (C := C))
    (G.triangleCenterUnit (k := k))

theorem gemstoneCentreUnit_app_self :
    (gemstoneCentreUnit (k := k) G).iso.hom.app X = 𝟙 X + G.alpha := by
  have := projectiveStableCategory_isIdempotentComplete (k := k) (C := C)
  exact G.triangleCenterUnit_app_self (k := k)

theorem gemstoneCentreUnit_app_shift :
    (gemstoneCentreUnit (k := k) G).iso.hom.app (X⟦(1 : ℤ)⟧) =
      𝟙 (X⟦(1 : ℤ)⟧) + G.alpha⟦(1 : ℤ)⟧' := by
  have := projectiveStableCategory_isIdempotentComplete (k := k) (C := C)
  exact G.triangleCenterUnit_app_shift (k := k)

theorem gemstoneCentreUnit_app_middle :
    (gemstoneCentreUnit (k := k) G).iso.hom.app G.middle = 𝟙 G.middle := by
  have := projectiveStableCategory_isIdempotentComplete (k := k) (C := C)
  exact G.triangleCenterUnit_app_middle (k := k)

theorem gemstoneCentreUnit_app_cone (K : GemstoneCone G) :
    (gemstoneCentreUnit (k := k) G).iso.hom.app K.Y = 𝟙 K.Y := by
  have := projectiveStableCategory_isIdempotentComplete (k := k) (C := C)
  exact G.triangleCenterUnit_app_cone (k := k) K

end PretriangulatedV2.StableCategory
