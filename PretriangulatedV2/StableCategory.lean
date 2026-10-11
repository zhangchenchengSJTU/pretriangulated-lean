import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import PretriangulatedV2.QuotientAdditive

/-!
# Additive stable quotients

This file defines the additive quotient of an abelian category by morphisms
factoring through ambient categorical projective objects.  It establishes only
the additive structure of the quotient.  In particular, it does not construct
or assert a canonical pretriangulated or triangulated structure; such a
structure needs additional Frobenius-style hypotheses and data.
-/

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace PretriangulatedV2

namespace StableCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]

/-- The additive quotient by maps factoring through objects satisfying `B`. -/
abbrev quotient (B : C → Prop) [Nonempty {X : C // B X}]
    [PretriangulatedV2.IdealQuotient.ClosedUnderBinaryBiproducts B] :=
  PretriangulatedV2.IdealQuotient.category B

/-- The canonical additive quotient functor. -/
abbrev quotientFunctor (B : C → Prop) [Nonempty {X : C // B X}]
    [PretriangulatedV2.IdealQuotient.ClosedUnderBinaryBiproducts B] : C ⥤ quotient B :=
  PretriangulatedV2.IdealQuotient.functor B

/-- Ambient categorical projective objects, viewed as an object property. -/
abbrev projectiveObjects : C → Prop := CategoryTheory.Projective

instance projectiveObjects_nonempty : Nonempty {P : C // projectiveObjects P} :=
  ⟨(0 : C), inferInstance⟩

instance projectiveObjects_closedUnderBinaryBiproducts :
    PretriangulatedV2.IdealQuotient.ClosedUnderBinaryBiproducts
      (projectiveObjects : C → Prop) where
  biprod_mem hP hQ := by
    let _ : CategoryTheory.Projective _ := hP
    let _ : CategoryTheory.Projective _ := hQ
    infer_instance

/-- The additive stable quotient by ambient projective objects. -/
abbrev projectiveStableCategory (C : Type u) [Category.{v} C] [Abelian C]
    [HasBinaryBiproducts C] :=
  quotient (projectiveObjects : C → Prop)

/-- Its canonical quotient functor. -/
abbrev projectiveStableQuotient : C ⥤ projectiveStableCategory C :=
  quotientFunctor (projectiveObjects : C → Prop)

noncomputable instance projectiveStableCategory_hasZeroObject :
    HasZeroObject (projectiveStableCategory C) :=
  PretriangulatedV2.IdealQuotient.quotient_hasZeroObject (projectiveObjects : C → Prop)

noncomputable instance projectiveStableCategory_hasBinaryBiproducts :
    HasBinaryBiproducts (projectiveStableCategory C) :=
  PretriangulatedV2.IdealQuotient.quotient_hasBinaryBiproducts (projectiveObjects : C → Prop)

end StableCategory

end PretriangulatedV2
