import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import PretriangulatedV2.StableCategory

/-!
# Frobenius abelian categories

The class below records the ambient categorical data needed for the additive
stable quotient: enough projectives, enough injectives, and equality of these
two object classes.  It deliberately contains no chosen suspension, class of
triangles, or triangulation axiom.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2

/-- An abelian category with enough projectives and injectives whose projective
and injective objects agree. -/
class FrobeniusAbelian (C : Type u) [Category.{v} C] [Abelian C] : Prop where
  enoughProjectives : CategoryTheory.EnoughProjectives C
  enoughInjectives : CategoryTheory.EnoughInjectives C
  projective_iff_injective (X : C) :
    CategoryTheory.Projective X ↔ CategoryTheory.Injective X

attribute [instance] FrobeniusAbelian.enoughProjectives
attribute [instance] FrobeniusAbelian.enoughInjectives

namespace StableCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]

/-- A projective object has zero identity after passage to the stable quotient. -/
lemma projectiveStableQuotient_map_id_eq_zero (P : C) [CategoryTheory.Projective P] :
    (projectiveStableQuotient (C := C)).map (𝟙 P) = 0 := by
  rw [PretriangulatedV2.IdealQuotient.functor_map_eq_zero_iff]
  exact ⟨P, inferInstance, 𝟙 P, 𝟙 P, by simp⟩

/-- Projective objects become zero objects in the additive stable quotient. -/
lemma isZero_projectiveStableQuotient_obj (P : C) [CategoryTheory.Projective P] :
    IsZero ((projectiveStableQuotient (C := C)).obj P) := by
  rw [IsZero.iff_id_eq_zero]
  simpa using projectiveStableQuotient_map_id_eq_zero (C := C) P

/-- In a Frobenius abelian category, injective objects have zero identity in the
projective stable quotient. -/
lemma injectiveStableQuotient_map_id_eq_zero [FrobeniusAbelian C]
    (I : C) [CategoryTheory.Injective I] :
    (projectiveStableQuotient (C := C)).map (𝟙 I) = 0 := by
  let _ : CategoryTheory.Projective I :=
    (FrobeniusAbelian.projective_iff_injective I).mpr inferInstance
  exact projectiveStableQuotient_map_id_eq_zero (C := C) I

/-- In a Frobenius abelian category, injective objects become zero objects in
the projective stable quotient. -/
lemma isZero_injectiveStableQuotient_obj [FrobeniusAbelian C]
    (I : C) [CategoryTheory.Injective I] :
    IsZero ((projectiveStableQuotient (C := C)).obj I) := by
  rw [IsZero.iff_id_eq_zero]
  simpa using injectiveStableQuotient_map_id_eq_zero (C := C) I

end StableCategory

end PretriangulatedV2
