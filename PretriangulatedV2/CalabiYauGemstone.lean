import PretriangulatedV2.CalabiYauSerre
import PretriangulatedV2.PeriodicGemstone

/-!
# Proposition 7.1 from original Calabi--Yau and periodic-resolution data

The projective Serre data and their original Calabi--Yau comparison construct
stable Serre duality and its canonical shift internally. Oddness then gives
the fixed-object comparison through the proved two-periodicity. The resulting
almost-vanishing morphism and all three gemstone properties are derived.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.StableCategory.CalabiYauGemstone

universe w v u

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Abelian C] [HasBinaryBiproducts C] [FrobeniusAbelian C] [Linear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
  {M L : C} [Projective M] [Projective L]

/-- Proposition 7.1 on the actual stable quotient. All Serre, fixed-object,
almost-vanishing, almost-split and gemstone conclusions are constructed from
the original projective CY/Heller and periodic-resolution hypotheses. -/
theorem exists_gemstone
    (T : C ≌ C) [T.functor.Additive] [Functor.Linear k T.functor]
    (p : FrobeniusCommutation.StableHellerParameter T)
    (d : ℤ) (hd : Odd d)
    (R : SerreDuality k (HellerClassification.Projectives (C := C)))
    (hCY : letI := HellerClassification.projectiveHasShift T
      R.equivalence.functor ≅ shiftFunctor (HellerClassification.Projectives (C := C)) d)
    (D : PeriodicResolution.Data M L)
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    (hcomm : ∀ a b : End M, a * b = b * a) (hfield : ¬ IsField (End M))
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧ PeriodicResolution.restrictM c = a) :
    Nonempty (Gemstone ((projectiveStableQuotient (C := C)).obj D.X)) :=
  PeriodicGemstone.exists_gemstone_of_odd_serre_shift (k := k) D
    (CalabiYauSerre.calabiYauStableSerre T d R hCY)
    hM hL hiota hq hcomm hfield hcentral d hd
    (CalabiYauSerre.calabiYauStableSerreIso T p d R hCY)

end PretriangulatedV2.StableCategory.CalabiYauGemstone
