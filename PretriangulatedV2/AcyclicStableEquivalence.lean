import PretriangulatedV2.Frobenius
import PretriangulatedV2.StableCocycles
import PretriangulatedV2.AcyclicMapLiftingCompletion
import PretriangulatedV2.AcyclicNullHomotopyCompletion
import Mathlib.Algebra.Homology.Embedding.Connect
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Actual complete resolutions and the stable cycle equivalence

The positive half is an actual injective resolution and the negative half an
actual projective resolution. They are joined along their actual augmentation
maps. In a Frobenius abelian category all their terms are projective.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory.AcyclicStableEquivalence

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- The actual augmented projective and injective resolutions join along `X`. -/
def completeData (X : C) :
    CochainComplex.ConnectData (ProjectiveResolution.of X).complex
      (InjectiveResolution.of X).cocomplex where
  d₀ := (ProjectiveResolution.of X).π.f 0 ≫ (InjectiveResolution.of X).ι.f 0
  comp_d₀ := by
    rw [← Category.assoc, ProjectiveResolution.complex_d_comp_π_f_zero, zero_comp]
  d₀_comp := by
    rw [Category.assoc, InjectiveResolution.ι_f_zero_comp_complex_d, comp_zero]

/-- A genuine bi-infinite complete resolution. -/
def completeComplex (X : C) : CochainComplex C ℤ :=
  (completeData X).cochainComplex

omit [HasBinaryBiproducts C] in
theorem completeComplex_projective (X : C) (n : ℤ) :
    Projective ((completeComplex X).X n) := by
  cases n with
  | ofNat n =>
    change Projective ((InjectiveResolution.of X).cocomplex.X n)
    exact (FrobeniusAbelian.projective_iff_injective _).mpr inferInstance
  | negSucc n =>
    change Projective ((ProjectiveResolution.of X).complex.X n)
    infer_instance

omit [HasBinaryBiproducts C] in
/-- At the join, exactness is inherited from the injective augmentation after
precomposition by the projective augmentation epimorphism. -/
theorem completeComplex_exactAt_zero (X : C) :
    (completeComplex X).ExactAt 0 := by
  apply ((completeComplex X).exactAt_iff' (-1) 0 1 (by simp) (by simp)).mpr
  change (ShortComplex.mk
    ((ProjectiveResolution.of X).π.f 0 ≫ (InjectiveResolution.of X).ι.f 0)
    ((InjectiveResolution.of X).cocomplex.d 0 1) _).Exact
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk
      ((ProjectiveResolution.of X).π.f 0 ≫ (InjectiveResolution.of X).ι.f 0)
      ((InjectiveResolution.of X).cocomplex.d 0 1)
      (completeData X).d₀_comp)
    (S₂ := ShortComplex.mk ((InjectiveResolution.of X).ι.f 0)
      ((InjectiveResolution.of X).cocomplex.d 0 1)
      (InjectiveResolution.of X).ι_f_zero_comp_complex_d)
    { τ₁ := (ProjectiveResolution.of X).π.f 0
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }).mpr
  exact (InjectiveResolution.of X).exact₀

omit [HasBinaryBiproducts C] in
/-- Exactness at the negative side of the join follows by postcomposition
of the projective augmentation with the injective augmentation monomorphism. -/
theorem completeComplex_exactAt_negOne (X : C) :
    (completeComplex X).ExactAt (-1) := by
  apply ((completeComplex X).exactAt_iff' (-2) (-1) 0 (by simp) (by simp)).mpr
  change (ShortComplex.mk ((ProjectiveResolution.of X).complex.d 1 0)
    ((ProjectiveResolution.of X).π.f 0 ≫ (InjectiveResolution.of X).ι.f 0) _).Exact
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk ((ProjectiveResolution.of X).complex.d 1 0)
      ((ProjectiveResolution.of X).π.f 0)
      (ProjectiveResolution.of X).complex_d_comp_π_f_zero)
    (S₂ := ShortComplex.mk ((ProjectiveResolution.of X).complex.d 1 0)
      ((ProjectiveResolution.of X).π.f 0 ≫ (InjectiveResolution.of X).ι.f 0)
      (completeData X).comp_d₀)
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (InjectiveResolution.of X).ι.f 0 }).mp
  exact (ProjectiveResolution.of X).exact₀

omit [HasBinaryBiproducts C] in
/-- Away from the join, the constructed complex inherits the exactness of its
actual projective and injective resolution halves. -/
theorem completeComplex_acyclic (X : C) : (completeComplex X).Acyclic := by
  intro n
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact completeComplex_exactAt_zero X
    | succ n =>
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact ((InjectiveResolution.of X).cocomplex_exactAt_succ n).isZero_homology.of_iso
        ((completeData X).homologyIsoPos (n + 1) (Int.ofNat (n + 1)) (by rfl))
  | negSucc n =>
    cases n with
    | zero => exact completeComplex_exactAt_negOne X
    | succ n =>
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact ((ProjectiveResolution.of X).complex_exactAt_succ n).isZero_homology.of_iso
        ((completeData X).homologyIsoNeg (n + 1) (Int.negSucc (n + 1)) (by omega))

/-- The zeroth cycles are the original object by the actual injective
augmentation kernel universal property. -/
def completeComplex_cyclesZeroIso (X : C) : (completeComplex X).cycles 0 ≅ X :=
  IsLimit.conePointUniqueUpToIso
    ((completeComplex X).cyclesIsKernel 0 1 (by simp))
    (InjectiveResolution.of X).isLimitKernelFork

/-- The constructed complete resolution belongs to the actual acyclic
degreewise-projective full subcategory. -/
def completeResolution (X : C) : StableCocycles.AcyclicProjectiveComplex C :=
  ⟨completeComplex X, completeComplex_projective X, completeComplex_acyclic X⟩

instance acyclicStableCycles_essSurj :
    (StableCocycles.acyclicStableCycles (C := C)).EssSurj where
  mem_essImage := by
    rintro ⟨X⟩
    exact ⟨(CategoryTheory.Quotient.functor
      (StableCocycles.acyclicHomotopyRelation (C := C))).obj (completeResolution X),
      ⟨(projectiveStableQuotient (C := C)).mapIso (completeComplex_cyclesZeroIso X)⟩⟩

/-- Every stable cycle map lifts to an actual map of complete acyclic
projective complexes, and hence to their actual homotopy quotient. -/
instance acyclicStableCycles_full :
    (StableCocycles.acyclicStableCycles (C := C)).Full where
  map_surjective {P R} f := by
    obtain ⟨a, ha⟩ := (projectiveStableQuotient (C := C)).map_surjective f
    obtain ⟨g, hg⟩ := AcyclicMapLifting.Connecting.exists_cochainMap P.as.obj R.as.obj
      P.as.property.2 R.as.property.2 P.as.property.1 R.as.property.1 a
    refine ⟨(CategoryTheory.Quotient.functor
      (StableCocycles.acyclicHomotopyRelation (C := C))).map
        (ObjectProperty.homMk g), ?_⟩
    change (projectiveStableQuotient (C := C)).map (cyclesMap g 0) = f
    rw [hg, ha]

omit [FrobeniusAbelian C] in
/-- Stable equality gives an actual projective factorization of the cycle map
of the difference, before any homotopy construction. -/
theorem cycleDifferenceFactorsThrough {P R : CochainComplex C ℤ}
    (f g : P ⟶ R)
    (h : (projectiveStableQuotient (C := C)).map (cyclesMap f 0) =
      (projectiveStableQuotient (C := C)).map (cyclesMap g 0)) :
    FactorsThrough (projectiveObjects : C → Prop) (cyclesMap (f - g) 0) := by
  apply (functor_map_eq_zero_iff (projectiveObjects : C → Prop) _).mp
  change (projectiveStableQuotient (C := C)).map
    ((cyclesFunctor C (ComplexShape.up ℤ) 0).map (f - g)) = 0
  rw [Functor.map_sub, Functor.map_sub]
  exact sub_eq_zero.mpr h

/-- Stable equality of actual cycle maps is witnessed by an actual cochain
homotopy, using the projective factorization of their difference. -/
theorem homotopyOfStableCyclesEq {P R : CochainComplex C ℤ}
    (hP : P.Acyclic) (hR : R.Acyclic)
    (projP : ∀ n : ℤ, Projective (P.X n))
    (projR : ∀ n : ℤ, Projective (R.X n))
    (f g : P ⟶ R)
    (h : (projectiveStableQuotient (C := C)).map (cyclesMap f 0) =
      (projectiveStableQuotient (C := C)).map (cyclesMap g 0)) :
    Nonempty (Homotopy f g) := by
  obtain ⟨J, hJ, a, b, hab⟩ := cycleDifferenceFactorsThrough f g h
  let : Projective J := hJ
  obtain ⟨H⟩ := AcyclicNullHomotopyCompletion.nullHomotopyOfCycleFactorization
    (f - g) hP hR projP projR a b hab.symm
  exact ⟨(Homotopy.equivSubZero (f := f) (g := g)).symm H⟩

instance acyclicStableCycles_faithful :
    (StableCocycles.acyclicStableCycles (C := C)).Faithful where
  map_injective {P R} f g h := by
    obtain ⟨a, ha⟩ := (CategoryTheory.Quotient.functor
      (StableCocycles.acyclicHomotopyRelation (C := C))).map_surjective f
    obtain ⟨b, hb⟩ := (CategoryTheory.Quotient.functor
      (StableCocycles.acyclicHomotopyRelation (C := C))).map_surjective g
    rw [← ha, ← hb] at h ⊢
    apply CategoryTheory.Quotient.sound
    change (projectiveStableQuotient (C := C)).map (cyclesMap a.hom 0) =
      (projectiveStableQuotient (C := C)).map (cyclesMap b.hom 0) at h
    exact homotopyOfStableCyclesEq P.as.property.2 R.as.property.2
      P.as.property.1 R.as.property.1 a.hom b.hom h

instance acyclicStableCycles_isEquivalence :
    (StableCocycles.acyclicStableCycles (C := C)).IsEquivalence where

/-- The actual zero-cycle equivalence from acyclic projective complexes modulo
actual cochain homotopy to the projective stable quotient. -/
def equivalence : StableCocycles.AcyclicProjectiveHomotopyCategory C ≌
    projectiveStableCategory C :=
  (StableCocycles.acyclicStableCycles (C := C)).asEquivalence

@[simp] theorem equivalence_functor :
    (equivalence (C := C)).functor = StableCocycles.acyclicStableCycles := rfl

end PretriangulatedV2.StableCategory.AcyclicStableEquivalence
