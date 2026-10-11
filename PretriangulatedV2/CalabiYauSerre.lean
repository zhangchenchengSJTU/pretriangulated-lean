import PretriangulatedV2.StableSerreDuality
import PretriangulatedV2.HellerClassification
import PretriangulatedV2.ShiftLinear
import PretriangulatedV2.StableTriangulationLinear
import PretriangulatedV2.GeneratorCommShift

/-!
# Passing Calabi--Yau Serre data from projectives to the stable category

A genuine Serre duality on the full projective subcategory is transported
through its natural comparison with an ambient autoequivalence. This produces
the original projective-projective pairings used by the proved stable Serre
construction. No almost-vanishing or stable Serre conclusion is assumed.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace PretriangulatedV2.CalabiYauSerre

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Abelian C] [HasBinaryBiproducts C] [FrobeniusAbelian C] [Linear k C]

open HellerClassification

/-- The linear identification of actual full-subcategory Hom with ambient Hom. -/
def projectiveHomEquiv (P Q : Projectives (C := C)) :
    (P ⟶ Q) ≃ₗ[k] (P.obj ⟶ Q.obj) := InducedCategory.homLinearEquiv

/-- Linear transport in the codomain along an actual isomorphism. -/
def postcomposeIso {X Y Z : C} (e : Y ≅ Z) : (X ⟶ Y) ≃ₗ[k] (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.add_comp]
  map_smul' r f := by simp

variable (S : C ≌ C) [S.functor.Additive] [Functor.Linear k S.functor]
  (R : SerreDuality k (Projectives (C := C)))
  (γ : R.equivalence.functor ⋙ (projectives (C := C)).ι ≅
    (projectives (C := C)).ι ⋙ S.functor)

/-- Actual ambient projectives with their true projectivity proofs. -/
def asProjective (P : C) [CategoryTheory.Projective P] : Projectives (C := C) :=
  ⟨P, by change CategoryTheory.Projective P; infer_instance⟩

/-- The raw projective pairing obtained from the original Serre/CY pairing
and its natural ambient comparison. -/
def projectiveDuality : ProjectiveSerreDuality k C S.functor where
  duality P Q :=
    (((postcomposeIso (k := k) ((γ.app (asProjective P)).symm)).trans
        (projectiveHomEquiv (asProjective Q)
          (R.equivalence.functor.obj (asProjective P))).symm).trans
        (R.duality (asProjective P) (asProjective Q))).trans
      (projectiveHomEquiv (asProjective P) (asProjective Q)).symm.dualMap
  naturality_source := by
    intro P P' Q _ _ _ f g a
    let p := asProjective P
    let p' := asProjective P'
    let q := asProjective Q
    let f' : p' ⟶ p := ObjectProperty.homMk f
    let g' : p ⟶ q := ObjectProperty.homMk g
    have hγ : S.functor.map f ≫ γ.inv.app p =
        γ.inv.app p' ≫ (R.equivalence.functor.map f').hom := γ.inv.naturality f'
    change R.duality p q (ObjectProperty.homMk ((a ≫ S.functor.map f) ≫ γ.inv.app p)) g' =
      R.duality p' q (ObjectProperty.homMk (a ≫ γ.inv.app p')) (f' ≫ g')
    rw [Category.assoc, hγ, ← Category.assoc]
    exact R.naturality_source f' g' (ObjectProperty.homMk (a ≫ γ.inv.app p'))
  naturality_target := by
    intro P Q Q' _ _ _ f g a
    let p := asProjective P
    let q := asProjective Q
    let q' := asProjective Q'
    let f' : q ⟶ q' := ObjectProperty.homMk f
    let g' : p ⟶ q := ObjectProperty.homMk g
    change R.duality p q (ObjectProperty.homMk ((f ≫ a) ≫ γ.inv.app p)) g' =
      R.duality p q' (ObjectProperty.homMk (a ≫ γ.inv.app p)) (g' ≫ f')
    have he : (ObjectProperty.homMk ((f ≫ a) ≫ γ.inv.app p) :
        q ⟶ R.equivalence.functor.obj p) = f' ≫ ObjectProperty.homMk (a ≫ γ.inv.app p) := by
      apply ObjectProperty.hom_ext
      simp [f', Category.assoc]
    rw [he]
    exact R.naturality_target f' g' (ObjectProperty.homMk (a ≫ γ.inv.app p))

/-- The actual inverse cosyzygy is naturally the canonical shift by `-1`. -/
def omegaIsoShift :
    (StableCategory.Cosyzygy.equivalence (C := C)).inverse ≅
      shiftFunctor (StableCategory.projectiveStableCategory C) (-1 : ℤ) :=
  Iso.isoInverseOfIsoFunctor
    (G := StableCategory.Cosyzygy.equivalence (C := C))
    (G' := shiftEquiv (StableCategory.projectiveStableCategory C) (1 : ℤ))
    (StableCategory.cosyzygyIsoShift (C := C))

variable [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- The original projective Serre data give genuine stable Serre duality. -/
def stableSerre : SerreDuality k (StableCategory.projectiveStableCategory C) :=
  StableCategory.StableSerreDuality.serreDuality S (projectiveDuality S R γ)

/-- A proved stable identification of the ambient Serre extension converts
the genuine stable Serre functor into the expected canonical shift. -/
def stableSerreIsoShift (n : ℤ)
    (e : StableCategory.stableFunctor S.functor ≅
      shiftFunctor (StableCategory.projectiveStableCategory C) n) :
    (stableSerre S R γ).equivalence.functor ≅
      shiftFunctor (StableCategory.projectiveStableCategory C) (n - 1) :=
  StableCategory.StableSerreDuality.serreIsoOmega S (projectiveDuality S R γ) ≪≫
    Functor.isoWhiskerRight e (StableCategory.Cosyzygy.equivalence (C := C)).inverse ≪≫
    Functor.isoWhiskerLeft _ (omegaIsoShift (C := C)) ≪≫
    (shiftFunctorAdd' (StableCategory.projectiveStableCategory C) n (-1 : ℤ) (n - 1)
      (by omega)).symm

section Powers

variable (T : C ≌ C) [T.functor.Additive] [Functor.Linear k T.functor]

/-- The actual projective inclusion comparison at the generator. -/
def projectiveInclusionGenerator :
    letI := projectiveHasShift T
    shiftFunctor (Projectives (C := C)) (1 : ℤ) ⋙ (projectives (C := C)).ι ≅
      (projectives (C := C)).ι ⋙ T.functor :=
  Functor.isoWhiskerRight (projectiveShiftOneIso T) _

/-- Every projective suspension has its actual ambient extension. -/
def projectiveInclusionPower (d : ℤ) :
    letI := projectiveHasShift T
    letI := AutoequivalenceShift.hasShift T
    shiftFunctor (Projectives (C := C)) d ⋙ (projectives (C := C)).ι ≅
      (projectives (C := C)).ι ⋙ shiftFunctor C d := by
  letI := projectiveHasShift T
  letI := AutoequivalenceShift.hasShift T
  letI := GeneratorCommShift.commutation T (projectives (C := C)).ι
    (projectiveInclusionGenerator T)
  exact (projectives (C := C)).ι.commShiftIso d

/-- Original CY data, rather than a stable Serre conclusion, determine the
ambient comparison of the projective Serre functor. -/
def calabiYauAmbientComparison (d : ℤ)
    (R₀ : SerreDuality k (Projectives (C := C)))
    (hCY : letI := projectiveHasShift T
      R₀.equivalence.functor ≅ shiftFunctor (Projectives (C := C)) d) :
    letI := AutoequivalenceShift.hasShift T
    R₀.equivalence.functor ⋙ (projectives (C := C)).ι ≅
      (projectives (C := C)).ι ⋙ shiftFunctor C d :=
  Functor.isoWhiskerRight hCY _ ≪≫ projectiveInclusionPower T d

/-- Natural isomorphisms of endofunctors also compare their actual cubes. -/
def cubeIso {F G : C ⥤ C} (e : F ≅ G) : cube F ≅ cube G :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight e F ≪≫ Functor.isoWhiskerLeft G e) F ≪≫
    Functor.isoWhiskerLeft (G ⋙ G) e

/-- The actual stable Heller parameter identifies the ambient generator
with the third canonical suspension. -/
def stableGeneratorIso (p : StableCategory.FrobeniusCommutation.StableHellerParameter T) :
    StableCategory.stableFunctor T.functor ≅
      shiftFunctor (StableCategory.projectiveStableCategory C) (3 : ℤ) :=
  p.delta ≪≫ cubeIso (StableCategory.cosyzygyIsoShift (C := C)) ≪≫
    Functor.isoWhiskerRight
      (shiftFunctorAdd' (StableCategory.projectiveStableCategory C) (1 : ℤ) 1 2
        (by omega)).symm _ ≪≫
      (shiftFunctorAdd' (StableCategory.projectiveStableCategory C) (2 : ℤ) 1 3
        (by omega)).symm

/-- The ambient quotient comparison at the actual generator. -/
def quotientGenerator (p : StableCategory.FrobeniusCommutation.StableHellerParameter T) :
    letI := AutoequivalenceShift.hasShift T
    shiftFunctor C (1 : ℤ) ⋙ StableCategory.projectiveStableQuotient (C := C) ≅
      StableCategory.projectiveStableQuotient (C := C) ⋙
        shiftFunctor (StableCategory.projectiveStableCategory C) (3 : ℤ) :=
  Functor.isoWhiskerRight (AutoequivalenceShift.shiftOneIso T) _ ≪≫
    (eqToIso (StableCategory.stableFunctor_spec T.functor)).symm ≪≫
    Functor.isoWhiskerLeft _ (stableGeneratorIso T p)

/-- A natural quotient comparison descends through the genuine full stable
quotient; its components and naturality use actual ambient representatives. -/
def descendQuotientIso (F : C ⥤ C) [F.Additive] [F.PreservesProjectiveObjects]
    (G : StableCategory.projectiveStableCategory C ⥤
      StableCategory.projectiveStableCategory C)
    (e : F ⋙ StableCategory.projectiveStableQuotient (C := C) ≅
      StableCategory.projectiveStableQuotient (C := C) ⋙ G) :
    StableCategory.stableFunctor F ≅ G :=
  NatIso.ofComponents (fun X => e.app X.as) (by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨f, rfl⟩ := (StableCategory.projectiveStableQuotient (C := C)).map_surjective f
    exact e.hom.naturality f)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [T.functor.Additive] in
/-- All ambient powers inherit linearity from the original autoequivalence. -/
theorem generatedShiftLinear (d : ℤ) :
    letI := AutoequivalenceShift.hasShift T
    Functor.Linear k (shiftFunctor C d) := by
  let := AutoequivalenceShift.hasShift T
  have : Functor.Linear k (shiftFunctor C (1 : ℤ)) :=
    Functor.linear_of_iso k (AutoequivalenceShift.shiftOneIso T).symm
  exact shift_linear_of_one (k := k) d

/-- The Heller generator comparison commutes with every actual power, using
the generated action of the third stable suspension on the target. -/
def quotientPowerGenerated
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter T) (d : ℤ) :
    let E := shiftEquiv (StableCategory.projectiveStableCategory C) (3 : ℤ)
    letI := AutoequivalenceShift.hasShift T
    letI := AutoequivalenceShift.hasShift E
    shiftFunctor C d ⋙ StableCategory.projectiveStableQuotient (C := C) ≅
      StableCategory.projectiveStableQuotient (C := C) ⋙
        shiftFunctor (StableCategory.projectiveStableCategory C) d := by
  let E := shiftEquiv (StableCategory.projectiveStableCategory C) (3 : ℤ)
  letI := AutoequivalenceShift.hasShift T
  letI := AutoequivalenceShift.hasShift E
  letI := GeneratorCommShift.commutation E
    (StableCategory.projectiveStableQuotient (C := C)) (quotientGenerator T p)
  exact (StableCategory.projectiveStableQuotient (C := C)).commShiftIso d

/-- The generated action of the third stable suspension is the actual
canonical suspension by `3d`, for every positive or negative integer. -/
def quotientPowerIso
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter T) (d : ℤ) :
    letI := AutoequivalenceShift.hasShift T
    shiftFunctor C d ⋙ StableCategory.projectiveStableQuotient (C := C) ≅
      StableCategory.projectiveStableQuotient (C := C) ⋙
        shiftFunctor (StableCategory.projectiveStableCategory C) (3 * d) :=
  quotientPowerGenerated T p d ≪≫ Functor.isoWhiskerLeft _
    (GeneratorCommShift.generatedShiftIsoCanonical
      (C := StableCategory.projectiveStableCategory C) (3 : ℤ) d)

/-- All actual ambient powers descend to the canonical stable shifts forced
by the Heller parameter. -/
def stablePowerIso
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter T) (d : ℤ) :
    letI := AutoequivalenceShift.hasShift T
    letI := AutoequivalenceShift.shift_additive T d
    StableCategory.stableFunctor (shiftFunctor C d) ≅
      shiftFunctor (StableCategory.projectiveStableCategory C) (3 * d) := by
  letI := AutoequivalenceShift.hasShift T
  letI := AutoequivalenceShift.shift_additive T d
  exact descendQuotientIso (shiftFunctor C d) _ (quotientPowerIso T p d)

/-- The original CY pairing gives a genuine stable Serre duality for the
ambient extension of the `d`-th projective suspension. -/
def calabiYauStableSerre (d : ℤ)
    (R₀ : SerreDuality k (Projectives (C := C)))
    (hCY : letI := projectiveHasShift T
      R₀.equivalence.functor ≅ shiftFunctor (Projectives (C := C)) d) :
    SerreDuality k (StableCategory.projectiveStableCategory C) := by
  letI := AutoequivalenceShift.hasShift T
  have : (shiftEquiv C d).functor.Additive := by
    change (shiftFunctor C d).Additive
    exact AutoequivalenceShift.shift_additive T d
  have : Functor.Linear k (shiftEquiv C d).functor := generatedShiftLinear (k := k) T d
  exact stableSerre (shiftEquiv C d) R₀ (calabiYauAmbientComparison T d R₀ hCY)

/-- Genuine projective `d`-Calabi--Yau duality and the actual Heller parameter
produce stable Serre duality with functor `Σ^(3d-1) = Ω^(1-3d)`.
Neither stable Serre duality nor this natural comparison is an input. -/
def calabiYauStableSerreIso
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter T) (d : ℤ)
    (R₀ : SerreDuality k (Projectives (C := C)))
    (hCY : letI := projectiveHasShift T
      R₀.equivalence.functor ≅ shiftFunctor (Projectives (C := C)) d) :
    (calabiYauStableSerre T d R₀ hCY).equivalence.functor ≅
      shiftFunctor (StableCategory.projectiveStableCategory C) (3 * d - 1) := by
  letI := AutoequivalenceShift.hasShift T
  have : (shiftEquiv C d).functor.Additive := by
    change (shiftFunctor C d).Additive
    exact AutoequivalenceShift.shift_additive T d
  have : Functor.Linear k (shiftEquiv C d).functor := generatedShiftLinear (k := k) T d
  exact stableSerreIsoShift (shiftEquiv C d) R₀
    (calabiYauAmbientComparison T d R₀ hCY) (3 * d) (stablePowerIso T p d)

end Powers

end PretriangulatedV2.CalabiYauSerre
