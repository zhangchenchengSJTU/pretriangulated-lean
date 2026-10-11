import PretriangulatedV2.PeriodicConeTruncation
import PretriangulatedV2.PeriodicTriangleConstruction

/-! Lifting zero-cycle maps and constructing periodic good fillings. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2.StableCategory.HellerObstructionAssembly

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]
variable (S : C ≌ C) [S.functor.Additive]

omit [HasBinaryBiproducts C] [S.functor.Additive] in
/-- A zero-cycle map extends to the first two terms by injectivity. -/
theorem exists_initial_square (P R : PeriodicComplexes.SComplex S)
    (hP : P.complex.ExactAt 1) (w : P.complex.cycles 0 ⟶ R.complex.cycles 0) :
    ∃ (a₀ : P.complex.X 0 ⟶ R.complex.X 0)
      (a₁ : P.complex.X 1 ⟶ R.complex.X 1),
      P.complex.iCycles 0 ≫ a₀ = w ≫ R.complex.iCycles 0 ∧
      P.complex.d 0 1 ≫ a₁ = a₀ ≫ R.complex.d 0 1 := by
  let : Injective (R.complex.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (R.projective 0)
  let : Injective (R.complex.X 1) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (R.projective 1)
  let a₀ := Injective.factorThru (w ≫ R.complex.iCycles 0) (P.complex.iCycles 0)
  have ha₀ : P.complex.iCycles 0 ≫ a₀ = w ≫ R.complex.iCycles 0 :=
    Injective.comp_factorThru _ _
  have hz : P.complex.iCycles 0 ≫ (a₀ ≫ R.complex.d 0 1) = 0 := by
    rw [← Category.assoc, ha₀, Category.assoc, R.complex.iCycles_d, comp_zero]
  let he := ComplexInjectiveExtensions.cycleSequence_shortExact P.complex 0 (by
    simpa using hP)
  let b := he.exact.descToInjective (a₀ ≫ R.complex.d 0 1) hz
  let a₁ := Injective.factorThru b (P.complex.iCycles 1)
  refine ⟨a₀, a₁, ha₀, ?_⟩
  rw [← P.complex.toCycles_i 0 1, Category.assoc]
  erw [Injective.comp_factorThru]
  exact he.exact.comp_descToInjective _ _

variable [HasShift (HellerClassification.Projectives (C := C)) ℤ]
  [HasBinaryBiproducts (HellerClassification.Projectives (C := C))]
  [∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive]
  (e : shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ) ≅
    (HellerClassification.projectiveEquivalence S).functor)

/-- TR3 and TR4 supply a good filling of a square of δ-exact projective triangles. -/
theorem exists_good_square (p : HellerExactness.Parameter S)
    (hp : letI := HellerClassification.pretriangulated S p e
      IsTriangulated (HellerClassification.Projectives (C := C)))
    (T R : Triangle (HellerClassification.Projectives (C := C)))
    (hT : T ∈ HellerClassification.distinguishedTriangles S p e)
    (hR : R ∈ HellerClassification.distinguishedTriangles S p e)
    (a : T.obj₁ ⟶ R.obj₁) (b : T.obj₂ ⟶ R.obj₂)
    (hab : T.mor₁ ≫ b = a ≫ R.mor₁) :
    ∃ m : T ⟶ R, m.hom₁ = a ∧ m.hom₂ = b ∧
      (letI := HellerClassification.pretriangulated S p e;
        letI : PreservesBinaryBiproducts
            (shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ)) :=
          preservesBinaryBiproducts_of_preservesBiproducts _;
        truncatedCone m ∈ distTriang (HellerClassification.Projectives (C := C))) := by
  let : CategoryTheory.Pretriangulated (HellerClassification.Projectives (C := C)) :=
    HellerClassification.pretriangulated S p e
  let : IsTriangulated (HellerClassification.Projectives (C := C)) := hp
  let : PreservesBinaryBiproducts
      (shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  obtain ⟨c, hc₂, hc₃⟩ := HellerClassification.complete_distinguished_triangle_morphism
    S p e T R hT hR a b hab
  let m : T ⟶ R := Triangle.homMk _ _ a b c hab hc₂ hc₃
  obtain ⟨m', hm₁, hm₂, hm⟩ := GoodFillIns.exists_good_fill_in m hT hR
  exact ⟨m', hm₁, hm₂, hm⟩

open PeriodicTriangleConstruction

/-- A triangle map on periodic truncations induces a three-term map. -/
def mapFromTruncation {D R : ThreeTerm S}
    (m : PeriodicConeTruncation.truncation S e D.sComplex ⟶
      PeriodicConeTruncation.truncation S e R.sComplex) : D.Map R where
  a₀ := m.hom₁.hom
  a₁ := m.hom₂.hom
  a₂ := m.hom₃.hom
  comm₀ := by
    have h := congrArg (fun t => t.hom) m.comm₁
    simpa only [PeriodicConeTruncation.truncation, Triangle.mk,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ThreeTerm.sComplex, ThreeTerm.complex_d₀₁] using h.symm
  comm₁ := by
    have h := congrArg (fun t => t.hom) m.comm₂
    simpa only [PeriodicConeTruncation.truncation, Triangle.mk,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ThreeTerm.sComplex, ThreeTerm.complex_d₁₂] using h.symm
  comm₂ := by
    have h := congrArg (fun t => (t ≫ e.hom.app _).hom) m.comm₃
    rw [Category.assoc, e.hom.naturality] at h
    have hD := PeriodicConeTruncation.truncation_third S e D.sComplex
    have hR := PeriodicConeTruncation.truncation_third S e R.sComplex
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h hD hR
    erw [← Category.assoc, hD] at h
    simp only [Category.assoc] at h
    erw [hR] at h
    have hiD : (D.period 3).inv = 𝟙 _ := by
      simp [ThreeTerm.period, ThreeTerm.stepIso, ThreeTerm.X]
      rfl
    have hiR : (R.period 3).inv = 𝟙 _ := by
      simp [ThreeTerm.period, ThreeTerm.stepIso, ThreeTerm.X]
      rfl
    simpa only [ObjectProperty.FullSubcategory.comp_hom,
      HellerClassification.projectiveEquivalence_map_hom, ThreeTerm.sComplex,
      ThreeTerm.complex_d₂₃, hiD, hiR,
      Category.comp_id, Category.id_comp, Category.assoc] using h.symm

omit [HasBinaryBiproducts C] [FrobeniusAbelian C]
  [HasBinaryBiproducts (HellerClassification.Projectives (C := C))]
  [∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive] in
/-- Periodic extension followed by truncation recovers the triangle map. -/
theorem truncationMap_mapFromTruncation {D R : ThreeTerm S}
    (m : PeriodicConeTruncation.truncation S e D.sComplex ⟶
      PeriodicConeTruncation.truncation S e R.sComplex) :
    PeriodicConeTruncation.truncationMap S e (P := D.sComplex) (R := R.sComplex)
      (mapFromTruncation S e m).cochainMap
      (mapFromTruncation S e m).twistMap_cochainMap = m := by
  ext <;> simp [PeriodicConeTruncation.truncationMap, mapFromTruncation]

/-- A triangulated parameter gives a periodic map with the prescribed first
two components and a δ-exact mapping cone. -/
theorem exists_good_periodic_map (p : HellerExactness.Parameter S)
    (hp : letI := HellerClassification.pretriangulated S p e
      IsTriangulated (HellerClassification.Projectives (C := C)))
    (D R : ThreeTerm S)
    (hD : PeriodicConeTruncation.truncation S e D.sComplex ∈
      HellerClassification.distinguishedTriangles S p e)
    (hR : PeriodicConeTruncation.truncation S e R.sComplex ∈
      HellerClassification.distinguishedTriangles S p e)
    (a : PeriodicConeTruncation.term S D.sComplex 0 ⟶ PeriodicConeTruncation.term S R.sComplex 0)
    (b : PeriodicConeTruncation.term S D.sComplex 1 ⟶ PeriodicConeTruncation.term S R.sComplex 1)
    (hab : (PeriodicConeTruncation.truncation S e D.sComplex).mor₁ ≫ b =
      a ≫ (PeriodicConeTruncation.truncation S e R.sComplex).mor₁) :
    ∃ (f : D.complex ⟶ R.complex) (_hf : PeriodicCone.IsPeriodic S D.sComplex R.sComplex f),
      f.f 0 = a.hom ∧ f.f 1 = b.hom ∧
      HellerExactness.DeltaExactTruncation S p ((CochainComplex.mappingCone f).d 0 1)
        ((CochainComplex.mappingCone f).d 1 2)
        ((CochainComplex.mappingCone f).d 2 3 ≫ (PeriodicCone.period S D.sComplex R.sComplex f 3).inv) := by
  obtain ⟨m, hm₀, hm₁, hm⟩ := exists_good_square S e p hp _ _ hD hR a b hab
  let A := mapFromTruncation S e m
  refine ⟨A.cochainMap, A.twistMap_cochainMap, ?_, ?_, ?_⟩
  · simp only [ThreeTerm.Map.cochainMap_zero, A, mapFromTruncation, hm₀]
  · simp only [ThreeTerm.Map.cochainMap_one, A, mapFromTruncation, hm₁]
  · apply PeriodicConeTruncation.cone_exact_of_good S e p _ A.twistMap_cochainMap
    rw [truncationMap_mapFromTruncation]
    exact hm

/-- A triangulated parameter gives a periodic map inducing the prescribed
zero-cycle map and having a δ-exact cone. -/
theorem exists_good_periodic_map_over_cycles (p : HellerExactness.Parameter S)
    (hp : letI := HellerClassification.pretriangulated S p e
      IsTriangulated (HellerClassification.Projectives (C := C)))
    (D R : ThreeTerm S) (hP : D.complex.ExactAt 1)
    (hD : PeriodicConeTruncation.truncation S e D.sComplex ∈
      HellerClassification.distinguishedTriangles S p e)
    (hR : PeriodicConeTruncation.truncation S e R.sComplex ∈
      HellerClassification.distinguishedTriangles S p e)
    (w : D.complex.cycles 0 ⟶ R.complex.cycles 0) :
    ∃ (f : D.complex ⟶ R.complex) (_hf : PeriodicCone.IsPeriodic S D.sComplex R.sComplex f),
      cyclesMap f 0 = w ∧
      HellerExactness.DeltaExactTruncation S p ((CochainComplex.mappingCone f).d 0 1)
        ((CochainComplex.mappingCone f).d 1 2)
        ((CochainComplex.mappingCone f).d 2 3 ≫ (PeriodicCone.period S D.sComplex R.sComplex f 3).inv) := by
  obtain ⟨a₀, a₁, ha₀, ha₁⟩ := exists_initial_square S D.sComplex R.sComplex hP w
  let a : PeriodicConeTruncation.term S D.sComplex 0 ⟶
      PeriodicConeTruncation.term S R.sComplex 0 := ObjectProperty.homMk a₀
  let b : PeriodicConeTruncation.term S D.sComplex 1 ⟶
      PeriodicConeTruncation.term S R.sComplex 1 := ObjectProperty.homMk a₁
  have hab : (PeriodicConeTruncation.truncation S e D.sComplex).mor₁ ≫ b =
      a ≫ (PeriodicConeTruncation.truncation S e R.sComplex).mor₁ := by
    apply ObjectProperty.hom_ext
    exact ha₁
  obtain ⟨f, hf, hf₀, _, hCf⟩ := exists_good_periodic_map S e p hp D R hD hR a b hab
  refine ⟨f, hf, ?_, hCf⟩
  apply (cancel_mono (R.complex.iCycles 0)).mp
  rw [cyclesMap_i, hf₀]
  exact ha₀

end PretriangulatedV2.StableCategory.HellerObstructionAssembly
