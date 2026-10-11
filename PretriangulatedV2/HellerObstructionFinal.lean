import PretriangulatedV2.HellerObstructionAssembly
import PretriangulatedV2.HellerPeriodicRealization
import PretriangulatedV2.PeriodicTriangleExactness

/-! Periodic realizations and good fillings for Heller's lightning-flash obstruction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2.StableCategory.HellerObstructionFinal

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]
variable (S : C ≌ C) [S.functor.Additive]
open PeriodicTriangleConstruction
abbrev Q := projectiveStableQuotient (C := C)
abbrev F := Cosyzygy.functor (C := C)

omit [S.functor.Additive] in
/-- Naturality transports an identity component along a stable isomorphism. -/
theorem unit_component_of_iso (u : TriangleCenterUnit F)
    {A B : projectiveStableCategory C} (e : A ≅ B)
    (h : u.iso.hom.app A = 𝟙 _) : u.iso.hom.app B = 𝟙 _ := by
  apply (cancel_epi e.hom).mp
  change e.hom ≫ u.iso.hom.app B = e.hom ≫ 𝟙 B
  have hn := u.iso.hom.naturality e.hom
  dsimp only [Functor.id_map] at hn
  simpa only [h, Category.id_comp, Category.comp_id] using hn

/-- A distinguished triangle is isomorphic to the stable cone triangle when
their first arrows agree under the zero-cycle isomorphisms. -/
def coneTriangleIso (D R : PeriodicComplexes.SComplex S)
    (f : D.complex ⟶ R.complex) (hD : D.complex.Acyclic)
    (T : Triangle (projectiveStableCategory C)) (hT : T ∈ distTriang (projectiveStableCategory C))
    (iU : T.obj₁ ≅ Q.obj (D.complex.cycles 0))
    (iY : T.obj₂ ≅ Q.obj (R.complex.cycles 0))
    (hw : T.mor₁ ≫ iY.hom = iU.hom ≫ Q.map (cyclesMap f 0)) :
    letI : Injective (D.complex.X 0) :=
      (FrobeniusAbelian.projective_iff_injective _).mp (D.projective 0)
    T ≅ MappingConeCycles.triangle f hD := by
  letI : Injective (D.complex.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (D.projective 0)
  exact isoTriangleOfIso₁₂ T _ hT (MappingConeCycles.triangle_distinguished f hD)
    iU iY hw

omit [FrobeniusAbelian C] [S.functor.Additive] in
/-- Faithfulness of the cycle functor reflects stable cycle equality
to a cochain homotopy. -/
theorem homotopy_of_stable_cycles_eq
    [(StableCocycles.acyclicStableCycles (C := C)).Faithful]
    (D R : PeriodicComplexes.SComplex S) (hD : D.complex.Acyclic) (hR : R.complex.Acyclic)
    (f g : D.complex ⟶ R.complex)
    (hfg : Q.map (cyclesMap f 0) = Q.map (cyclesMap g 0)) : Nonempty (Homotopy f g) := by
  let P : StableCocycles.AcyclicProjectiveComplex C := ⟨D.complex, D.projective, hD⟩
  let Q' : StableCocycles.AcyclicProjectiveComplex C := ⟨R.complex, R.projective, hR⟩
  let f' : P ⟶ Q' := ObjectProperty.homMk f
  let g' : P ⟶ Q' := ObjectProperty.homMk g
  apply (CategoryTheory.Quotient.functor_map_eq_iff
    (StableCocycles.acyclicHomotopyRelation (C := C)) f' g').mp
  apply (StableCocycles.acyclicStableCycles (C := C)).map_injective
  exact hfg

variable [HasShift (HellerClassification.Projectives (C := C)) ℤ]
  [HasBinaryBiproducts (HellerClassification.Projectives (C := C))]
  [∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive]
  (e : shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ) ≅
    (HellerClassification.projectiveEquivalence S).functor)

/-- The two triangulated parameters give periodic good fillings of the same
zero-cycle map, with δ-exact cones for their respective parameters. -/
theorem exists_good_pair (p : HellerExactness.Parameter S) (u : TriangleCenterUnit F)
    (hp : letI := HellerClassification.pretriangulated S p e
      IsTriangulated (HellerClassification.Projectives (C := C)))
    (hpu : letI := HellerClassification.pretriangulated S (p.twist u) e
      IsTriangulated (HellerClassification.Projectives (C := C)))
    (D R : ThreeTerm S) (hP : D.complex.ExactAt 1)
    (hD : HellerExactness.DeltaExactTruncation S p D.f D.g D.h)
    (hR : HellerExactness.DeltaExactTruncation S p R.f R.g R.h)
    (huD : u.iso.hom.app (Q.obj (D.complex.cycles 0)) = 𝟙 _)
    (huR : u.iso.hom.app (Q.obj (R.complex.cycles 0)) = 𝟙 _)
    (w : D.complex.cycles 0 ⟶ R.complex.cycles 0) :
    ∃ (f g : D.complex ⟶ R.complex)
      (_hf : PeriodicCone.IsPeriodic S D.sComplex R.sComplex f)
      (_hg : PeriodicCone.IsPeriodic S D.sComplex R.sComplex g),
      cyclesMap f 0 = w ∧ cyclesMap g 0 = w ∧
      HellerExactness.DeltaExactTruncation S p ((CochainComplex.mappingCone f).d 0 1)
        ((CochainComplex.mappingCone f).d 1 2)
        ((CochainComplex.mappingCone f).d 2 3 ≫ (PeriodicCone.period S D.sComplex R.sComplex f 3).inv) ∧
      HellerExactness.DeltaExactTruncation S (p.twist u) ((CochainComplex.mappingCone g).d 0 1)
        ((CochainComplex.mappingCone g).d 1 2)
        ((CochainComplex.mappingCone g).d 2 3 ≫ (PeriodicCone.period S D.sComplex R.sComplex g 3).inv) := by
  have hD' := PeriodicTriangleExactness.truncation_of_threeTerm S p D hD
  have hR' := PeriodicTriangleExactness.truncation_of_threeTerm S p R hR
  have htD := HellerObstruction.twisted_exact_of_unit_component S p u D.sComplex huD hD'
  have htR := HellerObstruction.twisted_exact_of_unit_component S p u R.sComplex huR hR'
  have hd := (PeriodicConeTruncation.truncation_distinguished_iff S e p D.sComplex).mpr hD'
  have hr := (PeriodicConeTruncation.truncation_distinguished_iff S e p R.sComplex).mpr hR'
  have htd :=
    (PeriodicConeTruncation.truncation_distinguished_iff S e (p.twist u) D.sComplex).mpr htD
  have htr :=
    (PeriodicConeTruncation.truncation_distinguished_iff S e (p.twist u) R.sComplex).mpr htR
  obtain ⟨f, hf, hfw, hCf⟩ := HellerObstructionAssembly.exists_good_periodic_map_over_cycles
    S e p hp D R hP hd hr w
  obtain ⟨g, hg, hgw, hCg⟩ := HellerObstructionAssembly.exists_good_periodic_map_over_cycles
    S e (p.twist u) hpu D R hP htd htr w
  exact ⟨f, g, hf, hg, hfw, hgw, hCf, hCg⟩

/-- Periodic realizations, good fillings, and cycle-functor faithfulness imply
the lightning-flash obstruction for any supplied projective shift. -/
theorem proposition_4_2_generic_of_faithful_cycles
    [(StableCocycles.acyclicStableCycles (C := C)).Faithful]
    (p : HellerExactness.Parameter S) (u : TriangleCenterUnit F)
    (hp : letI := HellerClassification.pretriangulated S p e
      IsTriangulated (HellerClassification.Projectives (C := C)))
    (hpu : letI := HellerClassification.pretriangulated S (p.twist u) e
      IsTriangulated (HellerClassification.Projectives (C := C)))
    (T : Triangle (projectiveStableCategory C)) (hT : T ∈ distTriang (projectiveStableCategory C))
    (hU : u.iso.hom.app T.obj₁ - 𝟙 _ = 0)
    (hY : u.iso.hom.app T.obj₂ - 𝟙 _ = 0) :
    IsLightningFlash T T (u.iso.hom.app T.obj₃ - 𝟙 _) := by
  let D := HellerPeriodicRealization.realization S p T.obj₁.as
  let R := HellerPeriodicRealization.realization S p T.obj₂.as
  have hD : HellerExactness.DeltaExactTruncation S p D.f D.g D.h :=
    HellerExactness.deltaExactTruncation_of_extension S p _
      (HellerClassification.completeMorphism_deltaExact S p _)
  have hR : HellerExactness.DeltaExactTruncation S p R.f R.g R.h :=
    HellerExactness.deltaExactTruncation_of_extension S p _
      (HellerClassification.completeMorphism_deltaExact S p _)
  have hDa := PeriodicTriangleExactness.threeTerm_acyclic S p D hD
  have hRa := PeriodicTriangleExactness.threeTerm_acyclic S p R hR
  let iU : T.obj₁ ≅ Q.obj (D.complex.cycles 0) :=
    Q.mapIso (HellerPeriodicRealization.realizationCycleIso S p T.obj₁.as)
  let iY : T.obj₂ ≅ Q.obj (R.complex.cycles 0) :=
    Q.mapIso (HellerPeriodicRealization.realizationCycleIso S p T.obj₂.as)
  have huD := unit_component_of_iso u iU (sub_eq_zero.mp hU)
  have huR := unit_component_of_iso u iY (sub_eq_zero.mp hY)
  let w := Q.preimage (iU.inv ≫ T.mor₁ ≫ iY.hom)
  obtain ⟨f, g, hf, hg, hfw, hgw, hCf, hCg⟩ :=
    exists_good_pair S e p u hp hpu D R (hDa 1) hD hR huD huR w
  have hfg : Q.map (cyclesMap f 0) = Q.map (cyclesMap g 0) := by rw [hfw, hgw]
  obtain ⟨H⟩ := homotopy_of_stable_cycles_eq S D.sComplex R.sComplex hDa hRa f g hfg
  let : Injective (D.complex.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (D.sComplex.projective 0)
  have hl := HellerObstruction.cone_component_isLightningFlash S p u D.sComplex R.sComplex
    f g hf hg hDa H hCf hCg
  have hw : T.mor₁ ≫ iY.hom = iU.hom ≫ Q.map (cyclesMap f 0) := by
    rw [hfw, Q.map_preimage]
    simp
  exact HellerObstruction.component_isLightningFlash_of_triangleIso u
    (coneTriangleIso S D.sComplex R.sComplex f hDa T hT iU iY hw) hl

omit [HasShift (HellerClassification.Projectives (C := C)) ℤ]
  [HasBinaryBiproducts (HellerClassification.Projectives (C := C))]
  [∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive] in
/-- The obstruction for the integer shift generated by S. -/
theorem proposition_4_2_of_faithful_cycles
    [(StableCocycles.acyclicStableCycles (C := C)).Faithful]
    (p : HellerExactness.Parameter S) (u : TriangleCenterUnit F)
    (hp : HellerObstruction.ParameterTriangulated S p)
    (hpu : HellerObstruction.ParameterTriangulated S (p.twist u))
    (T : Triangle (projectiveStableCategory C)) (hT : T ∈ distTriang (projectiveStableCategory C))
    (hU : u.iso.hom.app T.obj₁ - 𝟙 _ = 0)
    (hY : u.iso.hom.app T.obj₂ - 𝟙 _ = 0) :
    IsLightningFlash T T (u.iso.hom.app T.obj₃ - 𝟙 _) := by
  let := HellerClassification.projectiveHasShift S
  let : ∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive :=
    fun n => AutoequivalenceShift.shift_additive (HellerClassification.projectiveEquivalence S) n
  let : CategoryTheory.Pretriangulated (HellerClassification.Projectives (C := C)) :=
    HellerClassification.constructedPretriangulated S p
  exact proposition_4_2_generic_of_faithful_cycles S
    (HellerClassification.projectiveShiftOneIso S) p u hp hpu T hT hU hY

end PretriangulatedV2.StableCategory.HellerObstructionFinal
