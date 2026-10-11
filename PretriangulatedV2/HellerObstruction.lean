import PretriangulatedV2.PeriodicCone
import PretriangulatedV2.HellerClassification
import PretriangulatedV2.GoodFillIns

/-! Components of the genuine Heller obstruction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2.StableCategory.HellerObstruction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]
variable (S : C ≌ C) [S.functor.Additive]

abbrev Q := projectiveStableQuotient (C := C)
abbrev F := Cosyzygy.functor (C := C)

/-- A parameter is triangulated when its actual constructed projective
pretriangulation satisfies mathlib's octahedron axiom. -/
def ParameterTriangulated (p : HellerExactness.Parameter S) : Prop :=
  let := HellerClassification.projectiveHasShift S
  let : ∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive :=
    fun n => AutoequivalenceShift.shift_additive (HellerClassification.projectiveEquivalence S) n
  let := HellerClassification.constructedPretriangulated S p
  IsTriangulated (HellerClassification.Projectives (C := C))

/-- Actual triangulated Heller parameters have the proved good-fill-in
property. The conclusion is obtained from the octahedron theorem, not supplied
as part of the parameter data. -/
theorem hasGoodFillIns (p : HellerExactness.Parameter S) (hp : ParameterTriangulated S p) :
    let := HellerClassification.projectiveHasShift S
    let : ∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive :=
      fun n => AutoequivalenceShift.shift_additive (HellerClassification.projectiveEquivalence S) n
    let := HellerClassification.constructedPretriangulated S p
    letI : PreservesBinaryBiproducts
        (shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ)) :=
      preservesBinaryBiproducts_of_preservesBiproducts _
    HasGoodFillIns (HellerClassification.Projectives (C := C)) := by
  let := HellerClassification.projectiveHasShift S
  let : ∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive :=
    fun n => AutoequivalenceShift.shift_additive (HellerClassification.projectiveEquivalence S) n
  let := HellerClassification.constructedPretriangulated S p
  let : IsTriangulated (HellerClassification.Projectives (C := C)) := hp
  let : PreservesBinaryBiproducts
      (shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  change HasGoodFillIns (HellerClassification.Projectives (C := C))
  intro T T' hT hT' m
  exact GoodFillIns.exists_good_fill_in (C := HellerClassification.Projectives (C := C))
    m hT hT'

/-- At a zero component of u−1, δ-exactness is also twisted-δ-exactness.
The passage from an arbitrary exact-row witness to canonical cycles is proved
in `PeriodicExactnessBridge`. -/
theorem twisted_exact_of_unit_component (p : HellerExactness.Parameter S)
    (u : TriangleCenterUnit F) (P : PeriodicComplexes.SComplex S)
    (hu : u.iso.hom.app (Q.obj (P.complex.cycles 0)) = 𝟙 _)
    (hP : HellerExactness.DeltaExactTruncation S p (P.complex.d 0 1)
      (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv)) :
    HellerExactness.DeltaExactTruncation S (p.twist u) (P.complex.d 0 1)
      (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv) := by
  apply ComplexInjectiveExtensions.deltaExactTruncation_of_periodic
  obtain ⟨h₁, h₂, h₃, hE⟩ :=
    PeriodicExactnessBridge.periodic_of_deltaExactTruncation S p P hP
  refine ⟨h₁, h₂, h₃, ?_⟩
  rw [HellerExactness.deltaExact_iff_stableComparison] at hE ⊢
  erw [HellerParameter.twist_delta_hom_app, hu, (stableFunctor S.functor).map_id,
    Category.id_comp]
  exact hE

/-- The cone part of Proposition 4.2: actual δ-exact and twisted-δ-exact
periodic mapping cones force u−1 to be the concrete stable lightning flash.
Periodicity and the transported homotopy are actual constructed maps. -/
theorem cone_component_isLightningFlash
    (p : HellerExactness.Parameter S) (u : TriangleCenterUnit F)
    (P R : PeriodicComplexes.SComplex S)
    (f g : P.complex ⟶ R.complex)
    (hf : PeriodicCone.IsPeriodic S P R f) (hg : PeriodicCone.IsPeriodic S P R g)
    (hPac : P.complex.Acyclic) (H : Homotopy f g)
    (hCf : HellerExactness.DeltaExactTruncation S p
      ((CochainComplex.mappingCone f).d 0 1)
      ((CochainComplex.mappingCone f).d 1 2)
      ((CochainComplex.mappingCone f).d 2 3 ≫ (PeriodicCone.period S P R f 3).inv))
    (hCg : HellerExactness.DeltaExactTruncation S (p.twist u)
      ((CochainComplex.mappingCone g).d 0 1)
      ((CochainComplex.mappingCone g).d 1 2)
      ((CochainComplex.mappingCone g).d 2 3 ≫ (PeriodicCone.period S P R g 3).inv)) :
    let : Injective (P.complex.X 0) :=
      (FrobeniusAbelian.projective_iff_injective _).mp (P.projective 0)
    IsLightningFlash (MappingConeCycles.triangle f hPac) (MappingConeCycles.triangle f hPac)
      (u.iso.hom.app (Q.obj ((CochainComplex.mappingCone f).cycles 0)) - 𝟙 _) := by
  let : Injective (P.complex.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (P.projective 0)
  let H' := PeriodicCone.periodicHomotopy S P R f hf hg H
  have hc := PeriodicExactnessBridge.lemma_4_1 S p u
    (PeriodicCone.complex S P R f hf) (PeriodicCone.complex S P R g hg)
    hCf hCg (ConeHomotopy.thetaOfHomotopy f g H)
  rw [PeriodicCone.theta_twist] at hc
  change (MappingConeCycles.thetaCyclesIso f H').hom =
      u.iso.hom.app (Q.obj ((CochainComplex.mappingCone f).cycles 0)) ≫
        (MappingConeCycles.thetaCyclesIso f H).hom at hc
  have he : (MappingConeCycles.thetaCyclesIso f H').hom ≫
      (MappingConeCycles.thetaCyclesIso f H).inv =
      u.iso.hom.app (Q.obj ((CochainComplex.mappingCone f).cycles 0)) := by
    rw [hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hl := MappingConeCycles.isLightningFlash_thetaCycles_discrepancy f hPac H H'
  rw [he] at hl
  exact hl

/-- Naturality transports the concrete cone obstruction to any isomorphic
stable triangle. -/
theorem component_isLightningFlash_of_triangleIso
    (u : TriangleCenterUnit F) {T T' : Triangle (projectiveStableCategory C)}
    (e : T ≅ T')
    (h : IsLightningFlash T' T' (u.iso.hom.app T'.obj₃ - 𝟙 _)) :
    IsLightningFlash T T (u.iso.hom.app T.obj₃ - 𝟙 _) := by
  have hl := h.conjugate e.symm
  have hn := u.iso.hom.naturality e.hom.hom₃
  dsimp only [Functor.id_map] at hn
  have he : e.hom.hom₃ ≫ (u.iso.hom.app T'.obj₃ - 𝟙 _) ≫ e.inv.hom₃ =
      u.iso.hom.app T.obj₃ - 𝟙 _ := by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp]
    rw [← Category.assoc, hn]
    simp
  simpa only [Iso.symm_inv, Iso.symm_hom, he] using hl

end PretriangulatedV2.StableCategory.HellerObstruction
