import PretriangulatedV2.ComplexInjectiveExtensions
import PretriangulatedV2.StableCocycles
import PretriangulatedV2.FrobeniusTriangulation
import PretriangulatedV2.GeneratorCommShift
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
The actual comparison between shifted cocycles and the canonical stable shift.
The minus sign in the cochain differential is retained by mathlib's actual
short-complex shift isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PretriangulatedV2.StableCategory.AcyclicShiftComparison

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- Actual shifted cocycles are the next cocycles, including the signed
cochain differential in the defining short-complex isomorphism. -/
def cyclesShiftOneIso (P : CochainComplex C ℤ) : (P⟦(1 : ℤ)⟧).cycles 0 ≅ P.cycles 1 :=
  (ShortComplex.cyclesFunctor C).mapIso
    ((CochainComplex.shiftShortComplexFunctorIso C 1 0 1 (by norm_num)).app P)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem cyclesShiftOneIso_naturality {P R : CochainComplex C ℤ} (f : P ⟶ R) :
    cyclesMap (f⟦(1 : ℤ)⟧') 0 ≫ (cyclesShiftOneIso R).hom =
      (cyclesShiftOneIso P).hom ≫ cyclesMap f 1 := by
  change ShortComplex.cyclesMap _ ≫ ShortComplex.cyclesMap _ =
    ShortComplex.cyclesMap _ ≫ ShortComplex.cyclesMap _
  rw [← ShortComplex.cyclesMap_comp, ← ShortComplex.cyclesMap_comp]
  congr 1
  exact ((CochainComplex.shiftShortComplexFunctorIso C 1 0 1 (by norm_num)).hom.naturality f)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[reassoc (attr := simp)]
theorem cyclesShiftOneIso_hom_i (P : CochainComplex C ℤ) :
    (cyclesShiftOneIso P).hom ≫ P.iCycles 1 = (P⟦(1 : ℤ)⟧).iCycles 0 := by
  simp [cyclesShiftOneIso, ShortComplex.cyclesFunctor, HomologicalComplex.iCycles,
    CochainComplex.shiftShortComplexFunctorIso, CochainComplex.shiftShortComplexFunctor',
    CochainComplex.shiftEval, HomologicalComplex.XIsoOfEq, ShortComplex.cyclesMap_i]

/-- The genuine map of consecutive-cycle short exact rows. -/
def cycleSequenceMap {P R : CochainComplex C ℤ} (f : P ⟶ R) (n : ℤ) :
    ComplexInjectiveExtensions.cycleSequence P n ⟶
      ComplexInjectiveExtensions.cycleSequence R n where
  τ₁ := cyclesMap f n
  τ₂ := f.f n
  τ₃ := cyclesMap f (n + 1)
  comm₁₂ := cyclesMap_i f n
  comm₂₃ := by
    apply (cancel_mono (R.iCycles (n + 1))).mp
    simp only [ComplexInjectiveExtensions.cycleSequence, Category.assoc,
      cyclesMap_i, toCycles_i_assoc, toCycles_i]
    exact f.comm n (n + 1)

/-- Actual acyclicity and an actual injective degree-zero term give the
comparison with the chosen cosyzygy. -/
def stableShiftOneIso (P : CochainComplex C ℤ) (hP : P.Acyclic)
    [Injective (P.X 0)] :
    (projectiveStableQuotient (C := C)).obj ((P⟦(1 : ℤ)⟧).cycles 0) ≅
      (Cosyzygy.functor (C := C)).obj
        ((projectiveStableQuotient (C := C)).obj (P.cycles 0)) := by
  let : Injective (ComplexInjectiveExtensions.cycleSequence P 0).X₂ :=
    inferInstanceAs (Injective (P.X 0))
  exact (projectiveStableQuotient (C := C)).mapIso (cyclesShiftOneIso P) ≪≫
    InjectiveComparison.connectingIso
      (ComplexInjectiveExtensions.cycleSequence_shortExact P 0 (by simpa using hP 1))

theorem stableShiftOneIso_naturality {P R : CochainComplex C ℤ}
    (hP : P.Acyclic) (hR : R.Acyclic) [Injective (P.X 0)] [Injective (R.X 0)]
    (f : P ⟶ R) :
    (projectiveStableQuotient (C := C)).map (cyclesMap (f⟦(1 : ℤ)⟧') 0) ≫
        (stableShiftOneIso R hR).hom =
      (stableShiftOneIso P hP).hom ≫
        (Cosyzygy.functor (C := C)).map
          ((projectiveStableQuotient (C := C)).map (cyclesMap f 0)) := by
  let : Injective (ComplexInjectiveExtensions.cycleSequence P 0).X₂ :=
    inferInstanceAs (Injective (P.X 0))
  let : Injective (ComplexInjectiveExtensions.cycleSequence R 0).X₂ :=
    inferInstanceAs (Injective (R.X 0))
  dsimp only [stableShiftOneIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, cyclesShiftOneIso_naturality,
    Functor.map_comp, Category.assoc]
  rw [InjectiveComparison.connectingIso_hom, InjectiveComparison.connectingIso_hom]
  rw [Category.assoc]
  congr 1
  exact (FrobeniusTriangles.connecting_naturality
    (ComplexInjectiveExtensions.cycleSequence_shortExact P 0 (by simpa using hP 1))
    (ComplexInjectiveExtensions.cycleSequence_shortExact R 0 (by simpa using hR 1))
    (cycleSequenceMap f 0)).symm

/-- The canonical stable shift comparison for an actual acyclic complex
of projective objects. -/
def canonicalShiftOneIso (P : StableCocycles.AcyclicProjectiveComplex C) :
    (projectiveStableQuotient (C := C)).obj ((P.obj⟦(1 : ℤ)⟧).cycles 0) ≅
      ((projectiveStableQuotient (C := C)).obj (P.obj.cycles 0))⟦(1 : ℤ)⟧ := by
  letI : Injective (P.obj.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (P.property.1 0)
  exact stableShiftOneIso P.obj P.property.2 ≪≫
    (cosyzygyIsoShift (C := C)).app _

theorem canonicalShiftOneIso_naturality
    {P R : StableCocycles.AcyclicProjectiveComplex C} (f : P ⟶ R) :
    (projectiveStableQuotient (C := C)).map (cyclesMap (f.hom⟦(1 : ℤ)⟧') 0) ≫
        (canonicalShiftOneIso R).hom =
      (canonicalShiftOneIso P).hom ≫
        ((projectiveStableQuotient (C := C)).map (cyclesMap f.hom 0))⟦(1 : ℤ)⟧' := by
  let : Injective (P.obj.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (P.property.1 0)
  let : Injective (R.obj.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (R.property.1 0)
  dsimp only [canonicalShiftOneIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, stableShiftOneIso_naturality P.property.2 R.property.2 f.hom,
    Category.assoc]
  rw [(cosyzygyIsoShift (C := C)).hom.naturality]
  simp only [Category.assoc]

/-- The actual projective acyclic complexes are closed under the signed
cochain shifts in every integer degree. -/
instance acyclicProjectiveComplexes_stableUnderShift :
    (StableCocycles.acyclicProjectiveComplexes (C := C)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        intro P hP
        refine ⟨?_, ?_⟩
        · intro i
          change Projective (P.X (i + n))
          exact hP.1 _
        · intro i
          rw [HomologicalComplex.exactAt_iff_isZero_homology]
          exact (hP.2 (n + i)).isZero_homology.of_iso
            ((CochainComplex.ShiftSequence.shiftIso C n i (n + i) rfl).app P) }

/-- Actual cochain homotopies remain homotopies under the restricted shift. -/
instance acyclicHomotopyRelation_shiftCompatible :
    (StableCocycles.acyclicHomotopyRelation (C := C)).IsCompatibleWithShift ℤ where
  condition n P R f g h := by
    obtain ⟨H⟩ := h
    let i := (StableCocycles.acyclicProjectiveComplexes (C := C)).ι.commShiftIso n
    have he (a : P ⟶ R) :
        i.hom.app P ≫ a.hom⟦n⟧' ≫ i.inv.app R = (a⟦n⟧').hom := by
      change i.hom.app P ≫ ((StableCocycles.acyclicProjectiveComplexes (C := C)).ι ⋙
        shiftFunctor _ n).map a ≫ i.inv.app R = _
      rw [← i.hom.naturality_assoc]
      simp
    exact ⟨by simpa only [Category.assoc, he f, he g] using
      ((H.shift n).compLeft (i.hom.app P)).compRight (i.inv.app R)⟩

/-- The genuine integer shift on `K_ac(P)` is induced by signed shifts of
actual cochain complexes and their actual homotopies. -/
@[instance_reducible]
def acyclicHomotopyHasShift :
    HasShift (StableCocycles.AcyclicProjectiveHomotopyCategory C) ℤ := inferInstance

/-- Natural comparison before passage to cochain homotopy. -/
def acyclicCyclesShiftOneIso :
    shiftFunctor (StableCocycles.AcyclicProjectiveComplex C) (1 : ℤ) ⋙
        StableCocycles.acyclicCyclesToStable ≅
      StableCocycles.acyclicCyclesToStable ⋙
        shiftFunctor (projectiveStableCategory C) (1 : ℤ) :=
  Functor.isoWhiskerRight
    ((StableCocycles.acyclicProjectiveComplexes (C := C)).ι.commShiftIso 1)
    (cyclesFunctor C (ComplexShape.up ℤ) 0 ⋙ projectiveStableQuotient) ≪≫
  NatIso.ofComponents canonicalShiftOneIso
    (fun f => canonicalShiftOneIso_naturality f)

/-- The actual zero-cycle functor on the cochain-homotopy quotient commutes
with the canonical stable suspension by a constructed natural isomorphism. -/
def acyclicStableCyclesShiftOneIso :
    shiftFunctor (StableCocycles.AcyclicProjectiveHomotopyCategory C) (1 : ℤ) ⋙
        StableCocycles.acyclicStableCycles ≅
      StableCocycles.acyclicStableCycles ⋙
        shiftFunctor (projectiveStableCategory C) (1 : ℤ) := by
  let q := CategoryTheory.Quotient.functor (StableCocycles.acyclicHomotopyRelation (C := C))
  let i : q ⋙ StableCocycles.acyclicStableCycles ≅ StableCocycles.acyclicCyclesToStable :=
    eqToIso (StableCocycles.acyclicStableCycles_spec (C := C))
  apply CategoryTheory.Quotient.natIsoLift (StableCocycles.acyclicHomotopyRelation (C := C))
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (q.commShiftIso (1 : ℤ)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ i ≪≫ acyclicCyclesShiftOneIso ≪≫
    Functor.isoWhiskerRight i.symm _ ≪≫ Functor.associator _ _ _

/-- The sign suitable for mathlib's actual cone triangle, whose third map
is minus the projection to the shifted source. -/
def triangleShiftOneIso :
    shiftFunctor (StableCocycles.AcyclicProjectiveHomotopyCategory C) (1 : ℤ) ⋙
        StableCocycles.acyclicStableCycles ≅
      StableCocycles.acyclicStableCycles ⋙
        shiftFunctor (projectiveStableCategory C) (1 : ℤ) :=
  (-1 : ℤˣ) • acyclicStableCyclesShiftOneIso

@[simp]
theorem triangleShiftOneIso_hom_app
    (P : StableCocycles.AcyclicProjectiveHomotopyCategory C) :
    triangleShiftOneIso.hom.app P = -acyclicStableCyclesShiftOneIso.hom.app P := by
  simp [triangleShiftOneIso]

/-- Full integer commutation, generated from the signed comparison used by
the actual cone triangles. Its target action is exactly the canonical stable
action already constructed from cosyzygy. -/
@[instance_reducible]
def acyclicStableCyclesCommShift :
    (StableCocycles.acyclicStableCycles (C := C)).CommShift ℤ :=
  GeneratorCommShift.commutation (Cosyzygy.equivalence (C := C))
    StableCocycles.acyclicStableCycles
    (triangleShiftOneIso ≪≫ Functor.isoWhiskerLeft StableCocycles.acyclicStableCycles
      (AutoequivalenceShift.shiftOneIso (Cosyzygy.equivalence (C := C))))

/-- The coherent extension retains the exact signed comparison at one. -/
theorem acyclicStableCyclesCommShift_one :
    letI := acyclicStableCyclesCommShift (C := C)
    (StableCocycles.acyclicStableCycles (C := C)).commShiftIso (1 : ℤ) =
      triangleShiftOneIso := by
  let := acyclicStableCyclesCommShift (C := C)
  apply Iso.ext
  apply (cancel_mono (Functor.isoWhiskerLeft StableCocycles.acyclicStableCycles
    (AutoequivalenceShift.shiftOneIso (Cosyzygy.equivalence (C := C)))).hom).mp
  exact congrArg Iso.hom
    (GeneratorCommShift.commutation_generator (Cosyzygy.equivalence (C := C))
      StableCocycles.acyclicStableCycles
      (triangleShiftOneIso ≪≫ Functor.isoWhiskerLeft StableCocycles.acyclicStableCycles
        (AutoequivalenceShift.shiftOneIso (Cosyzygy.equivalence (C := C)))))

end PretriangulatedV2.StableCategory.AcyclicShiftComparison
