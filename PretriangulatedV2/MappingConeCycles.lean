import PretriangulatedV2.AcyclicShiftComparison
import PretriangulatedV2.ComplexInjectiveExtensions
import PretriangulatedV2.ConeDiscrepancy
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-! The actual mapping-cone triangle on zero cycles. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex CategoryTheory.Pretriangulated

namespace PretriangulatedV2.StableCategory.MappingConeCycles

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
variable {P R : CochainComplex C ℤ} (f : P ⟶ R)

abbrev K := CochainComplex.mappingCone f

/-- The ambient middle object in the zero-cycle short exact sequence. -/
abbrev middle (_f : P ⟶ R) := R.cycles 0 ⊞ P.X 0

/-- Its first arrow retains the actual embedding into degree zero. -/
def first : P.cycles 0 ⟶ middle f :=
  biprod.lift (cyclesMap f 0) (P.iCycles 0)

/-- The signed degree-zero map to the genuine mapping cone. -/
def raw : middle f ⟶ (K f).X 0 :=
  biprod.snd ≫ P.d 0 1 ≫ (CochainComplex.mappingCone.inl f).v 1 0 (by norm_num) +
    (biprod.fst ≫ R.iCycles 0 - biprod.snd ≫ f.f 0) ≫
      (CochainComplex.mappingCone.inr f).f 0

@[reassoc]
lemma raw_fst : raw f ≫ (CochainComplex.mappingCone.fst f).1.v 0 1 rfl =
    biprod.snd ≫ P.d 0 1 := by
  simp [raw, Preadditive.add_comp, Preadditive.sub_comp,
    CochainComplex.mappingCone.inl_v_fst_v, CochainComplex.mappingCone.inr_f_fst_v]

@[reassoc]
lemma raw_snd : raw f ≫ (CochainComplex.mappingCone.snd f).v 0 0 rfl =
    biprod.fst ≫ R.iCycles 0 - biprod.snd ≫ f.f 0 := by
  simp [raw, Preadditive.add_comp, Preadditive.sub_comp,
    CochainComplex.mappingCone.inl_v_snd_v, CochainComplex.mappingCone.inr_f_snd_v]

lemma raw_d : raw f ≫ (K f).d 0 1 = 0 := by
  apply CochainComplex.mappingCone.ext_to f 1 2 rfl
  · rw [Category.assoc, CochainComplex.mappingCone.d_fst_v f 0 1 2 rfl rfl,
      Preadditive.comp_neg, ← Category.assoc, raw_fst]
    simp
  · rw [Category.assoc, CochainComplex.mappingCone.d_snd_v f 0 1 rfl,
      Preadditive.comp_add, ← Category.assoc, raw_fst, ← Category.assoc, raw_snd,
      Preadditive.sub_comp]
    simp only [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
    rw [← f.comm 0 1]
    simp

/-- The actual second arrow into the kernel of the cone differential. -/
def second : middle f ⟶ (K f).cycles 0 :=
  (K f).liftCycles (raw f) 1 (by
    apply (ComplexShape.up ℤ).next_eq'
    rfl) (raw_d f)

@[reassoc (attr := simp)]
lemma second_i : second f ≫ (K f).iCycles 0 = raw f := by
  apply HomologicalComplex.liftCycles_i

lemma first_second : first f ≫ second f = 0 := by
  apply (cancel_mono ((K f).iCycles 0)).mp
  rw [Category.assoc, second_i, zero_comp]
  apply CochainComplex.mappingCone.ext_to f 0 1 rfl
  · simp [first, raw_fst, Category.assoc]
  · rw [Category.assoc, raw_snd, Preadditive.comp_sub]
    simp [first, cyclesMap_i]

/-- The ambient short complex whose stable image is the cone triangle. -/
def sequence : ShortComplex C := ShortComplex.mk (first f) (second f) (first_second f)

instance first_mono : Mono (first f) := by
  dsimp only [first]
  infer_instance

/-- The first arrow is precisely the kernel of the actual cone-cycle map. -/
def firstIsKernel : IsLimit (KernelFork.ofι (first f) (first_second f)) := by
  apply KernelFork.IsLimit.ofι'
  intro A y hy
  have hr : y ≫ raw f = 0 := by
    rw [← second_i, ← Category.assoc, hy, zero_comp]
  have hp : (y ≫ biprod.snd) ≫ P.d 0 1 = 0 := by
    simpa only [Category.assoc, raw_fst, zero_comp] using
      congrArg (fun z => z ≫ (CochainComplex.mappingCone.fst f).1.v 0 1 rfl) hr
  let a := P.liftCycles (y ≫ biprod.snd) 1 (by
    apply (ComplexShape.up ℤ).next_eq'
    rfl) hp
  have ha : a ≫ P.iCycles 0 = y ≫ biprod.snd := by
    apply HomologicalComplex.liftCycles_i
  refine ⟨a, ?_⟩
  apply biprod.hom_ext
  · apply (cancel_mono (R.iCycles 0)).mp
    have hq : y ≫ biprod.fst ≫ R.iCycles 0 - y ≫ biprod.snd ≫ f.f 0 = 0 := by
      simpa only [Category.assoc, raw_snd, Preadditive.comp_sub, zero_comp] using
        congrArg (fun z => z ≫ (CochainComplex.mappingCone.snd f).v 0 0 rfl) hr
    simp only [first, Category.assoc, biprod.lift_fst, cyclesMap_i]
    rw [← Category.assoc, ha]
    simpa only [Category.assoc] using (sub_eq_zero.mp hq).symm
  · simpa only [first, Category.assoc, biprod.lift_snd] using ha

/-- Acyclicity in source degree one makes the cone-cycle map epi.  The proof
lifts actual morphisms after an epi refinement, so no projective generator is
assumed. -/
theorem second_epi (hP : P.ExactAt 1) : Epi (second f) := by
  let : Epi (P.toCycles 0 1) :=
    (ComplexInjectiveExtensions.cycleSequence_shortExact P 0 (by simpa using hP)).epi_g
  rw [epi_iff_surjective_up_to_refinements]
  intro A z
  let x := z ≫ (K f).iCycles 0
  have hx : x ≫ (K f).d 0 1 = 0 := by
    simp [x]
  let a := x ≫ (CochainComplex.mappingCone.fst f).1.v 0 1 rfl
  have ha : a ≫ P.d 1 2 = 0 := by
    have hd := congrArg
      (fun t => t ≫ (CochainComplex.mappingCone.fst f).1.v 1 2 rfl) hx
    rw [Category.assoc, CochainComplex.mappingCone.d_fst_v f 0 1 2 rfl rfl,
      Preadditive.comp_neg, zero_comp] at hd
    have hd' : -(a ≫ P.d 1 2) = 0 := by
      simpa only [a, Category.assoc, Preadditive.neg_comp] using hd
    exact neg_eq_zero.mp hd'
  let ac := P.liftCycles a 2 (by
    apply (ComplexShape.up ℤ).next_eq'
    rfl) ha
  obtain ⟨A', π, hπ, p, hp⟩ := surjective_up_to_refinements_of_epi (P.toCycles 0 1) ac
  have hp' : π ≫ a = p ≫ P.d 0 1 := by
    simpa only [ac, Category.assoc, liftCycles_i, toCycles_i] using
      congrArg (fun t => t ≫ P.iCycles 1) hp
  let b := π ≫ x ≫ (CochainComplex.mappingCone.snd f).v 0 0 rfl + p ≫ f.f 0
  have hb : b ≫ R.d 0 1 = 0 := by
    have hd := congrArg
      (fun t => t ≫ (CochainComplex.mappingCone.snd f).v 1 1 rfl) hx
    rw [Category.assoc, CochainComplex.mappingCone.d_snd_v f 0 1 rfl,
      Preadditive.comp_add, zero_comp] at hd
    have hd' : a ≫ f.f 1 + (x ≫ (CochainComplex.mappingCone.snd f).v 0 0 rfl) ≫
        R.d 0 1 = 0 := by
      simpa only [a, Category.assoc] using hd
    dsimp only [b]
    simp only [Preadditive.add_comp, Category.assoc]
    rw [f.comm 0 1, ← Category.assoc p, ← hp']
    simpa only [Preadditive.comp_add, Category.assoc, add_comm, comp_zero] using
      congrArg (fun t => π ≫ t) hd'
  let bc := R.liftCycles b 1 (by
    apply (ComplexShape.up ℤ).next_eq'
    rfl) hb
  refine ⟨A', π, hπ, biprod.lift bc p, ?_⟩
  apply (cancel_mono ((K f).iCycles 0)).mp
  simp only [Category.assoc, second_i]
  apply CochainComplex.mappingCone.ext_to f 0 1 rfl
  · simp only [Category.assoc, raw_fst, biprod.lift_snd_assoc]
    simpa only [a, x, Category.assoc] using hp'
  · simp only [Category.assoc, raw_snd, Preadditive.comp_sub,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc]
    rw [HomologicalComplex.liftCycles_i]
    simp only [b, x, Category.assoc]
    abel

/-- The actual short exact row producing the cone triangle on zero cycles. -/
theorem sequence_shortExact (hP : P.ExactAt 1) : (sequence f).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (firstIsKernel f)
  mono_f := first_mono f
  epi_g := second_epi f hP

@[reassoc (attr := simp)]
lemma inl_second : (biprod.inl : R.cycles 0 ⟶ middle f) ≫ second f =
    cyclesMap (CochainComplex.mappingCone.inr f) 0 := by
  apply (cancel_mono ((K f).iCycles 0)).mp
  simp [second_i, raw, Preadditive.comp_add, Preadditive.comp_sub,
    cyclesMap_i]

/-- The cone projection on cycles, before the negative sign in the actual
standard triangle. -/
def third : (K f).cycles 0 ⟶ P.cycles 1 :=
  P.liftCycles ((K f).iCycles 0 ≫ (CochainComplex.mappingCone.fst f).1.v 0 1 rfl)
    2 (by apply (ComplexShape.up ℤ).next_eq'; rfl) (by
      have hd := congrArg
        (fun t => t ≫ (CochainComplex.mappingCone.fst f).1.v 1 2 rfl)
        ((K f).iCycles_d 0 1)
      rw [Category.assoc, CochainComplex.mappingCone.d_fst_v f 0 1 2 rfl rfl,
        Preadditive.comp_neg, zero_comp] at hd
      have hd' : -(((K f).iCycles 0 ≫
          (CochainComplex.mappingCone.fst f).1.v 0 1 rfl) ≫ P.d 1 2) = 0 := by
        simpa only [Category.assoc, Preadditive.neg_comp] using hd
      exact neg_eq_zero.mp hd')

@[reassoc (attr := simp)]
lemma third_i : third f ≫ P.iCycles 1 =
    (K f).iCycles 0 ≫ (CochainComplex.mappingCone.fst f).1.v 0 1 rfl := by
  apply HomologicalComplex.liftCycles_i

@[reassoc (attr := simp)]
lemma second_third : second f ≫ third f = biprod.snd ≫ P.toCycles 0 1 := by
  apply (cancel_mono (P.iCycles 1)).mp
  simp [Category.assoc, third_i, raw_fst, toCycles_i]

/-- The actual commutative comparison with the source's injective cycle row. -/
def sequenceMap : sequence f ⟶ ComplexInjectiveExtensions.cycleSequence P 0 where
  τ₁ := 𝟙 _
  τ₂ := biprod.snd
  τ₃ := third f
  comm₁₂ := by simp [sequence, first, ComplexInjectiveExtensions.cycleSequence]
  comm₂₃ := by simp [sequence, ComplexInjectiveExtensions.cycleSequence]

/-- Exact normalization of mathlib's signed standard-triangle projection. -/
lemma triangle_third_cycles :
    cyclesMap (CochainComplex.mappingCone.triangle f).mor₃ 0 ≫
        (AcyclicShiftComparison.cyclesShiftOneIso P).hom = -third f := by
  apply (cancel_mono (P.iCycles 1)).mp
  rw [Category.assoc, AcyclicShiftComparison.cyclesShiftOneIso_hom_i,
    Preadditive.neg_comp, third_i]
  erw [cyclesMap_i]
  have he : (CochainComplex.mappingCone.triangle f).mor₃.f 0 =
      -(CochainComplex.mappingCone.fst f).1.v 0 1 rfl := by
    apply CochainComplex.mappingCone.ext_from f 1 0 rfl
    · simp only [Preadditive.comp_neg, CochainComplex.mappingCone.inl_v_triangle_mor₃_f,
        CochainComplex.mappingCone.inl_v_fst_v]
      rfl
    · simp
  rw [he, Preadditive.comp_neg]
  rfl

variable [FrobeniusAbelian C]

/-- The connecting map of the genuine cone-cycle row is the unsigned cone
projection followed by the actual cosyzygy comparison. -/
lemma stable_connecting (hP : P.ExactAt 1) :
    FrobeniusTriangles.stableConnecting (sequence_shortExact f hP) =
      (projectiveStableQuotient (C := C)).map (third f) ≫
        (projectiveStableQuotient (C := C)).map
          (FrobeniusTriangles.connecting
            (ComplexInjectiveExtensions.cycleSequence_shortExact P 0
              (by simpa using hP))) := by
  have hn := FrobeniusTriangles.connecting_naturality
    (sequence_shortExact f hP)
    (ComplexInjectiveExtensions.cycleSequence_shortExact P 0 (by simpa using hP))
    (sequenceMap f)
  dsimp only [sequenceMap] at hn
  erw [(projectiveStableQuotient (C := C)).map_id,
    (Cosyzygy.functor (C := C)).map_id, Category.comp_id] at hn
  simpa only [sequenceMap,
    Category.comp_id,
    FrobeniusTriangles.stableConnecting, zero_add] using hn

omit [FrobeniusAbelian C] in
/-- The degreewise split cone short exact sequence is a genuine short exact
sequence of cochain complexes. -/
theorem cone_shortExact :
    (CochainComplex.mappingCone.triangleRotateShortComplex f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (CochainComplex.mappingCone.triangleRotateShortComplexSplitting f n).shortExact)

omit [FrobeniusAbelian C] in
/-- Cones of maps of acyclic complexes are acyclic, with no equivalence
between stable and homotopy categories assumed. -/
theorem cone_acyclic (hP : P.Acyclic) (hR : R.Acyclic) : (K f).Acyclic := by
  apply (cone_shortExact f).acyclic_X₂
  · exact hR
  · intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hP (1 + i)).isZero_homology.of_iso
      ((CochainComplex.ShiftSequence.shiftIso C 1 i (1 + i) rfl).app P)

omit [FrobeniusAbelian C] in
/-- The genuine cone terms remain projective. -/
theorem cone_projective (hP : ∀ n, Projective (P.X n))
    (hR : ∀ n, Projective (R.X n)) (n : ℤ) : Projective ((K f).X n) := by
  let : Projective (P.X (n + 1)) := hP _
  let : Projective (R.X n) := hR _
  exact Projective.of_iso (homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
    inferInstance

/-- The sign required by the actual standard cone triangle. -/
def signedShiftOneIso (P : CochainComplex C ℤ) (hP : P.Acyclic)
    [Injective (P.X 0)] :
    (projectiveStableQuotient (C := C)).obj ((P⟦(1 : ℤ)⟧).cycles 0) ≅
      ((projectiveStableQuotient (C := C)).obj (P.cycles 0))⟦(1 : ℤ)⟧ :=
  (-1 : ℤˣ) • (AcyclicShiftComparison.stableShiftOneIso P hP ≪≫
    (cosyzygyIsoShift (C := C)).app _)

@[simp]
lemma signedShiftOneIso_hom (P : CochainComplex C ℤ) (hP : P.Acyclic)
    [Injective (P.X 0)] :
    (signedShiftOneIso P hP).hom =
      -((AcyclicShiftComparison.stableShiftOneIso P hP).hom ≫
        (cosyzygyIsoShift (C := C)).hom.app _) := by
  simp [signedShiftOneIso]

/-- The actual standard cone triangle after applying zero cycles and the
signed shift comparison. -/
def triangle (hP : P.Acyclic) [Injective (P.X 0)] :
    CategoryTheory.Pretriangulated.Triangle (projectiveStableCategory C) :=
  CategoryTheory.Pretriangulated.Triangle.mk
    ((projectiveStableQuotient (C := C)).map (cyclesMap f 0))
    ((projectiveStableQuotient (C := C)).map
      (cyclesMap (CochainComplex.mappingCone.inr f) 0))
    ((projectiveStableQuotient (C := C)).map
        (cyclesMap (CochainComplex.mappingCone.triangle f).mor₃ 0) ≫
      (signedShiftOneIso P hP).hom)

lemma triangle_third (hP : P.Acyclic) [Injective (P.X 0)] :
    (triangle f hP).mor₃ =
      FrobeniusTriangles.stableConnecting (sequence_shortExact f (hP 1)) ≫
        (cosyzygyIsoShift (C := C)).hom.app _ := by
  let : Injective (ComplexInjectiveExtensions.cycleSequence P 0).X₂ :=
    inferInstanceAs (Injective (P.X 0))
  have hn := congrArg (fun t => (projectiveStableQuotient (C := C)).map t)
    (triangle_third_cycles f)
  simp only [Functor.map_comp, Functor.map_neg] at hn
  dsimp only [triangle, CategoryTheory.Pretriangulated.Triangle.mk]
  rw [signedShiftOneIso_hom]
  dsimp only [AcyclicShiftComparison.stableShiftOneIso, Iso.trans_hom,
    Functor.mapIso_hom]
  rw [Preadditive.comp_neg]
  simp only [← Category.assoc]
  rw [hn, Preadditive.neg_comp, Preadditive.neg_comp, neg_neg,
    InjectiveComparison.connectingIso_hom]
  rw [stable_connecting f (hP 1)]
  rfl

/-- This comparison is a triangle isomorphism, with the injective middle
summand removed in the actual stable quotient. -/
def triangleIso (hP : P.Acyclic) [Injective (P.X 0)] :
    triangle f hP ≅ shortExactTriangle (sequence_shortExact f (hP 1)) := by
  let E := FrobeniusTriangles.stableBiprodInjectiveIso (R.cycles 0) (P.X 0)
  refine CategoryTheory.Pretriangulated.Triangle.isoMk _ _
    (Iso.refl _) E.symm (Iso.refl _) ?_ ?_ ?_
  · change (projectiveStableQuotient (C := C)).map (cyclesMap f 0) ≫
        (projectiveStableQuotient (C := C)).map biprod.inl =
      𝟙 _ ≫ (projectiveStableQuotient (C := C)).map (first f)
    apply (cancel_mono E.hom).mp
    simp only [Category.assoc, Category.id_comp]
    change _ = (projectiveStableQuotient (C := C)).map (first f) ≫
      (projectiveStableQuotient (C := C)).map biprod.fst
    simp [E, FrobeniusTriangles.stableBiprodInjectiveIso, ← Functor.map_comp, first]
  · change (projectiveStableQuotient (C := C)).map
        (cyclesMap (CochainComplex.mappingCone.inr f) 0) ≫ 𝟙 _ =
      (projectiveStableQuotient (C := C)).map biprod.inl ≫
        (projectiveStableQuotient (C := C)).map (second f)
    simp [← Functor.map_comp]
  · dsimp only [Iso.refl_hom]
    rw [(shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map_id,
      Category.comp_id, Category.id_comp]
    exact triangle_third f hP

/-- The zero-cycle image of the genuine mapping-cone triangle is
canonically distinguished. -/
theorem triangle_distinguished (hP : P.Acyclic) [Injective (P.X 0)] :
    triangle f hP ∈ distTriang
      (projectiveStableCategory C) :=
  FrobeniusTriangles.isomorphic_distinguished (cosyzygyIsoShift (C := C))
    (shortExactTriangle_distinguished (sequence_shortExact f (hP 1)))
    (triangleIso f hP)

/-- The genuine zero-cycle functor followed by the actual projective stable
quotient. Its restriction to projective complexes descends through homotopies
in `StableCocycles`. -/
abbrev cyclesToStable : CochainComplex C ℤ ⥤ projectiveStableCategory C :=
  HomologicalComplex.cyclesFunctor C (ComplexShape.up ℤ) 0 ⋙
    projectiveStableQuotient (C := C)

/-- The actual cone isomorphism induced by a cochain homotopy, after taking
zero cycles and the stable quotient. -/
def thetaCyclesIso {g : P ⟶ R} (H : Homotopy f g) :
    (projectiveStableQuotient (C := C)).obj ((K f).cycles 0) ≅
      (projectiveStableQuotient (C := C)).obj
        ((CochainComplex.mappingCone g).cycles 0) :=
  (cyclesToStable (C := C)).mapIso (ConeHomotopy.thetaIso f g H)

/-- Proposition 2.3 on actual stable zero cycles. No triangulated-equivalence
assumption is used: the proven cochain equality supplies the lightning factor. -/
theorem isLightningFlash_thetaCycles_discrepancy {g : P ⟶ R}
    (hP : P.Acyclic) [Injective (P.X 0)] (H H' : Homotopy f g) :
    IsLightningFlash (triangle f hP) (triangle f hP)
      ((thetaCyclesIso f H').hom ≫ (thetaCyclesIso f H).inv - 𝟙 _) := by
  have hc := congrArg (fun t => (cyclesToStable (C := C)).map t)
    (ConeHomotopy.thetaOfHomotopy_comp_symm_sub_id f g H H')
  simp only [Functor.map_sub, Functor.map_comp] at hc
  erw [(cyclesToStable (C := C)).map_id] at hc
  dsimp only [CochainComplex.mappingCone.triangle_obj₃] at hc
  refine ⟨(signedShiftOneIso P hP).inv ≫
      (cyclesToStable (C := C)).map (-ConeHomotopy.homotopyDifferenceMap f g H H'), ?_⟩
  dsimp only [thetaCyclesIso, Functor.mapIso_hom, Functor.mapIso_inv,
    ConeHomotopy.thetaIso_hom, ConeHomotopy.thetaIso_inv]
  erw [hc]
  dsimp only [triangle, CategoryTheory.Pretriangulated.Triangle.mk]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end PretriangulatedV2.StableCategory.MappingConeCycles
