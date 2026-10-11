import PretriangulatedV2.HellerObstruction

/-! Projective truncations of periodic complexes, maps, and mapping cones. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2.StableCategory.PeriodicConeTruncation

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]
variable (S : C ≌ C) [S.functor.Additive]

variable [HasShift (HellerClassification.Projectives (C := C)) ℤ]
  (e : shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ) ≅
    (HellerClassification.projectiveEquivalence S).functor)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C]
  [HasShift (HellerClassification.Projectives (C := C)) ℤ] in
@[simp]
lemma projective_add_hom {X Y : HellerClassification.Projectives (C := C)} (a b : X ⟶ Y) :
    (a + b).hom = a.hom + b.hom :=
  (HellerClassification.projectives (C := C)).ι.map_add

abbrev term (P : PeriodicComplexes.SComplex S) (n : ℤ) :
    HellerClassification.Projectives (C := C) := ⟨P.complex.X n, P.projective n⟩

/-- The three-term projective triangle of an S-periodic complex. -/
def truncation (P : PeriodicComplexes.SComplex S) :
    Triangle (HellerClassification.Projectives (C := C)) :=
  Triangle.mk (ObjectProperty.homMk (P.complex.d 0 1) : term S P 0 ⟶ term S P 1)
    (ObjectProperty.homMk (P.complex.d 1 2) : term S P 1 ⟶ term S P 2)
    ((ObjectProperty.homMk (P.complex.d 2 3 ≫ (P.period 3).inv) :
      term S P 2 ⟶ (HellerClassification.projectiveEquivalence S).functor.obj (term S P 0)) ≫
      e.inv.app _)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive] in
/-- The shift comparison identifies the last arrow with the closing differential. -/
@[reassoc (attr := simp)]
lemma truncation_third (P : PeriodicComplexes.SComplex S) :
    ((truncation S e P).mor₃ ≫ e.hom.app _).hom =
      P.complex.d 2 3 ≫ (P.period 3).inv := by
  dsimp only [truncation, Triangle.mk]
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

/-- Periodicity supplies the closing square of a triangle map. -/
def truncationMap {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (hf : PeriodicCone.IsPeriodic S P R f) :
    truncation S e P ⟶ truncation S e R where
  hom₁ := ObjectProperty.homMk (f.f 0)
  hom₂ := ObjectProperty.homMk (f.f 1)
  hom₃ := ObjectProperty.homMk (f.f 2)
  comm₁ := by
    apply ObjectProperty.hom_ext
    exact (f.comm 0 1).symm
  comm₂ := by
    apply ObjectProperty.hom_ext
    exact (f.comm 1 2).symm
  comm₃ := by
    apply (cancel_mono (e.hom.app _)).mp
    rw [Category.assoc,
      e.hom.naturality]
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      HellerClassification.projectiveEquivalence_map_hom,
      ObjectProperty.homMk_hom, Category.assoc]
    have hs := truncation_third S e P
    have hr := truncation_third S e R
    dsimp only [ObjectProperty.FullSubcategory.comp_hom] at hs hr
    erw [← Category.assoc, hs, hr]
    have hp := PeriodicCone.periodic_comm S P R f hf 3
    have hp' : (P.period 3).inv ≫ S.functor.map (f.f 0) = f.f 3 ≫ (R.period 3).inv := by
      apply (cancel_mono (R.period 3).hom).mp
      apply (cancel_epi (P.period 3).hom).mp
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
        Category.comp_id, Int.reduceSub] using hp
    erw [Category.assoc, hp', ← Category.assoc, ← f.comm 2 3]
    simp only [Category.assoc]

variable [HasBinaryBiproducts (HellerClassification.Projectives (C := C))]

/-- The cone projections and inclusions give its component splitting
inside the projective subcategory. -/
def degreeIso {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (hf : PeriodicCone.IsPeriodic S P R f) (n : ℤ) :
    term S (PeriodicCone.complex S P R f hf) n ≅ term S P (n + 1) ⊞ term S R n where
  hom := biprod.lift
    (ObjectProperty.homMk ((CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl))
    (ObjectProperty.homMk ((CochainComplex.mappingCone.snd f).v n n (by omega)))
  inv := biprod.desc
    (ObjectProperty.homMk ((CochainComplex.mappingCone.inl f).v (n + 1) n (by omega)))
    (ObjectProperty.homMk ((CochainComplex.mappingCone.inr f).f n))
  hom_inv_id := by
    rw [biprod.lift_desc]
    apply ObjectProperty.hom_ext
    exact CochainComplex.mappingCone.id_X f n (n + 1) rfl
  inv_hom_id := by
    apply biprod.hom_ext'
    all_goals apply biprod.hom_ext
    all_goals apply ObjectProperty.hom_ext
    all_goals simp

/-- Periodicity and the shift comparison identify degree three with shifted degree zero. -/
def stepIso (P : PeriodicComplexes.SComplex S) : term S P 3 ≅ (term S P 0)⟦(1 : ℤ)⟧ :=
  (HellerClassification.projectives (C := C)).isoMk (P.period 3).symm ≪≫ e.symm.app _

/-- The cone's third projective vertex in truncated-cone coordinates. -/
def degreeTwoIso {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (hf : PeriodicCone.IsPeriodic S P R f) :
    term S (PeriodicCone.complex S P R f hf) 2 ≅
      (term S P 0)⟦(1 : ℤ)⟧ ⊞ term S R 2 :=
  degreeIso S f hf 2 ≪≫ biprod.mapIso (stepIso S e P) (Iso.refl _)

variable [∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive]

local instance : PreservesBinaryBiproducts
    (shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ)) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

omit [FrobeniusAbelian C] [HasBinaryBiproducts (HellerClassification.Projectives (C := C))]
  [∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive]
  [HasShift (HellerClassification.Projectives (C := C)) ℤ] in
@[reassoc (attr := simp)]
lemma period_inv_fst {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (n : ℤ) :
    (PeriodicCone.period S P R f n).inv ≫
        S.functor.map ((CochainComplex.mappingCone.fst f).1.v
          (n - 3) ((n + 1) - 3) (by omega)) =
      (CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl ≫ (P.period (n + 1)).inv := by
  simp [PeriodicCone.period, Preadditive.add_comp, Category.assoc,
    ← Functor.map_comp]

omit [FrobeniusAbelian C] [HasBinaryBiproducts (HellerClassification.Projectives (C := C))]
  [∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive]
  [HasShift (HellerClassification.Projectives (C := C)) ℤ] in
@[reassoc (attr := simp)]
lemma period_inv_snd {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (n : ℤ) :
    (PeriodicCone.period S P R f n).inv ≫
        S.functor.map ((CochainComplex.mappingCone.snd f).v (n - 3) (n - 3) (by omega)) =
      (CochainComplex.mappingCone.snd f).v n n (by omega) ≫ (R.period n).inv := by
  simp [PeriodicCone.period, Preadditive.add_comp, Category.assoc,
    ← Functor.map_comp]

omit [FrobeniusAbelian C] in
/-- The first differential is the first truncated-cone matrix. -/
lemma cone_comm₁ {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (hf : PeriodicCone.IsPeriodic S P R f) :
    (truncation S e (PeriodicCone.complex S P R f hf)).mor₁ ≫
        (degreeIso S f hf 1).hom =
      (degreeIso S f hf 0).hom ≫ (truncatedCone (truncationMap S e f hf)).mor₁ := by
  apply biprod.hom_ext
  all_goals dsimp only [degreeIso, truncation, Triangle.mk, PeriodicCone.complex,
    truncatedCone, truncatedConeMor₁, truncationMap, term]
  all_goals simp only [Int.reduceAdd]
  all_goals simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    biprod.inl_fst, biprod.inr_fst, biprod.inl_snd, biprod.inr_snd,
    Category.comp_id, comp_zero, add_zero, zero_add,
    biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_zero]
  all_goals apply ObjectProperty.hom_ext
  · change (CochainComplex.mappingCone f).d 0 1 ≫
        (CochainComplex.mappingCone.fst f).1.v 1 2 rfl =
      -(CochainComplex.mappingCone.fst f).1.v 0 1 rfl ≫ P.complex.d 1 2
    exact CochainComplex.mappingCone.d_fst_v f 0 1 2 rfl rfl
  · change (CochainComplex.mappingCone f).d 0 1 ≫
        (CochainComplex.mappingCone.snd f).v 1 1 rfl =
      (CochainComplex.mappingCone.fst f).1.v 0 1 rfl ≫ f.f 1 +
        (CochainComplex.mappingCone.snd f).v 0 0 rfl ≫ R.complex.d 0 1
    exact CochainComplex.mappingCone.d_snd_v f 0 1 rfl

omit [FrobeniusAbelian C] in
/-- The second differential is the second truncated-cone matrix. -/
lemma cone_comm₂ {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (hf : PeriodicCone.IsPeriodic S P R f) :
    (truncation S e (PeriodicCone.complex S P R f hf)).mor₂ ≫
        (degreeTwoIso S e f hf).hom =
      (degreeIso S f hf 1).hom ≫ (truncatedCone (truncationMap S e f hf)).mor₂ := by
  apply biprod.hom_ext
  all_goals dsimp only [degreeTwoIso, Iso.trans_hom, biprod.mapIso_hom,
    degreeIso, stepIso, truncation, Triangle.mk, PeriodicCone.complex,
    truncatedCone, truncatedConeMor₂, truncationMap, term]
  all_goals simp only [Int.reduceAdd]
  all_goals simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    biprod.inl_fst, biprod.inr_fst, biprod.inl_snd, biprod.inr_snd,
    Category.comp_id, comp_zero, add_zero, zero_add,
    biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_snd,
    biprod.map_fst, biprod.map_snd, Iso.refl_hom,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_zero]
  all_goals apply ObjectProperty.hom_ext
  · dsimp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.isoMk,
      ObjectProperty.homMk, Iso.symm_hom, Iso.app_hom]
    simpa only [HellerClassification.projective_neg_hom,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Preadditive.neg_comp, Category.assoc] using
      congrArg (fun t => t ≫ (P.period 3).inv ≫ (e.inv.app (term S P 0)).hom)
        (CochainComplex.mappingCone.d_fst_v f 1 2 3 rfl rfl)
  · simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      neg_zero, zero_add, projective_add_hom] using CochainComplex.mappingCone.d_snd_v f 1 2 rfl

omit [Abelian C] [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive]
  [HasBinaryBiproducts (HellerClassification.Projectives (C := C))]
  [∀ n : ℤ, (shiftFunctor (HellerClassification.Projectives (C := C)) n).Additive] in
lemma inv_naturality_hom {X Y : HellerClassification.Projectives (C := C)} (a : X ⟶ Y) :
    (e.inv.app X).hom ≫ (a⟦(1 : ℤ)⟧').hom =
      S.functor.map a.hom ≫ (e.inv.app Y).hom := by
  simpa only [ObjectProperty.FullSubcategory.comp_hom,
    HellerClassification.projectiveEquivalence_map_hom] using
      congrArg (fun t => t.hom) (e.inv.naturality a).symm

omit [FrobeniusAbelian C] in
/-- The signed third differential, including the shift-biproduct
comparison, is the third truncated-cone matrix. -/
lemma cone_comm₃ {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (hf : PeriodicCone.IsPeriodic S P R f) :
    (truncation S e (PeriodicCone.complex S P R f hf)).mor₃ ≫
        ((degreeIso S f hf 0).hom)⟦(1 : ℤ)⟧' =
      (degreeTwoIso S e f hf).hom ≫ (truncatedCone (truncationMap S e f hf)).mor₃ := by
  apply (cancel_mono ((shiftFunctor (HellerClassification.Projectives (C := C)) (1 : ℤ)).mapBiprod
    (term S P 1) (term S R 0)).hom).mp
  dsimp only [truncatedCone, Triangle.mk, truncatedConeMor₃]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id, Category.comp_id]
  dsimp only [degreeIso]
  simp only [Int.reduceAdd]
  erw [biprod.map_lift_mapBiprod]
  apply biprod.hom_ext
  all_goals dsimp only [degreeTwoIso, Iso.trans_hom, biprod.mapIso_hom,
    degreeIso, stepIso, truncation, Triangle.mk, PeriodicCone.complex,
    truncatedConeMor₃Matrix, truncationMap, term]
  all_goals simp only [Int.reduceAdd, Int.reduceSub]
  all_goals simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    biprod.inl_fst, biprod.inr_fst, biprod.inl_snd, biprod.inr_snd,
    Category.comp_id, comp_zero, add_zero, zero_add,
    biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd,
    biprod.map_fst_assoc, biprod.map_snd_assoc, Iso.refl_hom,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_zero]
  all_goals apply ObjectProperty.hom_ext
  all_goals dsimp only [ObjectProperty.isoMk, Iso.app_hom, Iso.symm_hom]
  all_goals simp only [projective_add_hom, HellerClassification.projective_neg_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    Category.id_comp, Category.assoc]
  · change (CochainComplex.mappingCone f).d 2 3 ≫ (PeriodicCone.period S P R f 3).inv ≫
        (e.inv.app (term S (PeriodicCone.complex S P R f hf) 0)).hom ≫
        ((ObjectProperty.homMk ((CochainComplex.mappingCone.fst f).1.v 0 1 rfl) :
          term S (PeriodicCone.complex S P R f hf) 0 ⟶ term S P 1)⟦(1 : ℤ)⟧').hom =
      -((CochainComplex.mappingCone.fst f).1.v 2 3 rfl ≫ (P.period 3).inv ≫
        (e.inv.app (term S P 0)).hom ≫
        ((ObjectProperty.homMk (P.complex.d 0 1) : term S P 0 ⟶ term S P 1)⟦(1 : ℤ)⟧').hom)
    rw [inv_naturality_hom, inv_naturality_hom]
    simp only [ObjectProperty.homMk_hom]
    have hp := period_inv_fst S f 3
    simp only [Int.reduceAdd, Int.reduceSub] at hp
    erw [← Category.assoc (PeriodicCone.period S P R f 3).inv, hp]
    have hd := P.period_inv_comm 3 4
    simp only [Int.reduceSub] at hd
    have hc := congrArg (fun t => t ≫ (P.period 4).inv ≫ (e.inv.app (term S P 1)).hom)
      (CochainComplex.mappingCone.d_fst_v f 2 3 4 rfl rfl)
    simp only [Category.assoc, Preadditive.neg_comp] at hc
    erw [reassoc_of% hd] at hc
    simpa only [Category.assoc, Preadditive.neg_comp] using hc
  · change (CochainComplex.mappingCone f).d 2 3 ≫ (PeriodicCone.period S P R f 3).inv ≫
        (e.inv.app (term S (PeriodicCone.complex S P R f hf) 0)).hom ≫
        ((ObjectProperty.homMk ((CochainComplex.mappingCone.snd f).v 0 0 rfl) :
          term S (PeriodicCone.complex S P R f hf) 0 ⟶ term S R 0)⟦(1 : ℤ)⟧').hom =
      (CochainComplex.mappingCone.fst f).1.v 2 3 rfl ≫ (P.period 3).inv ≫
        (e.inv.app (term S P 0)).hom ≫
        ((ObjectProperty.homMk (f.f 0) : term S P 0 ⟶ term S R 0)⟦(1 : ℤ)⟧').hom +
      (CochainComplex.mappingCone.snd f).v 2 2 rfl ≫
        R.complex.d 2 3 ≫ (R.period 3).inv ≫ (e.inv.app (term S R 0)).hom
    rw [inv_naturality_hom, inv_naturality_hom]
    simp only [ObjectProperty.homMk_hom]
    have hp := period_inv_snd S f 3
    simp only [Int.reduceSub] at hp
    erw [← Category.assoc (PeriodicCone.period S P R f 3).inv, hp]
    have hf' : f.f 3 ≫ (R.period 3).inv = (P.period 3).inv ≫ S.functor.map (f.f 0) := by
      have h := PeriodicCone.periodic_comm S P R f hf 3
      simp only [Int.reduceSub] at h
      apply (cancel_epi (P.period 3).hom).mp
      apply (cancel_mono (R.period 3).hom).mp
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
        Category.comp_id] using h.symm
    have hc := congrArg (fun t => t ≫ (R.period 3).inv ≫ (e.inv.app (term S R 0)).hom)
      (CochainComplex.mappingCone.d_snd_v f 2 3 rfl)
    simp only [Category.assoc, Preadditive.add_comp] at hc
    erw [reassoc_of% hf'] at hc
    simpa only [Category.assoc] using hc

/-- Mapping-cone truncation is isomorphic to the truncated cone of the triangle map. -/
def coneTruncationIso {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (hf : PeriodicCone.IsPeriodic S P R f) :
    truncation S e (PeriodicCone.complex S P R f hf) ≅
      truncatedCone (truncationMap S e f hf) :=
  Triangle.isoMk _ _ (degreeIso S f hf 0) (degreeIso S f hf 1)
    (degreeTwoIso S e f hf) (cone_comm₁ S e f hf) (cone_comm₂ S e f hf)
      (cone_comm₃ S e f hf)

omit [HasBinaryBiproducts (HellerClassification.Projectives (C := C))] in
/-- A periodic truncation is distinguished exactly when it is δ-exact. -/
theorem truncation_distinguished_iff (p : HellerExactness.Parameter S)
    (P : PeriodicComplexes.SComplex S) :
    letI := HellerClassification.pretriangulated S p e
    truncation S e P ∈ distTriang (HellerClassification.Projectives (C := C)) ↔
      HellerExactness.DeltaExactTruncation S p (P.complex.d 0 1)
        (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv) := by
  change HellerExactness.DeltaExactTruncation S p _ _ _ ↔ _
  rw [truncation_third]
  rfl

/-- A good truncated cone gives a δ-exact periodic mapping cone. -/
theorem cone_exact_of_good (p : HellerExactness.Parameter S)
    {P R : PeriodicComplexes.SComplex S}
    (f : P.complex ⟶ R.complex) (hf : PeriodicCone.IsPeriodic S P R f)
    (hgood : letI := HellerClassification.pretriangulated S p e
      truncatedCone (truncationMap S e f hf) ∈
        distTriang (HellerClassification.Projectives (C := C))) :
    HellerExactness.DeltaExactTruncation S p ((CochainComplex.mappingCone f).d 0 1)
      ((CochainComplex.mappingCone f).d 1 2)
      ((CochainComplex.mappingCone f).d 2 3 ≫ (PeriodicCone.period S P R f 3).inv) := by
  let : CategoryTheory.Pretriangulated (HellerClassification.Projectives (C := C)) :=
    HellerClassification.pretriangulated S p e
  apply (truncation_distinguished_iff S e p (PeriodicCone.complex S P R f hf)).mp
  exact isomorphic_distinguished _ hgood _ (coneTruncationIso S e f hf)

end PretriangulatedV2.StableCategory.PeriodicConeTruncation
