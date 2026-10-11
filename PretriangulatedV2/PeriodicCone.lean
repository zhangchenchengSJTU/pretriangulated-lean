import PretriangulatedV2.MappingConeCycles
import PretriangulatedV2.PeriodicExactnessBridge

/-! Genuine S-periodicity of the mapping cone of a periodic cochain map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

namespace PretriangulatedV2.StableCategory.PeriodicCone

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
variable (S : C ≌ C) [S.functor.Additive]
variable (P R : PeriodicComplexes.SComplex S) (f : P.complex ⟶ R.complex)

/-- The map commutes with the specified actual S-periodicities. -/
def IsPeriodic : Prop := P.twistMap R f = f

omit [HasBinaryBiproducts C] [S.functor.Additive] in
lemma periodic_comm (hf : IsPeriodic S P R f) (n : ℤ) :
    S.functor.map (f.f (n - 3)) ≫ (R.period n).hom =
      (P.period n).hom ≫ f.f n := by
  have h := congrArg (fun t => t.f n) hf
  dsimp only [IsPeriodic, PeriodicComplexes.SComplex.twistMap] at h
  apply (cancel_epi (P.period n).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id] using h

private lemma mapped_ext_from (n m : ℤ) (hmn : m = n + 1) {W : C}
    {a b : S.functor.obj ((CochainComplex.mappingCone f).X n) ⟶ W}
    (h₁ : S.functor.map ((CochainComplex.mappingCone.inl f).v m n (by omega)) ≫ a =
      S.functor.map ((CochainComplex.mappingCone.inl f).v m n (by omega)) ≫ b)
    (h₂ : S.functor.map ((CochainComplex.mappingCone.inr f).f n) ≫ a =
      S.functor.map ((CochainComplex.mappingCone.inr f).f n) ≫ b) : a = b := by
  have ht := congrArg (fun t => S.functor.map t)
    (CochainComplex.mappingCone.id_X f n m (by omega))
  simp only [Functor.map_add, Functor.map_comp] at ht
  calc
    a = S.functor.map (𝟙 _) ≫ a := by simp
    _ = (S.functor.map ((CochainComplex.mappingCone.fst f).1.v n m (by omega)) ≫
          S.functor.map ((CochainComplex.mappingCone.inl f).v m n (by omega)) +
        S.functor.map ((CochainComplex.mappingCone.snd f).v n n (by omega)) ≫
          S.functor.map ((CochainComplex.mappingCone.inr f).f n)) ≫ a := by rw [ht]
    _ = (S.functor.map ((CochainComplex.mappingCone.fst f).1.v n m (by omega)) ≫
          S.functor.map ((CochainComplex.mappingCone.inl f).v m n (by omega)) +
        S.functor.map ((CochainComplex.mappingCone.snd f).v n n (by omega)) ≫
          S.functor.map ((CochainComplex.mappingCone.inr f).f n)) ≫ b := by
      simp only [Preadditive.add_comp, Category.assoc, h₁, h₂]
    _ = b := by rw [ht]; simp

/-- The explicit period isomorphism of actual cone components. -/
def period (n : ℤ) :
    S.functor.obj ((CochainComplex.mappingCone f).X (n - 3)) ≅
      (CochainComplex.mappingCone f).X n where
  hom := S.functor.map ((CochainComplex.mappingCone.fst f).1.v
      (n - 3) ((n + 1) - 3) (by omega)) ≫ (P.period (n + 1)).hom ≫
      (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) +
    S.functor.map ((CochainComplex.mappingCone.snd f).v (n - 3) (n - 3) (by omega)) ≫
      (R.period n).hom ≫ (CochainComplex.mappingCone.inr f).f n
  inv := (CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl ≫
      (P.period (n + 1)).inv ≫ S.functor.map
        ((CochainComplex.mappingCone.inl f).v ((n + 1) - 3) (n - 3) (by omega)) +
    (CochainComplex.mappingCone.snd f).v n n (by omega) ≫ (R.period n).inv ≫
      S.functor.map ((CochainComplex.mappingCone.inr f).f (n - 3))
  hom_inv_id := by
    apply mapped_ext_from S P R f (n - 3) ((n + 1) - 3) (by omega)
    · simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        ← Functor.map_comp_assoc, CochainComplex.mappingCone.inl_v_fst_v,
        CochainComplex.mappingCone.inl_v_snd_v, Functor.map_zero,
        CategoryTheory.Functor.map_id, Category.id_comp, zero_comp, comp_zero,
        add_zero, Iso.hom_inv_id_assoc, Category.comp_id,
        CochainComplex.mappingCone.inl_v_fst_v_assoc,
        CochainComplex.mappingCone.inl_v_snd_v_assoc]
    · simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        ← Functor.map_comp_assoc, CochainComplex.mappingCone.inr_f_fst_v,
        CochainComplex.mappingCone.inr_f_snd_v, Functor.map_zero,
        CategoryTheory.Functor.map_id, Category.id_comp, zero_comp, comp_zero,
        zero_add, Iso.hom_inv_id_assoc, Category.comp_id,
        CochainComplex.mappingCone.inr_f_fst_v_assoc,
        CochainComplex.mappingCone.inr_f_snd_v_assoc]
  inv_hom_id := by
    apply CochainComplex.mappingCone.ext_from f (n + 1) n rfl
    · simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        CochainComplex.mappingCone.inl_v_fst_v_assoc,
        CochainComplex.mappingCone.inl_v_snd_v_assoc,
        zero_comp, comp_zero, add_zero, ← Functor.map_comp_assoc,
        CochainComplex.mappingCone.inl_v_fst_v, CochainComplex.mappingCone.inl_v_snd_v,
        Functor.map_zero, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_assoc, Category.comp_id]
    · simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        CochainComplex.mappingCone.inr_f_fst_v_assoc,
        CochainComplex.mappingCone.inr_f_snd_v_assoc,
        zero_comp, comp_zero, zero_add, ← Functor.map_comp_assoc,
        CochainComplex.mappingCone.inr_f_fst_v, CochainComplex.mappingCone.inr_f_snd_v,
        Functor.map_zero, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_assoc, Category.comp_id]

@[reassoc (attr := simp)]
lemma map_inl_period (n : ℤ) :
    S.functor.map ((CochainComplex.mappingCone.inl f).v
        ((n + 1) - 3) (n - 3) (by omega)) ≫ (period S P R f n).hom =
      (P.period (n + 1)).hom ≫
        (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) := by
  simp [period, Preadditive.comp_add, ← Functor.map_comp_assoc]

@[reassoc (attr := simp)]
lemma map_inr_period (n : ℤ) :
    S.functor.map ((CochainComplex.mappingCone.inr f).f (n - 3)) ≫
        (period S P R f n).hom =
      (R.period n).hom ≫ (CochainComplex.mappingCone.inr f).f n := by
  simp [period, Preadditive.comp_add, ← Functor.map_comp_assoc]

/-- Compatibility of the actual cone differential with the constructed
period isomorphisms follows from the input periods and periodicity of f. -/
lemma period_comm (hf : IsPeriodic S P R f) (i j : ℤ) :
    S.functor.map ((CochainComplex.mappingCone f).d (i - 3) (j - 3)) ≫
        (period S P R f j).hom =
      (period S P R f i).hom ≫ (CochainComplex.mappingCone f).d i j := by
  by_cases hij : j = i + 1
  · subst j
    apply mapped_ext_from S P R f (i - 3) ((i + 1) - 3) (by omega)
    · rw [← Functor.map_comp_assoc,
        CochainComplex.mappingCone.inl_v_d f ((i + 1) - 3) (i - 3) (((i + 1) + 1) - 3)
          (by omega) (by omega)]
      simp only [Functor.map_sub, Functor.map_comp, Preadditive.sub_comp, Category.assoc,
        map_inr_period, map_inl_period]
      rw [← Category.assoc, periodic_comm S P R f hf (i + 1)]
      rw [← Category.assoc, P.period_comm (i + 1) ((i + 1) + 1)]
      rw [map_inl_period_assoc,
        CochainComplex.mappingCone.inl_v_d f (i + 1) i ((i + 1) + 1) (by omega) (by omega)]
      simp [Preadditive.comp_sub, Category.assoc]
    · rw [← Functor.map_comp_assoc, CochainComplex.mappingCone.inr_f_d]
      simp only [Functor.map_comp, Category.assoc, map_inr_period]
      rw [← Category.assoc, R.period_comm i (i + 1), map_inr_period_assoc,
        CochainComplex.mappingCone.inr_f_d]
      simp only [Category.assoc]
  · have hij' : ¬(ComplexShape.up ℤ).Rel i j := by
      simpa only [ComplexShape.up_Rel, eq_comm] using hij
    have hij'' : ¬(ComplexShape.up ℤ).Rel (i - 3) (j - 3) := by
      change ¬(i - 3) + 1 = j - 3
      omega
    simp [HomologicalComplex.shape _ _ _ hij',
      HomologicalComplex.shape _ _ _ hij'']

/-- The actual mapping cone inherits an S-periodic-complex structure. -/
def complex (hf : IsPeriodic S P R f) : PeriodicComplexes.SComplex S where
  complex := CochainComplex.mappingCone f
  projective := MappingConeCycles.cone_projective f P.projective R.projective
  period := period S P R f
  period_comm := period_comm S P R f hf

@[reassoc (attr := simp)]
lemma inl_period_inv (n : ℤ) :
    (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) ≫
        (period S P R f n).inv =
      (P.period (n + 1)).inv ≫ S.functor.map
        ((CochainComplex.mappingCone.inl f).v ((n + 1) - 3) (n - 3) (by omega)) := by
  apply (cancel_mono (period S P R f n).hom).mp
  simp [Category.assoc]

@[reassoc (attr := simp)]
lemma inr_period_inv (n : ℤ) :
    (CochainComplex.mappingCone.inr f).f n ≫ (period S P R f n).inv =
      (R.period n).inv ≫ S.functor.map ((CochainComplex.mappingCone.inr f).f (n - 3)) := by
  apply (cancel_mono (period S P R f n).hom).mp
  simp [Category.assoc]

/-- Reindex and transport a genuine cochain homotopy by the specified
S-periodicity, without requiring the homotopy itself to be periodic. -/
def twistHomotopy {g : P.complex ⟶ R.complex} (H : Homotopy f g) :
    Homotopy (P.twistMap R f) (P.twistMap R g) where
  hom p q := (P.period p).inv ≫ S.functor.map (H.hom (p - 3) (q - 3)) ≫ (R.period q).hom
  zero p q hpq := by
    rw [H.zero (p - 3) (q - 3) (by
      change ¬(q - 3) + 1 = p - 3
      have h : ¬ q + 1 = p := hpq
      omega), Functor.map_zero]
    simp
  comm n := by
    have hp : (ComplexShape.up ℤ).Rel n (n + 1) := by change n + 1 = n + 1; rfl
    have hm : (ComplexShape.up ℤ).Rel (n - 1) n := by change n - 1 + 1 = n; omega
    rw [dNext_eq _ hp, prevD_eq _ hm]
    have he := H.comm (n - 3)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (n - 3) ((n + 1) - 3) by
      change n - 3 + 1 = n + 1 - 3; omega),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel ((n - 1) - 3) (n - 3) by
        change (n - 1) - 3 + 1 = n - 3; omega)] at he
    apply (cancel_epi (P.period n).hom).mp
    dsimp only [PeriodicComplexes.SComplex.twistMap]
    simp only [Preadditive.comp_add, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (P.period n).hom, ← P.period_comm n (n + 1)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← R.period_comm (n - 1) n]
    simp only [← Functor.map_comp_assoc]
    rw [he]
    simp [Functor.map_add, Preadditive.add_comp]

/-- For periodic endpoints, the transported homotopy is another actual
homotopy between the original maps. -/
def periodicHomotopy {g : P.complex ⟶ R.complex}
    (hf : IsPeriodic S P R f) (hg : IsPeriodic S P R g) (H : Homotopy f g) :
    Homotopy f g :=
  (Homotopy.ofEq hf.symm).trans ((twistHomotopy S P R f H).trans (Homotopy.ofEq hg))

omit [HasBinaryBiproducts C] in
@[simp]
lemma periodicHomotopy_hom {g : P.complex ⟶ R.complex}
    (hf : IsPeriodic S P R f) (hg : IsPeriodic S P R g) (H : Homotopy f g) (p q : ℤ) :
    (periodicHomotopy S P R f hf hg H).hom p q =
      (P.period p).inv ≫ S.functor.map (H.hom (p - 3) (q - 3)) ≫ (R.period q).hom := by
  simp [periodicHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom, twistHomotopy]

/-- The transported homotopy gives exactly the S-twist of the actual change
of mapping cone. This is the chain-level identity used in Proposition 4.2. -/
theorem theta_twist {g : P.complex ⟶ R.complex}
    (hf : IsPeriodic S P R f) (hg : IsPeriodic S P R g) (H : Homotopy f g) :
    (complex S P R f hf).twistMap (complex S P R g hg)
        (ConeHomotopy.thetaOfHomotopy f g H) =
      ConeHomotopy.thetaOfHomotopy f g (periodicHomotopy S P R f hf hg H) := by
  ext n
  apply CochainComplex.mappingCone.ext_from f (n + 1) n rfl
  · dsimp only [PeriodicComplexes.SComplex.twistMap, complex]
    rw [← Category.assoc, inl_period_inv, Category.assoc,
      ← Functor.map_comp_assoc,
      ConeHomotopy.inl_thetaOfHomotopy_f f g H ((n + 1) - 3) (n - 3) (by omega)]
    simp only [Functor.map_add, Functor.map_comp, Preadditive.comp_add,
      Preadditive.add_comp, Category.assoc, map_inl_period, map_inr_period,
      Iso.inv_hom_id_assoc, ConeHomotopy.inl_thetaOfHomotopy_f,
      periodicHomotopy_hom]
  · dsimp only [PeriodicComplexes.SComplex.twistMap, complex]
    rw [← Category.assoc, inr_period_inv, Category.assoc,
      ← Functor.map_comp_assoc, ConeHomotopy.inr_thetaOfHomotopy_f]
    simp

end PretriangulatedV2.StableCategory.PeriodicCone
