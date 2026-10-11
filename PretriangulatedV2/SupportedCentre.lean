import PretriangulatedV2.Gemstone
import PretriangulatedV2.GemstoneObstruction
import PretriangulatedV2.Heller
import PretriangulatedV2.SquareZero
import PretriangulatedV2.NatTransExtension
import PretriangulatedV2.IndecomposableSplitting
import PretriangulatedV2.IndecomposableShift
import PretriangulatedV2.KrullSchmidt

/-!
The supported central transformation used in Section 6, and the shift
compatibility in Lemma 6.1 of arXiv:2608.09777v2.  The extension argument is
Chen--Ye Lemmas 2.4 and 2.7, proved explicitly in `NatTransExtension`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace PretriangulatedV2

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

omit [Preadditive C] in
/-- A central endomorphism transports naturally between any two objects
isomorphic to its support object. -/
theorem central_conjugates_natural {S Y Z : C} (a : S ⟶ S)
    (ha : ∀ g : S ⟶ S, a ≫ g = g ≫ a)
    (eY : Y ≅ S) (eZ : Z ≅ S) (f : Y ⟶ Z) :
    f ≫ (eZ.hom ≫ a ≫ eZ.inv) = (eY.hom ≫ a ≫ eY.inv) ≫ f := by
  apply (cancel_epi eY.inv).mp
  apply (cancel_mono eZ.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using (ha (eY.inv ≫ f ≫ eZ.hom)).symm

/-- The almost-vanishing component on one isomorphism class, zero elsewhere. -/
def supportedComponent (S : C) (a : S ⟶ S) (Y : C) : Y ⟶ Y := by
  classical
  exact if h : Nonempty (Y ≅ S) then h.some.hom ≫ a ≫ h.some.inv else 0

theorem supportedComponent_eq_conjugate {S Y : C} (a : S ⟶ S)
    (ha : ∀ g : S ⟶ S, a ≫ g = g ≫ a) (e : Y ≅ S) :
    supportedComponent S a Y = e.hom ≫ a ≫ e.inv := by
  classical
  dsimp only [supportedComponent]
  rw [dif_pos (show Nonempty (Y ≅ S) from ⟨e⟩)]
  simpa only [Category.id_comp, Category.comp_id] using
    (central_conjugates_natural a ha (Classical.choice (show Nonempty (Y ≅ S) from ⟨e⟩))
      e (𝟙 Y)).symm

theorem supportedComponent_eq_zero {S Y : C} (a : S ⟶ S)
    (hY : ¬ Nonempty (Y ≅ S)) : supportedComponent S a Y = 0 := by
  classical
  simp only [supportedComponent, dif_neg hY]

theorem supportedComponent_square_eq_zero {S : C} (a : S ⟶ S)
    (hsq : a ≫ a = 0) (Y : C) :
    supportedComponent S a Y ≫ supportedComponent S a Y = 0 := by
  classical
  by_cases hY : Nonempty (Y ≅ S)
  · simp only [supportedComponent, dif_pos hY, Category.assoc,
      Iso.inv_hom_id_assoc]
    simpa only [Category.assoc, comp_zero, zero_comp] using
      congrArg (fun g => hY.some.hom ≫ g ≫ hY.some.inv) hsq
  · simp only [supportedComponent_eq_zero a hY, zero_comp]

section IndecomposableNaturality

variable [HasBinaryBiproducts C] [IsIdempotentComplete C]

/-- The key non-isomorphism step in Chen--Ye Lemma 2.7, proved using actual
splitting of idempotents rather than assuming naturality. -/
theorem supportedComponent_natural {S Y Z : C} (a : S ⟶ S)
    (ha : IsAlmostVanishing a) (hcentral : ∀ g : S ⟶ S, a ≫ g = g ≫ a)
    (hY : Indecomposable Y) (hZ : Indecomposable Z) (f : Y ⟶ Z) :
    f ≫ supportedComponent S a Z = supportedComponent S a Y ≫ f := by
  classical
  by_cases hYS : Nonempty (Y ≅ S)
  · by_cases hZS : Nonempty (Z ≅ S)
    · rw [supportedComponent_eq_conjugate a hcentral hYS.some,
        supportedComponent_eq_conjugate a hcentral hZS.some]
      exact central_conjugates_natural a hcentral _ _ f
    · rw [supportedComponent_eq_zero a hZS,
        supportedComponent_eq_conjugate a hcentral hYS.some, comp_zero]
      apply Eq.symm
      apply (ha.endomorphism_conjugate hYS.some.symm).postcomp_eq_zero f
      intro hf
      let : IsSplitMono f := hf
      let : IsIso f := isIso_of_isSplitMono_of_indecomposable hY.1 hZ f
      exact hZS ⟨(asIso f).symm ≪≫ hYS.some⟩
  · by_cases hZS : Nonempty (Z ≅ S)
    · rw [supportedComponent_eq_zero a hYS,
        supportedComponent_eq_conjugate a hcentral hZS.some, zero_comp]
      apply (ha.endomorphism_conjugate hZS.some.symm).precomp_eq_zero f
      intro hf
      let : IsSplitEpi f := hf
      let : IsIso f := isIso_of_isSplitEpi_of_indecomposable hY hZ.1 f
      exact hYS ⟨asIso f ≪≫ hZS.some⟩
    · rw [supportedComponent_eq_zero a hYS, supportedComponent_eq_zero a hZS]
      simp only [comp_zero, zero_comp]

end IndecomposableNaturality

section GemstoneComponents

variable [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

namespace Gemstone

variable {X : C} (G : Gemstone X)

include G in
/-- Rigidity separates the two supported isomorphism classes. -/
theorem not_iso_shift : ¬ Nonempty (X ≅ X⟦(1 : ℤ)⟧) := by
  rintro ⟨e⟩
  apply G.indecomposable.1
  apply (IsZero.iff_id_eq_zero X).mpr
  have he := G.rigid e.hom
  calc
    𝟙 X = e.hom ≫ e.inv := e.hom_inv_id.symm
    _ = 0 := by rw [he]; simp

theorem shifted_alpha_central (f : X⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧) :
    G.alpha⟦(1 : ℤ)⟧' ≫ f = f ≫ G.alpha⟦(1 : ℤ)⟧' := by
  simpa only [Functor.map_comp, Functor.map_preimage] using
    congrArg (shiftFunctor C (1 : ℤ)).map
      (G.central ((shiftFunctor C (1 : ℤ)).preimage f))

/-- The two supported almost-vanishing components, before additive extension. -/
def supportedEndomorphism (Y : C) : Y ⟶ Y :=
  supportedComponent X G.alpha Y +
    supportedComponent (X⟦(1 : ℤ)⟧) (G.alpha⟦(1 : ℤ)⟧') Y

theorem supportedEndomorphism_eq_of_iso {Y : C} (e : Y ≅ X) :
    G.supportedEndomorphism Y = e.hom ≫ G.alpha ≫ e.inv := by
  have hY : ¬ Nonempty (Y ≅ X⟦(1 : ℤ)⟧) := by
    rintro ⟨d⟩
    exact G.not_iso_shift ⟨e.symm ≪≫ d⟩
  rw [supportedEndomorphism, supportedComponent_eq_zero _ hY, add_zero,
    supportedComponent_eq_conjugate G.alpha G.central e]

theorem supportedEndomorphism_eq_of_iso_shift {Y : C}
    (e : Y ≅ X⟦(1 : ℤ)⟧) :
    G.supportedEndomorphism Y = e.hom ≫ G.alpha⟦(1 : ℤ)⟧' ≫ e.inv := by
  have hY : ¬ Nonempty (Y ≅ X) := by
    rintro ⟨d⟩
    exact G.not_iso_shift ⟨d.symm ≪≫ e⟩
  rw [supportedEndomorphism, supportedComponent_eq_zero _ hY, zero_add,
    supportedComponent_eq_conjugate _ G.shifted_alpha_central e]

theorem supportedEndomorphism_eq_zero {Y : C} (hY : ¬ Nonempty (Y ≅ X))
    (hYs : ¬ Nonempty (Y ≅ X⟦(1 : ℤ)⟧)) : G.supportedEndomorphism Y = 0 := by
  rw [supportedEndomorphism, supportedComponent_eq_zero _ hY,
    supportedComponent_eq_zero _ hYs, add_zero]

theorem supportedEndomorphism_natural [IsIdempotentComplete C]
    {Y Z : C} (hY : Indecomposable Y) (hZ : Indecomposable Z) (f : Y ⟶ Z) :
    f ≫ G.supportedEndomorphism Z = G.supportedEndomorphism Y ≫ f := by
  simp only [supportedEndomorphism, Preadditive.comp_add, Preadditive.add_comp]
  rw [supportedComponent_natural G.alpha G.almostVanishing G.central hY hZ f,
    supportedComponent_natural _ G.almostVanishing.shift_one G.shifted_alpha_central hY hZ f]

/-- Periodicity identifies the second shifted component with the component
on the first support class. -/
theorem periodicity_conjugates_alpha :
    G.periodicity.inv ≫ G.alpha ≫ G.periodicity.hom =
      G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' := by
  apply (cancel_epi G.periodicity.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using G.compatible

/-- The supported components commute with suspension.  Both support classes
and the complement are checked, using full faithfulness of the actual shift. -/
theorem supportedEndomorphism_shift (Y : C) :
    (G.supportedEndomorphism Y)⟦(1 : ℤ)⟧' =
      G.supportedEndomorphism (Y⟦(1 : ℤ)⟧) := by
  classical
  let F := shiftFunctor C (1 : ℤ)
  by_cases hY : Nonempty (Y ≅ X)
  · let e := hY.some
    rw [G.supportedEndomorphism_eq_of_iso e,
      G.supportedEndomorphism_eq_of_iso_shift (F.mapIso e)]
    simp only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv, F]
  · by_cases hYs : Nonempty (Y ≅ X⟦(1 : ℤ)⟧)
    · let e := hYs.some
      rw [G.supportedEndomorphism_eq_of_iso_shift e,
        G.supportedEndomorphism_eq_of_iso (F.mapIso e ≪≫ G.periodicity.symm)]
      calc
        (e.hom ≫ G.alpha⟦(1 : ℤ)⟧' ≫ e.inv)⟦(1 : ℤ)⟧' =
            e.hom⟦(1 : ℤ)⟧' ≫ G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
              e.inv⟦(1 : ℤ)⟧' := by simp only [Functor.map_comp]
        _ = e.hom⟦(1 : ℤ)⟧' ≫
            (G.periodicity.inv ≫ G.alpha ≫ G.periodicity.hom) ≫
              e.inv⟦(1 : ℤ)⟧' := by rw [G.periodicity_conjugates_alpha]
        _ = (F.mapIso e ≪≫ G.periodicity.symm).hom ≫ G.alpha ≫
            (F.mapIso e ≪≫ G.periodicity.symm).inv := by
          simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
            Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc, F]
    · have hFY : ¬ Nonempty (Y⟦(1 : ℤ)⟧ ≅ X) := by
        rintro ⟨e⟩
        exact hYs ⟨F.preimageIso (e ≪≫ G.periodicity)⟩
      have hFYs : ¬ Nonempty (Y⟦(1 : ℤ)⟧ ≅ X⟦(1 : ℤ)⟧) := by
        rintro ⟨e⟩
        exact hY ⟨F.preimageIso e⟩
      rw [G.supportedEndomorphism_eq_zero hY hYs,
        G.supportedEndomorphism_eq_zero hFY hFYs, Functor.map_zero]

variable {k : Type w} [Field k] [Linear k C] [FiniteDimensional k (X ⟶ X)]

include k in
theorem supportedEndomorphism_square_eq_zero (Y : C) :
    G.supportedEndomorphism Y ≫ G.supportedEndomorphism Y = 0 := by
  classical
  by_cases hY : Nonempty (Y ≅ X)
  · rw [G.supportedEndomorphism_eq_of_iso hY.some]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, comp_zero, zero_comp] using
      congrArg (fun f => hY.some.hom ≫ f ≫ hY.some.inv) (G.alpha_sq_eq_zero (k := k))
  · rw [supportedEndomorphism, supportedComponent_eq_zero _ hY, zero_add]
    exact supportedComponent_square_eq_zero _ (G.shifted_alpha_sq_eq_zero (k := k)) Y

end Gemstone

end GemstoneComponents

section GlobalGemstoneUnit

variable [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  [IsIdempotentComplete C]

namespace Gemstone

variable {X : C} (G : Gemstone X)
  (hgen : ∀ Y : C, Nonempty (BinaryDecomposition Indecomposable Y))

/-- The global natural endomorphism obtained from the two gemstone support
classes by the finite direct-sum extension theorem. -/
def supportedNaturalEndomorphism : 𝟭 C ⟶ 𝟭 C :=
  extendNaturalEndomorphism hgen (fun Y _ => G.supportedEndomorphism Y)
    (fun _ _ hY hZ f => G.supportedEndomorphism_natural hY hZ f)

theorem supportedNaturalEndomorphism_app (Y : C) (hY : Indecomposable Y) :
    (G.supportedNaturalEndomorphism hgen).app Y = G.supportedEndomorphism Y :=
  extendNaturalEndomorphism_app hgen _ _ Y hY

/-- Checking shift compatibility on the generating family suffices for all
objects, by the proved uniqueness of additive natural-transformation extension. -/
theorem supportedNaturalEndomorphism_shift (Y : C) :
    ((G.supportedNaturalEndomorphism hgen).app Y)⟦(1 : ℤ)⟧' =
      (G.supportedNaturalEndomorphism hgen).app (Y⟦(1 : ℤ)⟧) := by
  let eta := G.supportedNaturalEndomorphism hgen
  let F := shiftFunctor C (1 : ℤ)
  let s : F ⟶ F := Functor.whiskerRight eta F
  let t : F ⟶ F := Functor.whiskerLeft F eta
  change s.app Y = t.app Y
  apply BinaryDecomposition.natTrans_eq s t _ (Classical.choice (hgen Y))
  intro Z hZ
  change ((G.supportedNaturalEndomorphism hgen).app Z)⟦(1 : ℤ)⟧' =
    (G.supportedNaturalEndomorphism hgen).app (Z⟦(1 : ℤ)⟧)
  rw [G.supportedNaturalEndomorphism_app hgen Z hZ,
    G.supportedNaturalEndomorphism_app hgen _ (indecomposable_shift Z 1 hZ)]
  exact G.supportedEndomorphism_shift Z

omit [IsIdempotentComplete C] in
/-- Objects with no summand in either support class receive a zero component,
even when they are decomposable. -/
theorem supportedDecomposition_eq_zero {Y : C}
    (d : BinaryDecomposition Indecomposable Y)
    (hX : ∀ f : X ⟶ Y, ¬ IsSplitMono f)
    (hs : ∀ f : X⟦(1 : ℤ)⟧ ⟶ Y, ¬ IsSplitMono f) :
    d.endomorphism (fun Z _ => G.supportedEndomorphism Z) = 0 := by
  induction d with
  | zero => rfl
  | atom Y hY =>
      apply G.supportedEndomorphism_eq_zero
      · rintro ⟨e⟩
        exact hX e.inv (inferInstance)
      · rintro ⟨e⟩
        exact hs e.inv (inferInstance)
  | @iso Y Z e d ih =>
      have hX' : ∀ f : X ⟶ Z, ¬ IsSplitMono f := by
        intro f hf
        let : IsSplitMono f := hf
        exact hX (f ≫ e.inv) (inferInstance)
      have hs' : ∀ f : X⟦(1 : ℤ)⟧ ⟶ Z, ¬ IsSplitMono f := by
        intro f hf
        let : IsSplitMono f := hf
        exact hs (f ≫ e.inv) (inferInstance)
      simp only [BinaryDecomposition.endomorphism, ih hX' hs', comp_zero, zero_comp]
  | @sum Y Z dY dZ ihY ihZ =>
      have hXY : ∀ f : X ⟶ Y, ¬ IsSplitMono f := by
        intro f hf
        let : IsSplitMono f := hf
        exact hX (f ≫ biprod.inl) (inferInstance)
      have hsY : ∀ f : X⟦(1 : ℤ)⟧ ⟶ Y, ¬ IsSplitMono f := by
        intro f hf
        let : IsSplitMono f := hf
        exact hs (f ≫ biprod.inl) (inferInstance)
      have hXZ : ∀ f : X ⟶ Z, ¬ IsSplitMono f := by
        intro f hf
        let : IsSplitMono f := hf
        exact hX (f ≫ biprod.inr) (inferInstance)
      have hsZ : ∀ f : X⟦(1 : ℤ)⟧ ⟶ Z, ¬ IsSplitMono f := by
        intro f hf
        let : IsSplitMono f := hf
        exact hs (f ≫ biprod.inr) (inferInstance)
      simp only [BinaryDecomposition.endomorphism, ihY hXY hsY, ihZ hXZ hsZ]
      ext <;> simp

theorem supportedNaturalEndomorphism_app_eq_zero_of_no_sections (Y : C)
    (hX : ∀ f : X ⟶ Y, ¬ IsSplitMono f)
    (hs : ∀ f : X⟦(1 : ℤ)⟧ ⟶ Y, ¬ IsSplitMono f) :
    (G.supportedNaturalEndomorphism hgen).app Y = 0 :=
  G.supportedDecomposition_eq_zero (Classical.choice (hgen Y)) hX hs

theorem supportedNaturalEndomorphism_app_eq_zero_of_no_retracts (Y : C)
    (hX : ¬ Nonempty (Retract X Y))
    (hs : ¬ Nonempty (Retract (X⟦(1 : ℤ)⟧) Y)) :
    (G.supportedNaturalEndomorphism hgen).app Y = 0 := by
  apply G.supportedNaturalEndomorphism_app_eq_zero_of_no_sections hgen Y
  · intro f hf
    let : IsSplitMono f := hf
    exact hX ⟨⟨f, retraction f, IsSplitMono.id f⟩⟩
  · intro f hf
    let : IsSplitMono f := hf
    exact hs ⟨⟨f, retraction f, IsSplitMono.id f⟩⟩

variable {k : Type w} [Field k] [Linear k C] [FiniteDimensional k (X ⟶ X)]

include k in
theorem supportedNaturalEndomorphism_square_eq_zero (Y : C) :
    (G.supportedNaturalEndomorphism hgen).app Y ≫
      (G.supportedNaturalEndomorphism hgen).app Y = 0 :=
  extendNaturalEndomorphism_square_eq_zero hgen _ _
    (fun Z _ => G.supportedEndomorphism_square_eq_zero (k := k) Z) Y

/-- Lemma 6.1 with finite indecomposable generation exposed as the precise
categorical input.  The global unit and its naturality are constructed here. -/
def supportedTriangleCenterUnit : TriangleCenterUnit (shiftFunctor C (1 : ℤ)) where
  iso := idPlusSquareZero (G.supportedNaturalEndomorphism hgen)
    (G.supportedNaturalEndomorphism_square_eq_zero (k := k) hgen)
  commutes := idPlusSquareZero_commutes (shiftFunctor C (1 : ℤ))
    (G.supportedNaturalEndomorphism hgen)
    (G.supportedNaturalEndomorphism_square_eq_zero (k := k) hgen)
    (G.supportedNaturalEndomorphism_shift hgen)

theorem supportedTriangleCenterUnit_app (Y : C) (hY : Indecomposable Y) :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app Y =
      𝟙 Y + G.supportedEndomorphism Y := by
  rw [supportedTriangleCenterUnit, idPlusSquareZero_hom_app,
    G.supportedNaturalEndomorphism_app hgen Y hY]
  rfl

theorem supportedTriangleCenterUnit_app_self :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app X = 𝟙 X + G.alpha := by
  rw [G.supportedTriangleCenterUnit_app hgen X G.indecomposable,
    G.supportedEndomorphism_eq_of_iso (Iso.refl X)]
  simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]

theorem supportedTriangleCenterUnit_app_shift :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app (X⟦(1 : ℤ)⟧) =
      𝟙 (X⟦(1 : ℤ)⟧) + G.alpha⟦(1 : ℤ)⟧' := by
  rw [G.supportedTriangleCenterUnit_app hgen _
      (indecomposable_shift X 1 G.indecomposable),
    G.supportedEndomorphism_eq_of_iso_shift (Iso.refl _)]
  simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]

theorem supportedTriangleCenterUnit_app_outside (Y : C) (hY : Indecomposable Y)
    (hYX : ¬ Nonempty (Y ≅ X)) (hYs : ¬ Nonempty (Y ≅ X⟦(1 : ℤ)⟧)) :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app Y = 𝟙 Y := by
  rw [G.supportedTriangleCenterUnit_app hgen Y hY,
    G.supportedEndomorphism_eq_zero hYX hYs, add_zero]

theorem supportedTriangleCenterUnit_app_eq_id_of_no_retracts (Y : C)
    (hX : ¬ Nonempty (Retract X Y))
    (hs : ¬ Nonempty (Retract (X⟦(1 : ℤ)⟧) Y)) :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app Y = 𝟙 Y := by
  rw [supportedTriangleCenterUnit, idPlusSquareZero_hom_app,
    G.supportedNaturalEndomorphism_app_eq_zero_of_no_retracts hgen Y hX hs]
  simp only [Functor.id_obj, add_zero]

/-- The finite-sum extension is unique, as in Chen--Ye Lemma 2.7. -/
theorem supportedTriangleCenterUnit_unique (u : 𝟭 C ≅ 𝟭 C)
    (hu : ∀ (Y : C), Indecomposable Y → u.hom.app Y =
      𝟙 Y + G.supportedEndomorphism Y) :
    u = (G.supportedTriangleCenterUnit (k := k) hgen).iso := by
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  apply BinaryDecomposition.natTrans_eq u.hom
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom _
    (Classical.choice (hgen Y))
  intro Z hZ
  rw [hu Z hZ, G.supportedTriangleCenterUnit_app hgen Z hZ]

end Gemstone

end GlobalGemstoneUnit

section GemstoneVertexComponents

variable [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  [IsIdempotentComplete C]
  {k : Type w} [Field k] [Linear k C]
  [∀ Y Z : C, FiniteDimensional k (Y ⟶ Z)]
  [Functor.Linear k (shiftFunctor C (1 : ℤ))]

namespace Gemstone

variable {X : C} (G : Gemstone X)
  (hgen : ∀ Y : C, Nonempty (BinaryDecomposition Indecomposable Y))

/-- Lemma 5.5 excludes both support summands from the middle vertex. -/
theorem supportedTriangleCenterUnit_app_middle :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app G.middle =
      𝟙 G.middle := by
  rw [supportedTriangleCenterUnit, idPlusSquareZero_hom_app,
    G.supportedNaturalEndomorphism_app_eq_zero_of_no_sections hgen G.middle
      (G.not_isSplitMono_to_middle (k := k))
      (G.not_isSplitMono_shift_to_middle (k := k))]
  simp only [Functor.id_obj, add_zero]

/-- Lemmas 5.5 and 5.7 exclude both support summands from the cone vertex. -/
theorem supportedTriangleCenterUnit_app_cone (K : GemstoneCone G) :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app K.Y = 𝟙 K.Y :=
  G.supportedTriangleCenterUnit_app_eq_id_of_no_retracts hgen K.Y
    (G.lemma_5_7_no_retract (k := k) K)
    (G.lemma_5_5_no_retracts (k := k) K).2.2.1

theorem supportedTriangleCenterUnit_app_shift_middle :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app
      (G.middle⟦(1 : ℤ)⟧) = 𝟙 (G.middle⟦(1 : ℤ)⟧) := by
  rw [← (G.supportedTriangleCenterUnit (k := k) hgen).commutes,
    G.supportedTriangleCenterUnit_app_middle hgen]
  exact (shiftFunctor C (1 : ℤ)).map_id _

theorem supportedTriangleCenterUnit_app_shift_cone (K : GemstoneCone G) :
    (G.supportedTriangleCenterUnit (k := k) hgen).iso.hom.app
      (K.Y⟦(1 : ℤ)⟧) = 𝟙 (K.Y⟦(1 : ℤ)⟧) := by
  rw [← (G.supportedTriangleCenterUnit (k := k) hgen).commutes,
    G.supportedTriangleCenterUnit_app_cone hgen K]
  exact (shiftFunctor C (1 : ℤ)).map_id _

end Gemstone

end GemstoneVertexComponents

section HomFiniteGemstoneUnit

variable [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  [IsIdempotentComplete C]
  {k : Type w} [Field k] [Linear k C]
  [∀ Y Z : C, FiniteDimensional k (Y ⟶ Z)]

namespace Gemstone

variable {X : C} (G : Gemstone X)

/-- The supported global triangle-centre unit of Section 6, with finite
generation proved from Hom finiteness rather than assumed. -/
def triangleCenterUnit : TriangleCenterUnit (shiftFunctor C (1 : ℤ)) :=
  G.supportedTriangleCenterUnit (k := k)
    (fun Y => nonempty_indecomposable_decomposition (k := k) Y)

theorem triangleCenterUnit_app_self :
    (G.triangleCenterUnit (k := k)).iso.hom.app X = 𝟙 X + G.alpha :=
  G.supportedTriangleCenterUnit_app_self _

theorem triangleCenterUnit_app_shift :
    (G.triangleCenterUnit (k := k)).iso.hom.app (X⟦(1 : ℤ)⟧) =
      𝟙 (X⟦(1 : ℤ)⟧) + G.alpha⟦(1 : ℤ)⟧' :=
  G.supportedTriangleCenterUnit_app_shift _

theorem triangleCenterUnit_app_outside (Y : C) (hY : Indecomposable Y)
    (hYX : ¬ Nonempty (Y ≅ X)) (hYs : ¬ Nonempty (Y ≅ X⟦(1 : ℤ)⟧)) :
    (G.triangleCenterUnit (k := k)).iso.hom.app Y = 𝟙 Y :=
  G.supportedTriangleCenterUnit_app_outside _ Y hY hYX hYs

/-- The three component prescriptions in Section 6 uniquely determine the
natural isomorphism, including on all objects in the two support classes. -/
theorem triangleCenterUnit_unique (u : 𝟭 C ≅ 𝟭 C)
    (huX : u.hom.app X = 𝟙 X + G.alpha)
    (hus : u.hom.app (X⟦(1 : ℤ)⟧) =
      𝟙 (X⟦(1 : ℤ)⟧) + G.alpha⟦(1 : ℤ)⟧')
    (huo : ∀ (Y : C), Indecomposable Y → ¬ Nonempty (Y ≅ X) →
      ¬ Nonempty (Y ≅ X⟦(1 : ℤ)⟧) → u.hom.app Y = 𝟙 Y) :
    u = (G.triangleCenterUnit (k := k)).iso := by
  classical
  apply G.supportedTriangleCenterUnit_unique _ u
  intro Y hY
  by_cases hYX : Nonempty (Y ≅ X)
  · let e := hYX.some
    rw [G.supportedEndomorphism_eq_of_iso e]
    apply (cancel_mono e.hom).mp
    calc
      u.hom.app Y ≫ e.hom = e.hom ≫ u.hom.app X :=
        (u.hom.naturality e.hom).symm
      _ = (𝟙 Y + e.hom ≫ G.alpha ≫ e.inv) ≫ e.hom := by
        rw [huX]
        simp only [Preadditive.comp_add, Preadditive.add_comp, Category.comp_id,
          Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · by_cases hYs : Nonempty (Y ≅ X⟦(1 : ℤ)⟧)
    · let e := hYs.some
      rw [G.supportedEndomorphism_eq_of_iso_shift e]
      apply (cancel_mono e.hom).mp
      calc
        u.hom.app Y ≫ e.hom = e.hom ≫ u.hom.app (X⟦(1 : ℤ)⟧) :=
          (u.hom.naturality e.hom).symm
        _ = (𝟙 Y + e.hom ≫ G.alpha⟦(1 : ℤ)⟧' ≫ e.inv) ≫ e.hom := by
          rw [hus]
          simp only [Preadditive.comp_add, Preadditive.add_comp, Category.comp_id,
            Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [huo Y hY hYX hYs, G.supportedEndomorphism_eq_zero hYX hYs, add_zero]

include k in
/-- Lemma 6.1, including the preceding construction of the natural unit. -/
theorem lemma_6_1 :
    ∃ u : TriangleCenterUnit (shiftFunctor C (1 : ℤ)),
      u.iso.hom.app X = 𝟙 X + G.alpha ∧
      u.iso.hom.app (X⟦(1 : ℤ)⟧) = 𝟙 (X⟦(1 : ℤ)⟧) + G.alpha⟦(1 : ℤ)⟧' ∧
      ∀ (Y : C), Indecomposable Y → ¬ Nonempty (Y ≅ X) →
        ¬ Nonempty (Y ≅ X⟦(1 : ℤ)⟧) → u.iso.hom.app Y = 𝟙 Y :=
  ⟨G.triangleCenterUnit (k := k), G.triangleCenterUnit_app_self,
    G.triangleCenterUnit_app_shift, G.triangleCenterUnit_app_outside⟩

variable [Functor.Linear k (shiftFunctor C (1 : ℤ))]

theorem triangleCenterUnit_app_middle :
    (G.triangleCenterUnit (k := k)).iso.hom.app G.middle = 𝟙 G.middle :=
  G.supportedTriangleCenterUnit_app_middle _

theorem triangleCenterUnit_app_cone (K : GemstoneCone G) :
    (G.triangleCenterUnit (k := k)).iso.hom.app K.Y = 𝟙 K.Y :=
  G.supportedTriangleCenterUnit_app_cone _ K

theorem triangleCenterUnit_app_shift_middle :
    (G.triangleCenterUnit (k := k)).iso.hom.app (G.middle⟦(1 : ℤ)⟧) =
      𝟙 (G.middle⟦(1 : ℤ)⟧) :=
  G.supportedTriangleCenterUnit_app_shift_middle _

theorem triangleCenterUnit_app_shift_cone (K : GemstoneCone G) :
    (G.triangleCenterUnit (k := k)).iso.hom.app (K.Y⟦(1 : ℤ)⟧) =
      𝟙 (K.Y⟦(1 : ℤ)⟧) :=
  G.supportedTriangleCenterUnit_app_shift_cone _ K

end Gemstone

end HomFiniteGemstoneUnit

end PretriangulatedV2
