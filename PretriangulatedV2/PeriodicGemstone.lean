import PretriangulatedV2.PeriodicResolution
import PretriangulatedV2.AlmostSplitSequences
import PretriangulatedV2.StableIdempotents
import PretriangulatedV2.IndecomposableShift
import PretriangulatedV2.Gemstone
import PretriangulatedV2.HellerClassification
import PretriangulatedV2.StableIsoReflection
import PretriangulatedV2.StableSerreDuality

/-!
Proposition 7.1 after its algebraic periodic resolution. The Serre duality
input is explicitly supplied as actual natural pairing data; construction
of that pairing from the paper's projective Calabi–Yau hypothesis belongs
to the independent Serre bridge. This file does not assume existence of
almost-vanishing maps or a gemstone.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped IsMulCommutative

namespace PretriangulatedV2.StableCategory.PeriodicGemstone

universe v u w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C] {k : Type w} [Field k] [Linear k C]
  {M L : C} [Projective M] [Projective L] (D : PeriodicResolution.Data M L)

include k

/-- The actual ambient quotient object is indecomposable, by transporting
idempotents through the proved endomorphism algebra isomorphism. -/
theorem X_indecomposable (hM : Indecomposable M) (hiota : D.iota ≠ 0) :
    Indecomposable D.X := by
  apply AlmostSplitSequences.indecomposable_of_idempotents_trivial
  · intro h
    exact D.stable_X_not_isZero hiota ((projectiveStableQuotient (C := C)).map_isZero h)
  · intro a ha
    let e := D.endAlgEquiv (k := k)
    have ha' : IsIdempotentElem (e.symm a) := by
      change e.symm a * e.symm a = e.symm a
      rw [← map_mul]
      exact congrArg e.symm ha
    rcases AlmostVanishingSerre.idempotent_eq_zero_or_one hM (e.symm a) ha' with h | h
    · left
      apply e.symm.injective
      simpa using h
    · right
      exact e.symm.injective (h.trans (map_one e.symm).symm)

theorem stable_X_indecomposable (hM : Indecomposable M) (hiota : D.iota ≠ 0) :
    Indecomposable ((projectiveStableQuotient (C := C)).obj D.X) := by
  apply AlmostSplitSequences.indecomposable_of_idempotents_trivial (D.stable_X_not_isZero hiota)
  intro a ha
  let e := D.projectiveStableEndAlgEquiv (k := k)
  have ha' : IsIdempotentElem (e.symm a) := by
    change e.symm a * e.symm a = e.symm a
    rw [← map_mul]
    exact congrArg e.symm ha
  rcases AlmostVanishingSerre.idempotent_eq_zero_or_one hM (e.symm a) ha' with h | h
  · left
    apply e.symm.injective
    simpa using h
  · right
    exact e.symm.injective (h.trans (map_one e.symm).symm)

theorem X'_indecomposable (hL : Indecomposable L) (hq : D.q ≠ 0) :
    Indecomposable D.X' := X_indecomposable (k := k) D.swap hL hq

theorem stable_X'_indecomposable (hL : Indecomposable L) (hq : D.q ≠ 0) :
    Indecomposable ((projectiveStableQuotient (C := C)).obj D.X') :=
  stable_X_indecomposable (k := k) D.swap hL hq

variable [∀ A B : C, FiniteDimensional k (A ⟶ B)]

/-- The Serre-pairing bridge needed by Proposition 7.1, kept explicitly as
actual duality data. Localness and almost-vanishing existence are proved by
the imported Serre-duality component. -/
theorem exists_alpha (R : SerreDuality k (projectiveStableCategory C))
    (hM : Indecomposable M) (hiota : D.iota ≠ 0)
    (hcomm : ∀ a b : End M, a * b = b * a) (hfield : ¬ IsField (End M))
    (e : R.equivalence.functor.obj ((projectiveStableQuotient (C := C)).obj D.X) ≅
      (projectiveStableQuotient (C := C)).obj D.X) :
    ∃ a : End ((projectiveStableQuotient (C := C)).obj D.X),
      IsAlmostVanishing a ∧ ¬ IsIso a := by
  let _ : IsIdempotentComplete (projectiveStableCategory C) :=
    projectiveStableCategory_isIdempotentComplete (k := k)
  let _ : IsMulCommutative (End ((projectiveStableQuotient (C := C)).obj D.X)) :=
    { is_comm := ⟨D.stable_end_commutative (k := k) hcomm⟩ }
  exact AlmostVanishingSerre.exists_noninvertible_almostVanishing_endomorphism R
    (stable_X_indecomposable (k := k) D hM hiota) (D.stable_end_not_isField (k := k) hfield) e

omit k

omit k [Field k] [Linear k C] [∀ A B : C, FiniteDimensional k (A ⟶ B)] in
abbrev firstBoundary (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (projectiveStableQuotient (C := C)).obj D.X' ⟶
      (projectiveStableQuotient (C := C)).obj (Cosyzygy.obj D.X) :=
  D.firstCosyzygyIso.inv ≫ (Cosyzygy.functor (C := C)).map a

omit k [Field k] [Linear k C] [∀ A B : C, FiniteDimensional k (A ⟶ B)] in
abbrev firstSequence (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :=
  HellerClassification.Realization.realizationSequence
    ((projectiveStableQuotient (C := C)).preimage (firstBoundary D a))

omit k [Field k] [Linear k C] [∀ A B : C, FiniteDimensional k (A ⟶ B)] [Projective M] in
theorem first_shortExact (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (firstSequence D a).ShortExact :=
  HellerClassification.Realization.realizationSequence_shortExact _

omit k [Field k] [Linear k C] [∀ A B : C, FiniteDimensional k (A ⟶ B)] in
omit [Projective M] in
theorem first_connecting (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (projectiveStableQuotient (C := C)).map
        (FrobeniusTriangles.connecting (first_shortExact D a)) = firstBoundary D a := by
  rw [HellerClassification.Realization.realization_connecting_stable_eq,
    CategoryTheory.Functor.map_preimage]

omit k [Field k] [Linear k C] [∀ A B : C, FiniteDimensional k (A ⟶ B)] [Projective M] in
theorem firstBoundary_almostVanishing
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : IsAlmostVanishing a) :
    IsAlmostVanishing (firstBoundary D a) :=
  AlmostSplitSequences.almostVanishing_iso_comp
    (ha.map_of_additive_fully_faithful_essSurj (Cosyzygy.functor (C := C)))
    D.firstCosyzygyIso.symm

omit k [Field k] [Linear k C] [∀ A B : C, FiniteDimensional k (A ⟶ B)] [Projective M] in
theorem firstBoundary_not_isIso
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : ¬ IsIso a) :
    ¬ IsIso (firstBoundary D a) := by
  intro h
  let _ := h
  have hm : IsIso ((Cosyzygy.functor (C := C)).map a) := by
    have : IsIso (D.firstCosyzygyIso.hom ≫ firstBoundary D a) := inferInstance
    simpa only [firstBoundary, Category.assoc, Iso.hom_inv_id_assoc] using this
  let _ := hm
  exact ha (isIso_of_reflects_iso a (Cosyzygy.functor (C := C)))

omit [Projective M] in
theorem first_nonsplit
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : IsAlmostVanishing a) :
    ¬ IsSplitEpi (firstSequence D a).g :=
  AlmostSplitSequences.not_splitEpi_of_connecting_ne_zero (first_shortExact D a)
    (by rw [first_connecting]; exact (firstBoundary_almostVanishing D ha).nonzero)

include k in
omit [∀ A B : C, FiniteDimensional k (A ⟶ B)] in
theorem first_middle_indecomposable
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : IsAlmostVanishing a) :
    Indecomposable (firstSequence D a).X₂ :=
  AlmostSplitSequences.middle_indecomposable (first_shortExact D a)
    (X_indecomposable (k := k) D hM hiota) (X'_indecomposable (k := k) D hL hq)
    D.hom_X_X'_zero (first_nonsplit D ha)

omit [Projective M] in
theorem first_middle_not_projective
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : ¬ IsIso a) :
    ¬ Projective (firstSequence D a).X₂ :=
  AlmostSplitSequences.middle_not_projective_of_connecting_not_isIso (first_shortExact D a)
    (by rw [first_connecting]; exact firstBoundary_not_isIso D ha)

abbrev firstTriangle (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :=
  Triangle.mk
    ((projectiveStableQuotient (C := C)).map (firstSequence D a).f)
    ((projectiveStableQuotient (C := C)).map (firstSequence D a).g ≫ D.firstShiftIso.inv)
    (a⟦(1 : ℤ)⟧')

omit [Projective M] in
omit [Projective M] in
theorem first_connecting_shift (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (projectiveStableQuotient (C := C)).map
        (FrobeniusTriangles.connecting (first_shortExact D a)) ≫
        (cosyzygyIsoShift (C := C)).hom.app ((projectiveStableQuotient (C := C)).obj D.X) =
      D.firstShiftIso.inv ≫ a⟦(1 : ℤ)⟧' := by
  rw [first_connecting]
  change (D.firstCosyzygyIso.inv ≫ (Cosyzygy.functor (C := C)).map a) ≫ _ = _
  rw [Category.assoc, (cosyzygyIsoShift (C := C)).hom.naturality]
  simp [PeriodicResolution.Data.firstShiftIso, Category.assoc]

def firstTriangleIso (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    shortExactTriangle (first_shortExact D a) ≅ firstTriangle D a :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) D.firstShiftIso.symm
    (by simp [shortExactTriangle, FrobeniusTriangles.triangle])
    (by simp [shortExactTriangle, FrobeniusTriangles.triangle])
    (by
      change _ ≫ (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact first_connecting_shift D a)

omit [Projective M] in
theorem firstTriangle_distinguished (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    firstTriangle D a ∈ distTriang (projectiveStableCategory C) :=
  isomorphic_distinguished _ (shortExactTriangle_distinguished (first_shortExact D a))
    _ (firstTriangleIso D a).symm

include k in
omit [∀ A B : C, FiniteDimensional k (A ⟶ B)] in
theorem firstTriangle_almostSplit (hM : Indecomposable M) (hiota : D.iota ≠ 0)
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : IsAlmostVanishing a) :
    IsAlmostSplitTriangle (firstTriangle D a) := by
  have hX := stable_X_indecomposable (k := k) D hM hiota
  have hshift := ha.shift_one
  refine ⟨firstTriangle_distinguished D a, hX, indecomposable_shift _ 1 hX,
    hshift.nonzero, ?_⟩
  intro W t ht
  exact (firstTriangle D a).coyoneda_exact₃ (firstTriangle_distinguished D a) t
    (hshift.precomp_eq_zero t ht)

abbrev shiftedFirstTriangle (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :=
  (Triangle.shiftFunctor (projectiveStableCategory C) (1 : ℤ)).obj (firstTriangle D a)

abbrev secondBoundary (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (projectiveStableQuotient (C := C)).obj D.X ⟶
      (projectiveStableQuotient (C := C)).obj (Cosyzygy.obj D.X') :=
  D.doubleShiftIso.inv ≫ (shiftedFirstTriangle D a).mor₃ ≫
    (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map D.firstShiftIso.hom ≫
      (cosyzygyIsoShift (C := C)).inv.app ((projectiveStableQuotient (C := C)).obj D.X')

abbrev secondSequence (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :=
  HellerClassification.Realization.realizationSequence
    ((projectiveStableQuotient (C := C)).preimage (secondBoundary D a))

theorem second_shortExact (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (secondSequence D a).ShortExact :=
  HellerClassification.Realization.realizationSequence_shortExact _

theorem second_connecting (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (projectiveStableQuotient (C := C)).map
        (FrobeniusTriangles.connecting (second_shortExact D a)) = secondBoundary D a := by
  rw [HellerClassification.Realization.realization_connecting_stable_eq,
    CategoryTheory.Functor.map_preimage]

theorem second_connecting_shift (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (projectiveStableQuotient (C := C)).map
        (FrobeniusTriangles.connecting (second_shortExact D a)) ≫
        (cosyzygyIsoShift (C := C)).hom.app ((projectiveStableQuotient (C := C)).obj D.X') =
      D.doubleShiftIso.inv ≫ (shiftedFirstTriangle D a).mor₃ ≫
        (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map D.firstShiftIso.hom := by
  rw [second_connecting]
  simp only [secondBoundary, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The second ambient realization is compared to the actual shift of the
first triangle by two genuine endpoint isomorphisms. -/
def shiftedFirstTriangleIso (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    shiftedFirstTriangle D a ≅ shortExactTriangle (second_shortExact D a) :=
  isoTriangleOfIso₁₃ _ _ ((firstTriangle D a).shift_distinguished (firstTriangle_distinguished D a) 1)
    (shortExactTriangle_distinguished (second_shortExact D a))
    D.firstShiftIso D.doubleShiftIso (by
      change _ = D.doubleShiftIso.hom ≫
        ((projectiveStableQuotient (C := C)).map
          (FrobeniusTriangles.connecting (second_shortExact D a)) ≫
          (cosyzygyIsoShift (C := C)).hom.app
            ((projectiveStableQuotient (C := C)).obj D.X'))
      rw [second_connecting_shift]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp])

def middleShiftIso (a : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (projectiveStableQuotient (C := C)).obj (secondSequence D a).X₂ ≅
      ((projectiveStableQuotient (C := C)).obj (firstSequence D a).X₂)⟦(1 : ℤ)⟧ :=
  (Triangle.π₂.mapIso (shiftedFirstTriangleIso D a)).symm

omit [Projective M] in
theorem shiftedFirst_mor₃_ne_zero
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : IsAlmostVanishing a) :
    (shiftedFirstTriangle D a).mor₃ ≠ 0 := by
  intro h
  have h' := congrArg (fun f => f ≫
    (shiftFunctorComm (projectiveStableCategory C) (1 : ℤ) 1).inv.app
      ((projectiveStableQuotient (C := C)).obj D.X)) h
  have hz : a⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' = 0 := by
    simpa [shiftedFirstTriangle, firstTriangle, Triangle.shiftFunctor, Category.assoc] using h'
  apply ha.nonzero
  apply (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map_injective
  apply (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map_injective
  simpa using hz

theorem second_nonsplit
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : IsAlmostVanishing a) :
    ¬ IsSplitEpi (secondSequence D a).g := by
  apply AlmostSplitSequences.not_splitEpi_of_connecting_ne_zero (second_shortExact D a)
  intro h
  have hz : D.doubleShiftIso.inv ≫ (shiftedFirstTriangle D a).mor₃ ≫
      (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map D.firstShiftIso.hom = 0 := by
    rw [← second_connecting_shift, h, zero_comp]
  apply shiftedFirst_mor₃_ne_zero D ha
  apply (cancel_mono
    ((shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map D.firstShiftIso.hom)).mp
  apply (cancel_epi D.doubleShiftIso.inv).mp
  simpa [Category.assoc] using hz

include k in
omit [∀ A B : C, FiniteDimensional k (A ⟶ B)] in
theorem second_middle_indecomposable
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : IsAlmostVanishing a) :
    Indecomposable (secondSequence D a).X₂ :=
  AlmostSplitSequences.middle_indecomposable (second_shortExact D a)
    (X'_indecomposable (k := k) D hL hq) (X_indecomposable (k := k) D hM hiota)
    D.hom_X'_X_zero (second_nonsplit D ha)

include k in
/-- The first represented Hom has the full endpoint dimension, whereas
the nonsplit reversed sequence has strictly smaller dimension. This is
the actual ambient nonisomorphism argument of Proposition 7.1, Step 3. -/
theorem ambient_middle_not_iso
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : IsAlmostVanishing a) :
    ¬ Nonempty ((firstSequence D a).X₂ ≅ (secondSequence D a).X₂) := by
  rintro ⟨e⟩
  have hfirst := (AlmostSplitSequences.homLeftLinearEquiv (k := k)
    (first_shortExact D a) D.X D.hom_X_X'_zero).finrank_eq
  have hsecond := AlmostSplitSequences.finrank_hom_middle_lt_end_right (k := k)
    (second_shortExact D a) D.hom_X_X'_zero (second_nonsplit D ha)
  have he := (Linear.homCongr k (Iso.refl D.X) e).finrank_eq
  change Module.finrank k (D.X ⟶ D.X) =
    Module.finrank k (D.X ⟶ (firstSequence D a).X₂) at hfirst
  change Module.finrank k (D.X ⟶ (secondSequence D a).X₂) <
    Module.finrank k (D.X ⟶ D.X) at hsecond
  omega

omit [Projective M] in
theorem stable_first_middle_not_isZero
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : ¬ IsIso a) :
    ¬ IsZero ((projectiveStableQuotient (C := C)).obj (firstSequence D a).X₂) := by
  intro h
  have hi := ((firstTriangle D a).isZero₂_iff_isIso₃
    (firstTriangle_distinguished D a)).mp h
  change IsIso ((shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map a) at hi
  let _ := hi
  exact ha (isIso_of_reflects_iso a (shiftFunctor (projectiveStableCategory C) (1 : ℤ)))

theorem second_middle_not_projective
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)} (ha : ¬ IsIso a) :
    ¬ Projective (secondSequence D a).X₂ := by
  intro h
  let _ := h
  have hz := IsZero.of_iso (isZero_projectiveStableQuotient_obj (secondSequence D a).X₂)
    (middleShiftIso D a).symm
  apply stable_first_middle_not_isZero D ha
  exact IsZero.of_iso ((shiftFunctor (projectiveStableCategory C) (-1 : ℤ)).map_isZero hz)
    (shiftShiftNeg ((projectiveStableQuotient (C := C)).obj (firstSequence D a).X₂) 1).symm

include k in
omit [FrobeniusAbelian C] in
/-- An ambient indecomposable with nonzero stable image remains
indecomposable in the actual quotient. Idempotents are lifted using the
proved finite-dimensional lifting theorem. -/
theorem stable_indecomposable_of_ambient {A : C} (hA : Indecomposable A)
    (hzero : ¬ IsZero ((projectiveStableQuotient (C := C)).obj A)) :
    Indecomposable ((projectiveStableQuotient (C := C)).obj A) := by
  apply AlmostSplitSequences.indecomposable_of_idempotents_trivial hzero
  intro e he
  let _ : ∀ A : C, FiniteDimensional k (End A) :=
    fun A => inferInstanceAs (FiniteDimensional k (A ⟶ A))
  obtain ⟨p, hp, hpe⟩ := (projectiveStableQuotient (C := C)).exists_idempotent_preimage
    (k := k) A e he
  rcases AlmostVanishingSerre.idempotent_eq_zero_or_one hA p hp with hp | hp
  · left
    rw [← hpe, hp, CategoryTheory.Functor.map_zero]
  · right
    rw [← hpe, hp, End.one_def, CategoryTheory.Functor.map_id]
    rfl

include k in
theorem stable_first_middle_indecomposable
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)}
    (ha : IsAlmostVanishing a) (hai : ¬ IsIso a) :
    Indecomposable ((projectiveStableQuotient (C := C)).obj (firstSequence D a).X₂) :=
  stable_indecomposable_of_ambient (k := k)
    (first_middle_indecomposable (k := k) D hM hL hiota hq ha)
    (stable_first_middle_not_isZero D hai)

include k in
/-- The actual G3 middle object is not isomorphic to its suspension. The
reflection from stable to ambient isomorphisms is proved independently
for Hom-finite indecomposable nonprojective objects. -/
theorem first_middle_not_periodic
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    {a : End ((projectiveStableQuotient (C := C)).obj D.X)}
    (ha : IsAlmostVanishing a) (hai : ¬ IsIso a) :
    ¬ Nonempty ((projectiveStableQuotient (C := C)).obj (firstSequence D a).X₂ ≅
      ((projectiveStableQuotient (C := C)).obj (firstSequence D a).X₂)⟦(1 : ℤ)⟧) := by
  rintro ⟨e⟩
  apply ambient_middle_not_iso (k := k) D ha
  exact nonempty_iso_of_stable_iso (k := k)
    (first_middle_indecomposable (k := k) D hM hL hiota hq ha)
    (second_middle_indecomposable (k := k) D hM hL hiota hq ha)
    (first_middle_not_projective D hai) (second_middle_not_projective D hai)
    (e ≪≫ (middleShiftIso D a).symm)

include k in
/-- Genuine gemstone assembly from an almost-vanishing endomorphism.
The endomorphism can subsequently be supplied by the actual Serre pairing
through `exists_gemstone`; G3 is proved from the ambient constructions. -/
def gemstoneOfAlpha
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    (hcomm : ∀ a b : End M, a * b = b * a)
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧ PeriodicResolution.restrictM c = a)
    (a : End ((projectiveStableQuotient (C := C)).obj D.X))
    (ha : IsAlmostVanishing a) (hai : ¬ IsIso a) :
    Gemstone ((projectiveStableQuotient (C := C)).obj D.X) where
  indecomposable := stable_X_indecomposable (k := k) D hM hiota
  periodicity := D.periodicity
  rigid := D.stable_hom_X_shift_one_zero
  alpha := a
  almostVanishing := ha
  not_isIso := hai
  central f := D.stable_end_commutative (k := k) hcomm f a
  compatible := D.periodicity_compatible hcentral a
  middle := (projectiveStableQuotient (C := C)).obj (firstSequence D a).X₂
  first := (projectiveStableQuotient (C := C)).map (firstSequence D a).f
  second := (projectiveStableQuotient (C := C)).map (firstSequence D a).g ≫ D.firstShiftIso.inv
  almostSplit := firstTriangle_almostSplit (k := k) D hM hiota ha
  middle_not_periodic := first_middle_not_periodic (k := k) D hM hL hiota hq ha hai

/-- Every even actual integer shift fixes the periodic stable object. -/
def evenShiftNatIso : (n : ℕ) →
    ((projectiveStableQuotient (C := C)).obj D.X)⟦(2 : ℤ) * n⟧ ≅
      (projectiveStableQuotient (C := C)).obj D.X
  | 0 => (shiftFunctorZero (projectiveStableCategory C) ℤ).app _
  | n + 1 =>
    (shiftFunctorAdd' (projectiveStableCategory C) ((2 : ℤ) * n) 2
      ((2 : ℤ) * (n + 1 : ℕ)) (by omega)).app _ ≪≫
      (shiftFunctor (projectiveStableCategory C) (2 : ℤ)).mapIso (evenShiftNatIso n) ≪≫
        D.shiftTwoIso

def evenShiftIso (n : ℤ) :
    ((projectiveStableQuotient (C := C)).obj D.X)⟦(2 : ℤ) * n⟧ ≅
      (projectiveStableQuotient (C := C)).obj D.X := by
  cases n with
  | ofNat n => exact evenShiftNatIso D n
  | negSucc n =>
    rw [show (2 : ℤ) * Int.negSucc n = -((2 : ℤ) * (n + 1 : ℕ)) by omega]
    exact (shiftFunctor (projectiveStableCategory C) (-((2 : ℤ) * (n + 1 : ℕ)))).mapIso
        (evenShiftNatIso D (n + 1)).symm ≪≫
      (shiftFunctorCompIsoId (projectiveStableCategory C)
        ((2 : ℤ) * (n + 1 : ℕ)) (-((2 : ℤ) * (n + 1 : ℕ))) (by omega)).app _

include k in
/-- Proposition 7.1 as a component with explicit actual stable Serre
duality data and its periodic-object comparison. These are mathematical
intermediate inputs, not assumptions of almost-vanishing or gemstone
existence. The paper-specific Calabi–Yau-to-Serre bridge remains external
to this component. -/
theorem exists_gemstone (R : SerreDuality k (projectiveStableCategory C))
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    (hcomm : ∀ a b : End M, a * b = b * a) (hfield : ¬ IsField (End M))
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧ PeriodicResolution.restrictM c = a)
    (e : R.equivalence.functor.obj ((projectiveStableQuotient (C := C)).obj D.X) ≅
      (projectiveStableQuotient (C := C)).obj D.X) :
    Nonempty (Gemstone ((projectiveStableQuotient (C := C)).obj D.X)) := by
  obtain ⟨a, ha, hai⟩ := exists_alpha (k := k) D R hM hiota hcomm hfield e
  exact ⟨gemstoneOfAlpha (k := k) D hM hL hiota hq hcomm hcentral a ha hai⟩

include k in
/-- The odd Calabi–Yau exponent enters through a genuine natural
identification of the Serre functor with the canonical shift by `3d−1`.
The required fixed-object isomorphism is derived from even periodicity. -/
theorem exists_gemstone_of_odd_serre_shift
    (R : SerreDuality k (projectiveStableCategory C))
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    (hcomm : ∀ a b : End M, a * b = b * a) (hfield : ¬ IsField (End M))
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧ PeriodicResolution.restrictM c = a)
    (d : ℤ) (hd : Odd d)
    (e : R.equivalence.functor ≅ shiftFunctor (projectiveStableCategory C) (3 * d - 1)) :
    Nonempty (Gemstone ((projectiveStableQuotient (C := C)).obj D.X)) := by
  obtain ⟨n, hn⟩ := hd
  have heven : 3 * d - 1 = (2 : ℤ) * (3 * n + 1) := by omega
  let eX : R.equivalence.functor.obj ((projectiveStableQuotient (C := C)).obj D.X) ≅
      (projectiveStableQuotient (C := C)).obj D.X :=
    e.app _ ≪≫ (by rw [heven]; exact evenShiftIso D (3 * n + 1))
  exact exists_gemstone (k := k) D R hM hL hiota hq hcomm hfield hcentral eX

include k in
/-- A raw projective-projective Serre pairing constructs the stable Serre
data internally before the gemstone argument. The remaining functor
identification is the separate Calabi–Yau shift adapter. -/
theorem exists_gemstone_of_projective_serre_odd_shift
    (S : C ≌ C) [S.functor.Additive] [Functor.Linear k S.functor]
    (P : ProjectiveSerreDuality k C S.functor)
    (hM : Indecomposable M) (hL : Indecomposable L) (hiota : D.iota ≠ 0) (hq : D.q ≠ 0)
    (hcomm : ∀ a b : End M, a * b = b * a) (hfield : ¬ IsField (End M))
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧ PeriodicResolution.restrictM c = a)
    (d : ℤ) (hd : Odd d)
    (e : stableFunctor S.functor ⋙ (Cosyzygy.equivalence (C := C)).inverse ≅
      shiftFunctor (projectiveStableCategory C) (3 * d - 1)) :
    Nonempty (Gemstone ((projectiveStableQuotient (C := C)).obj D.X)) :=
  exists_gemstone_of_odd_serre_shift (k := k) D (StableSerreDuality.serreDuality S P)
    hM hL hiota hq hcomm hfield hcentral d hd
    (StableSerreDuality.serreIsoOmega S P ≪≫ e)

end PretriangulatedV2.StableCategory.PeriodicGemstone
