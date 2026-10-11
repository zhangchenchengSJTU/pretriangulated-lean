import PretriangulatedV2.AlmostVanishingSerre
import PretriangulatedV2.FrobeniusTriangulation
import PretriangulatedV2.HomDimensions

/-!
Elementary ambient abelian results used by Proposition 7.1, Step 3.
The middle-object indecomposability proof uses idempotents on a genuine
short exact sequence. No existence of almost-split sequences is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2.AlmostSplitSequences

universe v u w

variable {C : Type u} [Category.{v} C]

section

variable [Preadditive C] [HasBinaryBiproducts C]

/-- A nonzero object with only trivial idempotent endomorphisms is
indecomposable, as witnessed by the projections of each biproduct. -/
theorem indecomposable_of_idempotents_trivial {X : C} (hX : ¬ IsZero X)
    (he : ∀ e : End X, IsIdempotentElem e → e = 0 ∨ e = 1) : Indecomposable X := by
  refine ⟨hX, ?_⟩
  intro A B e
  let p : End X := e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : IsIdempotentElem p := by
    change p ≫ p = p
    simp [p, Category.assoc]
  rcases he p hp with hp | hp
  · left
    apply (IsZero.iff_id_eq_zero A).mpr
    have h := congrArg (fun t => biprod.inl ≫ e.inv ≫ t ≫ e.hom ≫ biprod.fst) hp
    simpa [p, Category.assoc] using h
  · right
    apply (IsZero.iff_id_eq_zero B).mpr
    have h := congrArg (fun t => biprod.inr ≫ e.inv ≫ t ≫ e.hom ≫ biprod.snd) hp
    simpa [p, Category.assoc] using h.symm

omit [HasBinaryBiproducts C] in
/-- Precomposing an almost-vanishing map by an actual isomorphism preserves
the two annihilation properties. -/
theorem almostVanishing_iso_comp {A B W : C} {a : A ⟶ B}
    (ha : IsAlmostVanishing a) (e : W ≅ A) : IsAlmostVanishing (e.hom ≫ a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply ha.nonzero
    apply (cancel_epi e.hom).mp
    simpa using h
  · intro Y s hs
    rw [Category.assoc, ha.postcomp_eq_zero s hs, comp_zero]
  · intro Y t ht
    have ht' : ¬ IsSplitEpi (t ≫ e.hom) := by
      intro h
      let _ := h
      have : IsSplitEpi ((t ≫ e.hom) ≫ e.inv) := inferInstance
      apply ht
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
    rw [← Category.assoc, ha.precomp_eq_zero (t ≫ e.hom) ht']

end

variable [Abelian C] [HasBinaryBiproducts C] {S : ShortComplex C} (hS : S.ShortExact)

/-- The first endpoint action of an actual middle endomorphism. -/
abbrev leftAction (hvanish : ∀ f : S.X₁ ⟶ S.X₃, f = 0) (e : End S.X₂) : End S.X₁ :=
  (KernelFork.IsLimit.lift' hS.fIsKernel (S.f ≫ e)
    (by simpa only [Category.assoc] using hvanish (S.f ≫ e ≫ S.g))).val

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem leftAction_f (hvanish : ∀ f : S.X₁ ⟶ S.X₃, f = 0) (e : End S.X₂) :
    leftAction hS hvanish e ≫ S.f = S.f ≫ e :=
  (KernelFork.IsLimit.lift' hS.fIsKernel (S.f ≫ e)
    (by simpa only [Category.assoc] using hvanish (S.f ≫ e ≫ S.g))).property

/-- The right endpoint action is genuine descent through the cokernel. -/
abbrev rightAction (hvanish : ∀ f : S.X₁ ⟶ S.X₃, f = 0) (e : End S.X₂) : End S.X₃ :=
  (CokernelCofork.IsColimit.desc' hS.gIsCokernel (e ≫ S.g)
    (hvanish (S.f ≫ e ≫ S.g))).val

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem g_rightAction (hvanish : ∀ f : S.X₁ ⟶ S.X₃, f = 0) (e : End S.X₂) :
    S.g ≫ rightAction hS hvanish e = e ≫ S.g :=
  (CokernelCofork.IsColimit.desc' hS.gIsCokernel (e ≫ S.g)
    (hvanish (S.f ≫ e ≫ S.g))).property

omit [HasBinaryBiproducts C] in
theorem leftAction_idempotent (hvanish : ∀ f : S.X₁ ⟶ S.X₃, f = 0)
    (e : End S.X₂) (he : IsIdempotentElem e) :
    IsIdempotentElem (leftAction hS hvanish e) := by
  let _ := hS.mono_f
  change leftAction hS hvanish e ≫ leftAction hS hvanish e = leftAction hS hvanish e
  apply (cancel_mono S.f).mp
  simp only [Category.assoc, leftAction_f, leftAction_f_assoc]
  rw [show e ≫ e = e from he]

omit [HasBinaryBiproducts C] in
theorem rightAction_idempotent (hvanish : ∀ f : S.X₁ ⟶ S.X₃, f = 0)
    (e : End S.X₂) (he : IsIdempotentElem e) :
    IsIdempotentElem (rightAction hS hvanish e) := by
  let _ := hS.epi_g
  change rightAction hS hvanish e ≫ rightAction hS hvanish e = rightAction hS hvanish e
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, g_rightAction, Category.assoc, g_rightAction,
    ← Category.assoc, show e ≫ e = e from he]

include hS

omit [HasBinaryBiproducts C] in
/-- An idempotent middle endomorphism trivial on both endpoints is zero. -/
theorem end_eq_zero_of_boundary_zero (e : End S.X₂) (he : IsIdempotentElem e)
    (hf : S.f ≫ e = 0) (hg : e ≫ S.g = 0) : e = 0 := by
  obtain ⟨r, hr⟩ := KernelFork.IsLimit.lift' hS.fIsKernel e hg
  change r ≫ S.f = e at hr
  calc
    e = e ≫ e := he.symm
    _ = (r ≫ S.f) ≫ e := by rw [hr]
    _ = 0 := by rw [Category.assoc, hf, comp_zero]

omit [HasBinaryBiproducts C] in
/-- An endomorphism acting by zero at the left and identity at the right
produces an actual section of the short exact sequence. -/
theorem splitEpi_of_mixed_boundary (e : End S.X₂)
    (hf : S.f ≫ e = 0) (hg : e ≫ S.g = S.g) : IsSplitEpi S.g := by
  let _ := hS.epi_g
  obtain ⟨t, ht⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel e hf
  change S.g ≫ t = e at ht
  refine IsSplitEpi.mk' ⟨t, ?_⟩
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, ht, hg, Category.comp_id]

/-- The elementary indecomposability argument in Proposition 7.1, Step 3:
orthogonal indecomposable endpoints and a nonsplit actual short exact
sequence have indecomposable middle object. -/
theorem middle_indecomposable [IsIdempotentComplete C]
    (hA : Indecomposable S.X₁) (hB : Indecomposable S.X₃)
    (hvanish : ∀ f : S.X₁ ⟶ S.X₃, f = 0) (hnot : ¬ IsSplitEpi S.g) :
    Indecomposable S.X₂ := by
  let _ := hS.mono_f
  let _ := hS.epi_g
  apply indecomposable_of_idempotents_trivial
  · intro h
    apply hA.1
    apply (IsZero.iff_id_eq_zero S.X₁).mpr
    apply (cancel_mono S.f).mp
    rw [Category.id_comp, zero_comp]
    exact h.eq_zero_of_tgt S.f
  · intro e he
    have he' : IsIdempotentElem ((1 : End S.X₂) - e) := he.one_sub
    rcases AlmostVanishingSerre.idempotent_eq_zero_or_one hA
      (leftAction hS hvanish e) (leftAction_idempotent hS hvanish e he) with hleft | hleft <;>
      rcases AlmostVanishingSerre.idempotent_eq_zero_or_one hB
        (rightAction hS hvanish e) (rightAction_idempotent hS hvanish e he) with hright | hright
    · left
      apply end_eq_zero_of_boundary_zero hS e he
      · rw [← leftAction_f hS hvanish e, hleft, zero_comp]
      · rw [← g_rightAction hS hvanish e, hright, comp_zero]
    · exact False.elim (hnot (splitEpi_of_mixed_boundary hS e
        (by rw [← leftAction_f hS hvanish e, hleft, zero_comp])
        (by rw [← g_rightAction hS hvanish e, hright, End.one_def, Category.comp_id])))
    · apply False.elim
      apply hnot
      apply splitEpi_of_mixed_boundary hS ((1 : End S.X₂) - e)
      · rw [comp_sub, End.one_def, Category.comp_id, ← leftAction_f hS hvanish e, hleft]
        simp
      · rw [sub_comp, End.one_def, Category.id_comp, ← g_rightAction hS hvanish e, hright]
        simp
    · right
      have hz : (1 : End S.X₂) - e = 0 := by
        apply end_eq_zero_of_boundary_zero hS ((1 : End S.X₂) - e) he'
        · rw [comp_sub, End.one_def, Category.comp_id, ← leftAction_f hS hvanish e, hleft]
          simp
        · rw [sub_comp, End.one_def, Category.id_comp, ← g_rightAction hS hvanish e, hright]
          simp
      exact (sub_eq_zero.mp hz).symm

variable {k : Type w} [Field k] [Linear k C]

/-- Applying a represented Hom to an actual short exact sequence with
vanishing right endpoint yields an actual linear equivalence. -/
def homLeftLinearEquiv (W : C) (hvanish : ∀ f : W ⟶ S.X₃, f = 0) :
    (W ⟶ S.X₁) ≃ₗ[k] (W ⟶ S.X₂) :=
  LinearEquiv.ofBijective (Linear.rightComp k W S.f) (by
    let _ := hS.mono_f
    constructor
    · intro a b hab
      exact (cancel_mono S.f).mp hab
    · intro a
      obtain ⟨b, hb⟩ := KernelFork.IsLimit.lift' hS.fIsKernel a (hvanish (a ≫ S.g))
      exact ⟨b, hb⟩)

omit [HasBinaryBiproducts C] in
/-- The strict ambient dimension inequality used to distinguish the two
middle objects in Proposition 7.1. -/
theorem finrank_hom_middle_lt_end_right
    (hvanish : ∀ f : S.X₃ ⟶ S.X₁, f = 0) (hnot : ¬ IsSplitEpi S.g)
    [FiniteDimensional k (S.X₃ ⟶ S.X₂)] [FiniteDimensional k (S.X₃ ⟶ S.X₃)] :
    Module.finrank k (S.X₃ ⟶ S.X₂) < Module.finrank k (S.X₃ ⟶ S.X₃) := by
  let t := Linear.rightComp k S.X₃ S.g
  have hinj : Function.Injective t := by
    intro a b hab
    have hz : (a - b) ≫ S.g = 0 := by
      rw [sub_comp]
      exact sub_eq_zero.mpr hab
    obtain ⟨r, hr⟩ := KernelFork.IsLimit.lift' hS.fIsKernel (a - b) hz
    change r ≫ S.f = a - b at hr
    rw [hvanish r, zero_comp] at hr
    exact sub_eq_zero.mp hr.symm
  have hnot_surj : ¬ Function.Surjective t := by
    intro h
    obtain ⟨r, hr⟩ := h (𝟙 S.X₃)
    exact hnot (IsSplitEpi.mk' ⟨r, hr⟩)
  have hrange : LinearMap.range t < ⊤ :=
    lt_of_le_of_ne le_top (fun h => hnot_surj (LinearMap.range_eq_top.mp h))
  have h := Submodule.finrank_lt_finrank_of_lt hrange
  rw [LinearMap.finrank_range_of_inj hinj, finrank_top] at h
  exact h

variable [FrobeniusAbelian C]

omit k [Field k] [Linear k C] in
/-- A nonzero stable connecting morphism prevents the ambient sequence
from splitting. -/
theorem not_splitEpi_of_connecting_ne_zero
    (hδ : (StableCategory.projectiveStableQuotient (C := C)).map
      (StableCategory.FrobeniusTriangles.connecting hS) ≠ 0) : ¬ IsSplitEpi S.g := by
  intro h
  let _ := h
  let Q := StableCategory.projectiveStableQuotient (C := C)
  let T := StableCategory.shortExactTriangle hS
  have hT := StableCategory.shortExactTriangle_distinguished hS
  have hg : Epi (Q.map S.g) := inferInstance
  have hz : Q.map S.g ≫
      (Q.map (StableCategory.FrobeniusTriangles.connecting hS) ≫
        (StableCategory.cosyzygyIsoShift (C := C)).hom.app (Q.obj S.X₁)) = 0 :=
    comp_distTriang_mor_zero₂₃ T hT
  have hz' : Q.map (StableCategory.FrobeniusTriangles.connecting hS) ≫
      (StableCategory.cosyzygyIsoShift (C := C)).hom.app (Q.obj S.X₁) = 0 :=
    (cancel_epi (Q.map S.g)).mp (by simpa using hz)
  exact hδ ((cancel_mono
    ((StableCategory.cosyzygyIsoShift (C := C)).hom.app (Q.obj S.X₁))).mp
      (by simpa using hz'))

omit k [Field k] [Linear k C] in
/-- Noninvertibility of the actual stable connecting morphism forces the
ambient middle object to be nonprojective. -/
theorem middle_not_projective_of_connecting_not_isIso
    (hδ : ¬ IsIso ((StableCategory.projectiveStableQuotient (C := C)).map
      (StableCategory.FrobeniusTriangles.connecting hS))) : ¬ Projective S.X₂ := by
  intro h
  let _ := h
  let Q := StableCategory.projectiveStableQuotient (C := C)
  let T := StableCategory.shortExactTriangle hS
  have hT := StableCategory.shortExactTriangle_distinguished hS
  have hi : IsIso T.mor₃ := (T.isZero₂_iff_isIso₃ hT).mp
    (StableCategory.isZero_projectiveStableQuotient_obj S.X₂)
  change IsIso (Q.map (StableCategory.FrobeniusTriangles.connecting hS) ≫
    (StableCategory.cosyzygyIsoShift (C := C)).hom.app (Q.obj S.X₁)) at hi
  let _ := hi
  apply hδ
  have he : Q.map (StableCategory.FrobeniusTriangles.connecting hS) =
      (Q.map (StableCategory.FrobeniusTriangles.connecting hS) ≫
        (StableCategory.cosyzygyIsoShift (C := C)).hom.app (Q.obj S.X₁)) ≫
        (StableCategory.cosyzygyIsoShift (C := C)).inv.app (Q.obj S.X₁) := by
    rw [Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [he]
  infer_instance

end PretriangulatedV2.AlmostSplitSequences
