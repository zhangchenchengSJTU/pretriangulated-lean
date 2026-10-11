import PretriangulatedV2.CoherentLinear
import PretriangulatedV2.PeriodicResolution
import PretriangulatedV2.AlmostVanishingSerre
import Mathlib.CategoryTheory.Conj

/-!
Actual alternating exact projective data in mod(D), induced by a distinguished
periodic triangle in D. Exactness is proved through the genuine Yoneda Hom
sequence and actual coherent-presheaf kernels and cokernels.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2.YonedaPeriodicData

universe w v u

variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

abbrev Y : D ⥤ CoherentFunctors.Mod D := CoherentFunctors.yoneda

/-- Yoneda turns an actual Hom exactness statement into exactness in the
actual abelian coherent-functor category. -/
theorem yoneda_exact {A B C : D} (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0)
    (hlift : ∀ (W : D) (a : W ⟶ B), a ≫ g = 0 → ∃ b : W ⟶ A, b ≫ f = a) :
    (ShortComplex.mk (Y.map f) (Y.map g) (by rw [← Functor.map_comp, hfg, Functor.map_zero])).Exact := by
  have : (CoherentFunctors.coherent D).ι.PreservesHomology :=
    { preservesKernels := (CoherentFunctors.coherent D).preservesKernels_ι
      preservesCokernels := (CoherentFunctors.coherent D).preservesCokernels_ι }
  apply (ShortComplex.exact_map_iff_of_faithful
    (ShortComplex.mk (Y.map f) (Y.map g) (by rw [← Functor.map_comp, hfg, Functor.map_zero]))
    (CoherentFunctors.coherent D).ι).mp
  change (ShortComplex.mk (preadditiveYoneda.map f) (preadditiveYoneda.map g) _).Exact
  apply CoherentFunctors.exact_of_pointwise
  intro W a ha
  change a ≫ g = 0 at ha
  exact hlift W.unop a ha

variable {L M : D} (i : L ⟶ M) (q : M ⟶ L) (e : M ≅ L⟦(1 : ℤ)⟧)
  (hT : Triangle.mk i q (-i ≫ e.hom) ∈ distTriang D)

include hT in
omit [HasBinaryBiproducts D] in
theorem i_q_zero : i ≫ q = 0 := comp_distTriang_mor_zero₁₂ _ hT

include hT in
omit [HasBinaryBiproducts D] in
theorem q_i_zero : q ≫ i = 0 := by
  apply (cancel_mono e.hom).mp
  simpa only [Triangle.mk_mor₂, Triangle.mk_mor₃, Category.assoc,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_eq_zero, zero_comp] using
    (comp_distTriang_mor_zero₂₃ _ hT)

/-- Both positions of the alternating Yoneda sequence are genuinely exact. -/
def data
    (hi : ∀ a : M ⟶ L, a ≫ i = 0)
    (hq : ∀ a : L ⟶ M, a ≫ q = 0) :
    StableCategory.PeriodicResolution.Data (Y.obj M) (Y.obj L) where
  iota := Y.map i
  q := Y.map q
  iota_q := by rw [← Functor.map_comp, i_q_zero i q e hT, Functor.map_zero]
  q_iota := by rw [← Functor.map_comp, q_i_zero i q e hT, Functor.map_zero]
  exact_iota_q := yoneda_exact i q (i_q_zero i q e hT) (by
    intro W a ha
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ _ hT a ha
    exact ⟨b, hb.symm⟩)
  exact_q_iota := yoneda_exact q i (q_i_zero i q e hT) (by
    intro W a ha
    have hh : a ≫ (-i ≫ e.hom) = 0 := by simp [← Category.assoc, ha]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃ _ hT a hh
    exact ⟨b, hb.symm⟩)
  annihilate_iota := by
    intro a
    obtain ⟨a, rfl⟩ := Y.map_surjective a
    rw [← Functor.map_comp, hi, Functor.map_zero]
  annihilate_q := by
    intro a
    obtain ⟨a, rfl⟩ := Y.map_surjective a
    rw [← Functor.map_comp, hq, Functor.map_zero]

@[simp] theorem data_iota
    (hi : ∀ a : M ⟶ L, a ≫ i = 0) (hq : ∀ a : L ⟶ M, a ≫ q = 0) :
    (data i q e hT hi hq).iota = Y.map i := rfl

@[simp] theorem data_q
    (hi : ∀ a : M ⟶ L, a ≫ i = 0) (hq : ∀ a : L ⟶ M, a ≫ q = 0) :
    (data i q e hT hi hq).q = Y.map q := rfl

omit [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
theorem yoneda_map_ne_zero {A B : D} (f : A ⟶ B) (hf : f ≠ 0) : Y.map f ≠ 0 := by
  intro h
  apply hf
  apply Y.map_injective
  simpa only [Functor.map_zero] using h

omit [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- The two terms of the periodic data are actual projective representables. -/
theorem yoneda_projective (A : D) : Projective (Y.obj A) := inferInstance

variable {k : Type w} [Field k] [Linear k D]

/-- The actual Yoneda identification of endomorphism rings. -/
def endRingEquiv (A : D) : End A ≃+* End (Y.obj A) :=
  { Functor.FullyFaithful.mulEquivEnd (Functor.FullyFaithful.ofFullyFaithful Y) A with
    map_add' := fun _ _ => Y.map_add }

/-- Full faithfulness and the actual linear Yoneda action identify the
endomorphism algebras, without any quotient of endomorphisms. -/
def endAlgEquiv (A : D) : End A ≃ₐ[k] End (Y.obj A) :=
  { endRingEquiv A with
    commutes' := fun r => by
      change Y.map (r • 𝟙 A) = r • 𝟙 (Y.obj A)
      simp }

omit [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
@[simp] theorem endAlgEquiv_apply (A : D) (a : End A) :
    endAlgEquiv (k := k) A a = Y.map a := rfl

include k in
omit [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
theorem end_commutative (A : D) (hcomm : ∀ a b : End A, a * b = b * a)
    (a b : End (Y.obj A)) : a * b = b * a := by
  obtain ⟨a, rfl⟩ := (endAlgEquiv (k := k) A).surjective a
  obtain ⟨b, rfl⟩ := (endAlgEquiv (k := k) A).surjective b
  rw [← map_mul, hcomm a b, map_mul]

include k in
omit [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
theorem end_not_isField (A : D) (hnot : ¬ IsField (End A)) :
    ¬ IsField (End (Y.obj A)) := by
  intro hf
  let E := endAlgEquiv (k := k) A
  apply hnot
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hf.exists_pair_ne
    exact ⟨E.symm a, E.symm b, fun h => hab (E.symm.injective h)⟩
  · intro a b
    apply E.injective
    simpa only [map_mul] using hf.mul_comm (E a) (E b)
  · intro a ha
    have hea : E a ≠ 0 := by
      intro h
      exact ha (E.injective (by simpa using h))
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel hea
    refine ⟨E.symm b, E.injective ?_⟩
    simpa only [map_mul, AlgEquiv.apply_symm_apply, map_one] using hb

/-- Every summand of a projective representable is projective and hence,
because idempotents in D split, representable. Full faithfulness then reflects
the resulting decomposition back to D. -/
theorem yoneda_indecomposable [IsIdempotentComplete D] (A : D)
    (hA : Indecomposable A) : Indecomposable (Y.obj A) := by
  let : PreservesBinaryBiproducts (Y (D := D)) :=
    preservesBinaryBiproducts_of_preservesBiproducts (Y (D := D))
  constructor
  · intro hzero
    apply hA.1
    apply (IsZero.iff_id_eq_zero A).mpr
    apply Y.map_injective
    simpa using (IsZero.iff_id_eq_zero (Y.obj A)).mp hzero
  · intro B C e
    let : Projective (B ⊞ C) := Projective.of_iso e inferInstance
    let rB : Retract B (B ⊞ C) := { i := biprod.inl, r := biprod.fst }
    let rC : Retract C (B ⊞ C) := { i := biprod.inr, r := biprod.snd }
    let : Projective B := rB.projective
    let : Projective C := rC.projective
    obtain ⟨B', ⟨eB⟩⟩ := (CoherentFunctors.projective_iff_representable B).mp inferInstance
    obtain ⟨C', ⟨eC⟩⟩ := (CoherentFunctors.projective_iff_representable C).mp inferInstance
    let e' : Y.obj A ≅ Y.obj (B' ⊞ C') :=
      e ≪≫ biprod.mapIso eB eC ≪≫ (Y.mapBiprod B' C').symm
    rcases hA.2 B' C'
      (Functor.FullyFaithful.preimageIso (Functor.FullyFaithful.ofFullyFaithful Y) e') with hB | hC
    · exact Or.inl (IsZero.of_iso (Y.map_isZero hB) eB)
    · exact Or.inr (IsZero.of_iso (Y.map_isZero hC) eC)

/-- A central extension on the original biproduct gives an actual central
extension on the biproduct of representable coherent functors. The comparison
is the canonical additive Yoneda biproduct isomorphism. -/
theorem central_extension (M L : D)
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧
        biprod.inl ≫ c ≫ biprod.fst = a) :
    ∀ a : End (Y.obj M), ∃ c : End (Y.obj M ⊞ Y.obj L),
      (∀ z : End (Y.obj M ⊞ Y.obj L), c * z = z * c) ∧
        StableCategory.PeriodicResolution.restrictM c = a := by
  let : PreservesBinaryBiproducts (Y (D := D)) :=
    preservesBinaryBiproducts_of_preservesBiproducts (Y (D := D))
  intro a'
  obtain ⟨a, ha⟩ := Y.map_surjective a'
  obtain ⟨c, hc, hcorner⟩ := hcentral a
  let E := Y.mapBiprod M L
  let A := (endRingEquiv (M ⊞ L)).toMulEquiv.trans E.conj
  refine ⟨A c, ?_, ?_⟩
  · intro z
    obtain ⟨z, rfl⟩ := A.surjective z
    rw [← map_mul, hc z, map_mul]
  · change biprod.inl ≫ (E.inv ≫ Y.map c ≫ E.hom) ≫ biprod.fst = a'
    calc
      biprod.inl ≫ (E.inv ≫ Y.map c ≫ E.hom) ≫ biprod.fst =
          Y.map biprod.inl ≫ Y.map c ≫ Y.map biprod.fst := by
            simp only [E, Functor.mapBiprod_inv, Functor.mapBiprod_hom,
              ← Category.assoc, biprod.inl_desc]
            rw [Category.assoc, Category.assoc, biprod.lift_fst]
            exact (Category.assoc (Y.map (biprod.inl : M ⟶ M ⊞ L)) (Y.map c)
              (Y.map (biprod.fst : M ⊞ L ⟶ M))).symm
      _ = Y.map (biprod.inl ≫ c ≫ biprod.fst) := by simp only [← Functor.map_comp]
      _ = Y.map a := by rw [hcorner]
      _ = a' := ha

end PretriangulatedV2.YonedaPeriodicData
