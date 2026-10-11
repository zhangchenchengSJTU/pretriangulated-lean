import PretriangulatedV2.SerreDuality
import PretriangulatedV2.AlmostVanishing
import PretriangulatedV2.IndecomposableSplitting
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Almost-vanishing morphisms supplied by Serre duality

For an indecomposable object with commutative finite-dimensional endomorphism
algebra, idempotent completeness implies that its endomorphism algebra is
local. A nonzero linear form annihilating its nonunits determines an actual
almost-vanishing map through the Serre pairing.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped IsMulCommutative

namespace PretriangulatedV2

namespace AlmostVanishingSerre

/-- Artinian commutative rings without nontrivial idempotents are local.
The proof constructs the power-stabilization idempotent directly. -/
theorem isLocalRing_of_idempotents_trivial {R : Type*} [CommRing R]
    [Nontrivial R] [IsArtinianRing R]
    (hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing R := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes R a
  let N := n + 1
  have hN : n ≤ N := Nat.le_succ n
  have hNN : n ≤ N + N := hN.trans (Nat.le_add_right N N)
  have hrange :
      LinearMap.range (a ^ N • LinearMap.id : R →ₗ[R] R) =
        LinearMap.range (a ^ (N + N) • LinearMap.id : R →ₗ[R] R) :=
    (hn N hN).symm.trans (hn (N + N) hNN)
  have hmem : a ^ N ∈ LinearMap.range (a ^ N • LinearMap.id : R →ₗ[R] R) :=
    ⟨1, by simp⟩
  rw [hrange] at hmem
  obtain ⟨b, hb⟩ := hmem
  change a ^ (N + N) * b = a ^ N at hb
  have he : IsIdempotentElem (a ^ N * b) := by
    change (a ^ N * b) * (a ^ N * b) = a ^ N * b
    calc
      (a ^ N * b) * (a ^ N * b) = (a ^ N * a ^ N * b) * b := by ring
      _ = a ^ N * b := by rw [← pow_add, hb]
  rcases hidem _ he with he | he
  · right
    apply IsNilpotent.isUnit_one_sub
    refine ⟨N, ?_⟩
    rw [← hb, pow_add, mul_assoc, he, mul_zero]
  · left
    apply isUnit_iff_exists_inv.mpr
    refine ⟨a ^ n * b, ?_⟩
    simpa only [N, pow_succ, mul_assoc, mul_left_comm a] using he

variable {k : Type w} [Field k]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasBinaryBiproducts C] [IsIdempotentComplete C]

/-- Indecomposability makes every split idempotent trivial. -/
theorem idempotent_eq_zero_or_one {X : C} (hX : Indecomposable X)
    (e : End X) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  by_cases hzero : e = 0
  · exact Or.inl hzero
  right
  obtain ⟨Y, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split X e he
  have hY : ¬ IsZero Y := by
    intro hY
    apply hzero
    rw [← hri, hY.eq_zero_of_src i, comp_zero]
  have : IsSplitMono i := IsSplitMono.mk' ⟨r, hir⟩
  have : IsIso i := isIso_of_isSplitMono_of_indecomposable hY hX i
  change e = 𝟙 X
  rw [← hri]
  apply (cancel_epi i).mp
  simp [← Category.assoc, hir]

include k in
/-- Localness of the actual endomorphism algebra follows from the stated
categorical hypotheses, rather than being added as an application assumption. -/
theorem end_isLocalRing {X : C} [FiniteDimensional k (X ⟶ X)]
    [IsMulCommutative (End X)] (hX : Indecomposable X) : IsLocalRing (End X) := by
  have : Nontrivial (End X) := nontrivial_of_ne (0 : End X) 1 (by
    intro h
    apply hX.1
    exact (IsZero.iff_id_eq_zero X).mpr h.symm)
  have : FiniteDimensional k (End X) := inferInstanceAs (FiniteDimensional k (X ⟶ X))
  have : IsArtinianRing (End X) := IsArtinianRing.of_finite k (End X)
  exact isLocalRing_of_idempotents_trivial (idempotent_eq_zero_or_one hX)

section Functional

variable {R : Type*} [CommRing R] [Algebra k R] [IsLocalRing R]

/-- A genuine nonzero linear form annihilating every nonunit in a local
algebra is obtained by dual separation on its residue vector space. -/
theorem exists_functional_annihilating_nonunits :
    ∃ ℓ : Module.Dual k R, ℓ ≠ 0 ∧ ∀ a : R, ¬ IsUnit a → ℓ a = 0 := by
  let J : Submodule k R := (IsLocalRing.maximalIdeal R).restrictScalars k
  have hone : (1 : R) ∉ J := by
    exact fun h ↦ h isUnit_one
  obtain ⟨ℓ, hℓ, hJ⟩ := J.exists_dual_map_eq_bot_of_notMem hone inferInstance
  refine ⟨ℓ, ?_, ?_⟩
  · intro h
    apply hℓ
    simp [h]
  · intro a ha
    have hmem : ℓ a ∈ J.map ℓ := Submodule.mem_map.mpr ⟨a, ha, rfl⟩
    simpa only [hJ, Submodule.mem_bot] using hmem

end Functional

variable (D : SerreDuality k C)

omit [HasBinaryBiproducts C] [IsIdempotentComplete C] in
/-- A Serre pairing produces an almost-vanishing map from a local
commutative endomorphism algebra, using only a radical-annihilating functional. -/
theorem exists_almostVanishing_of_local {X : C} [IsMulCommutative (End X)]
    [IsLocalRing (End X)] :
    ∃ a : X ⟶ D.equivalence.functor.obj X, IsAlmostVanishing a := by
  obtain ⟨ℓ, hℓ, hrad⟩ := exists_functional_annihilating_nonunits (k := k) (R := End X)
  let a : X ⟶ D.equivalence.functor.obj X := (D.duality X X).symm ℓ
  have ha : D.duality X X a = ℓ := (D.duality X X).apply_symm_apply ℓ
  refine ⟨a, ?_, ?_, ?_⟩
  · intro h
    apply hℓ
    rw [← ha, h, map_zero]
  · intro W s hs
    apply D.hom_eq_zero_of_pairings_eq_zero
    intro b
    obtain ⟨r, hr⟩ := D.equivalence.functor.map_surjective (s ≫ b)
    rw [← D.naturality_target s a b, ← hr, D.pairing_serre_map, ha]
    apply hrad
    intro hu
    have : IsIso r := (isUnit_iff_isIso r).mp hu
    have : IsIso (s ≫ b) := by
      rw [← hr]
      infer_instance
    apply hs
    exact IsSplitMono.mk' ⟨b ≫ inv (s ≫ b), by simp [← Category.assoc]⟩
  · intro W t ht
    apply D.serreHom_eq_zero_of_pairings_eq_zero
    intro b
    rw [D.naturality_target t b a, ha]
    apply hrad
    intro hu
    have : IsIso (b ≫ t) := (isUnit_iff_isIso (b ≫ t)).mp hu
    apply ht
    exact IsSplitEpi.mk' ⟨inv (b ≫ t) ≫ b, by simp [Category.assoc]⟩

/-- Actual almost-vanishing existence for an indecomposable object with
commutative finite-dimensional endomorphisms. Localness is proved internally. -/
theorem exists_almostVanishing {X : C} [FiniteDimensional k (X ⟶ X)]
    [IsMulCommutative (End X)] (hX : Indecomposable X) :
    ∃ a : X ⟶ D.equivalence.functor.obj X, IsAlmostVanishing a := by
  have := end_isLocalRing (k := k) hX
  exact exists_almostVanishing_of_local D

omit [HasBinaryBiproducts C] [IsIdempotentComplete C] in
/-- Postcomposing by an isomorphism preserves both defining annihilation
properties of an almost-vanishing morphism. -/
theorem almostVanishing_comp_iso {X Y Z : C} {a : X ⟶ Y}
    (ha : IsAlmostVanishing a) (e : Y ≅ Z) : IsAlmostVanishing (a ≫ e.hom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply ha.nonzero
    apply (cancel_mono e.hom).mp
    simpa using h
  · intro W s hs
    have hs' : ¬ IsSplitMono (e.hom ≫ s) := by
      intro h
      have : IsSplitMono (e.hom ≫ s) := h
      apply hs
      simpa only [Iso.inv_hom_id_assoc] using
        (inferInstance : IsSplitMono (e.inv ≫ (e.hom ≫ s)))
    simpa only [Category.assoc] using ha.postcomp_eq_zero (e.hom ≫ s) hs'
  · intro W t ht
    rw [← Category.assoc, ha.precomp_eq_zero t ht, zero_comp]

/-- If the Serre image is isomorphic to the original indecomposable object,
the Serre pairing produces an actual almost-vanishing endomorphism. -/
theorem exists_almostVanishing_endomorphism {X : C} [FiniteDimensional k (X ⟶ X)]
    [IsMulCommutative (End X)] (hX : Indecomposable X)
    (e : D.equivalence.functor.obj X ≅ X) :
    ∃ a : X ⟶ X, IsAlmostVanishing a := by
  obtain ⟨a, ha⟩ := exists_almostVanishing D hX
  exact ⟨a ≫ e.hom, almostVanishing_comp_iso ha e⟩

/-- The almost-vanishing endomorphism in the nonfield case is noninvertible,
as required in Proposition 7.1. -/
theorem exists_noninvertible_almostVanishing_endomorphism {X : C}
    [FiniteDimensional k (X ⟶ X)] [IsMulCommutative (End X)]
    (hX : Indecomposable X) (hfield : ¬ IsField (End X))
    (e : D.equivalence.functor.obj X ≅ X) :
    ∃ a : X ⟶ X, IsAlmostVanishing a ∧ ¬ IsIso a := by
  have := end_isLocalRing (k := k) hX
  obtain ⟨f, hf, hfu⟩ := Ring.exists_not_isUnit_of_not_isField hfield
  have hfi : ¬ IsIso f := fun h ↦ hfu ((isUnit_iff_isIso f).mpr h)
  obtain ⟨a, ha⟩ := exists_almostVanishing_endomorphism D hX e
  refine ⟨a, ha, ?_⟩
  intro h
  have : IsIso a := h
  apply hf
  apply (cancel_mono a).mp
  simpa using ha.precomp_eq_zero f (not_isSplitEpi_of_not_isIso (k := k) f hfi)

end AlmostVanishingSerre

end PretriangulatedV2
