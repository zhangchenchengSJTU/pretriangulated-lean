import PretriangulatedV2.TruncatedModules
import PretriangulatedV2.StableLinear
import PretriangulatedV2.TruncatedPolynomialLocal
import PretriangulatedV2.AlmostSplitSequences
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Field.Equiv

/-!
# Actual morphism calculations for the truncated modules

Morphisms are actual linear maps over the large quotient. Cyclic generation
reduces their equality to the image of one; coordinate computations then
control the quotient by maps through categorical projective objects.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators

namespace PretriangulatedV2.TruncatedStableHom

open TruncatedPolynomialAlgebra TruncatedModules StableCategory

universe u

variable {R : Type u} [CommRing R]

/-- Restricted quotient modules are cyclic, so linear maps are determined by
the image of the actual residue class of one. -/
theorem linearMap_ext_one {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ N)
    (f g : Carrier R N n hn →ₗ[Trunc R N] Carrier R N l hl)
    (h : f 1 = g 1) : f = g := by
  ext b
  obtain ⟨a, ha⟩ := reduction_surjective (R := R) hn (show Trunc R n from b)
  have hb : a • (1 : Carrier R N n hn) = b := by
    rw [carrier_smul, mul_one]
    exact ha
  rw [← hb, f.map_smul, g.map_smul, h]

/-- Equality of actual finite-module morphisms is equally detected at one. -/
theorem hom_ext_one {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ N)
    (f g : truncatedModule R N n hn ⟶ truncatedModule R N l hl)
    (h : f.hom.hom 1 = g.hom.hom 1) : f = g := by
  apply FGModuleCat.hom_ext
  exact linearMap_ext_one hn hl f.hom.hom g.hom.hom h


/-- Every actual endomorphism is multiplication by its image of one. -/
theorem linearMap_apply_eq_mul_value {N n : ℕ} (hn : n ≤ N)
    (f : Carrier R N n hn →ₗ[Trunc R N] Carrier R N n hn)
    (b : Carrier R N n hn) : f b = b * f 1 := by
  obtain ⟨a, ha⟩ := reduction_surjective (R := R) hn (show Trunc R n from b)
  have hb : a • (1 : Carrier R N n hn) = b := by
    rw [carrier_smul, mul_one]
    exact ha
  rw [← hb, f.map_smul, carrier_smul, carrier_smul, mul_one]

/-- The ordinary endomorphism ring of each cyclic quotient is exactly that
quotient ring, through evaluation at one and actual multiplication maps. -/
def endValueRingEquiv {N n : ℕ} (hn : n ≤ N) :
    End (truncatedModule R N n hn) ≃+* Carrier R N n hn where
  toFun f := f.hom.hom 1
  invFun b := FGModuleCat.ofHom (LinearMap.mul (Trunc R N) (Carrier R N n hn) b)
  left_inv f := by
    apply hom_ext_one hn hn
    change f.hom.hom 1 * 1 = f.hom.hom 1
    exact mul_one _
  right_inv b := mul_one b
  map_mul' f g := by
    change f.hom.hom (g.hom.hom 1) = f.hom.hom 1 * g.hom.hom 1
    rw [linearMap_apply_eq_mul_value, mul_comm]
  map_add' f g := rfl

variable (R) [Nontrivial R]

/-- A coordinate of multiplication by x^m detects the corresponding low
coordinate in the actual quotient of length 2m. -/
theorem coefficient_mul_m (m : ℕ) (i : Fin m) (b : Trunc R (2 * m)) :
    coefficient (R := R) (2 * m) ⟨m + (i : ℕ), by omega⟩
      (b * x R (2 * m) ^ m) =
      coefficient (R := R) (2 * m) ⟨i, by omega⟩ b := by
  rw [coefficient_mul_pow]
  have heq : ∀ j : Fin (2 * m), (j : ℕ) + m = m + (i : ℕ) ↔
      j = ⟨i, by omega⟩ := by
    intro j
    constructor
    · intro h
      apply Fin.ext
      change (j : ℕ) = (i : ℕ)
      omega
    · intro h
      subst j
      change (i : ℕ) + m = m + (i : ℕ)
      omega
  simp only [heq]
  simp

/-- An element killed by x^m has zero image in the shorter quotient. -/
theorem reduction_eq_zero_of_annihilated (m : ℕ) (b : Trunc R (2 * m))
    (hb : x R (2 * m) ^ m * b = 0) :
    reduction (R := R) (show m ≤ 2 * m by omega) b = 0 := by
  apply (basis (R := R) m).repr.injective
  ext i
  change coefficient (R := R) m i
      (reduction (show m ≤ 2 * m by omega) b) = coefficient (R := R) m i 0
  rw [coefficient_reduction, map_zero]
  have h := congrArg
    (coefficient (R := R) (2 * m) ⟨m + (i : ℕ), by omega⟩) hb
  rw [mul_comm (x R (2 * m) ^ m) b, coefficient_mul_m, map_zero] at h
  exact h

/-- This Hom-composition vanishes already in the actual module category. -/
theorem hom_L₀_q₀_zero (m : ℕ) (f : L₀ R m ⟶ M₀ R m) : f ≫ q₀ R m = 0 := by
  apply hom_ext_one (by omega) (by omega)
  change reduction (show m ≤ 2 * m by omega) (f.hom.hom 1) = 0
  apply reduction_eq_zero_of_annihilated
  let a : algebra R m := x R (3 * m) ^ m
  have ha : a • (1 : L₀ R m) = 0 := by
    rw [carrier_smul]
    change reduction (show m ≤ 3 * m by omega) a * 1 = 0
    simp [a]
  have h := f.hom.hom.map_smul a (1 : L₀ R m)
  rw [ha, map_zero] at h
  change 0 = reduction (show 2 * m ≤ 3 * m by omega) a * (show Trunc R (2 * m) from f.hom.hom 1) at h
  simpa only [a, map_pow, reduction_x] using h.symm


/-- Shifted remainder multiplication for arbitrary complementary lengths.
This will supply the actual projective factorization through the regular
algebra, rather than an abstract witness of stable vanishing. -/
def shiftRaw (n t N : ℕ) (_h : n + t = N) : Trunc R n →ₗ[R] Trunc R N :=
  (basis (R := R) n).constr R (fun i => x R N ^ (t + (i : ℕ)))

@[simp] theorem shiftRaw_basis (n t N : ℕ) (h : n + t = N) (i : Fin n) :
    shiftRaw R n t N h (x R n ^ (i : ℕ)) = x R N ^ (t + (i : ℕ)) := by
  rw [← basis_apply (R := R) n i]
  simp only [shiftRaw, Basis.constr_basis]

theorem shiftRaw_pow (n t N : ℕ) (h : n + t = N) (s : ℕ) :
    shiftRaw R n t N h (x R n ^ s) = x R N ^ (t + s) := by
  by_cases hs : s < n
  · exact shiftRaw_basis R n t N h ⟨s, hs⟩
  · rw [x_pow_eq_zero_of_le (by omega), map_zero,
      x_pow_eq_zero_of_le (by omega)]

theorem shiftRaw_mul_x (n t N : ℕ) (h : n + t = N) (b : Trunc R n) :
    shiftRaw R n t N h (x R n * b) = x R N * shiftRaw R n t N h b := by
  have hlin : (shiftRaw R n t N h).comp (LinearMap.mul R (Trunc R n) (x R n)) =
      (LinearMap.mul R (Trunc R N) (x R N)).comp (shiftRaw R n t N h) := by
    apply (basis (R := R) n).ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.mul_apply', basis_apply]
    rw [← pow_succ', shiftRaw_pow, shiftRaw_pow, ← pow_succ']
    congr 1
  exact congrArg (fun f => f b) hlin

theorem shiftRaw_mul_pow (n t N : ℕ) (h : n + t = N) (s : ℕ) (b : Trunc R n) :
    shiftRaw R n t N h (x R n ^ s * b) = x R N ^ s * shiftRaw R n t N h b := by
  induction s with
  | zero => simp
  | succ s hs =>
    rw [pow_succ', mul_assoc, shiftRaw_mul_x, hs, ← mul_assoc, ← pow_succ']

theorem shiftRaw_reduction_mul (n t N : ℕ) (h : n + t = N)
    (a : Trunc R N) (b : Trunc R n) :
    shiftRaw R n t N h (reduction (show n ≤ N by omega) a * b) =
      a * shiftRaw R n t N h b := by
  conv_lhs => rw [← (basis (R := R) N).sum_repr a]
  conv_rhs => rw [← (basis (R := R) N).sum_repr a]
  simp only [map_sum, map_smul, basis_apply, map_pow, reduction_x,
    Finset.sum_mul, Algebra.smul_mul_assoc, shiftRaw_mul_pow]

/-- An explicit actual A-linear map M₀→A, given by multiplication by x^m
on canonical remainders. -/
def regularLiftLinear (m : ℕ) :
    Carrier R (3 * m) (2 * m) (by omega) →ₗ[algebra R m] algebra R m where
  toFun := shiftRaw R (2 * m) m (3 * m) (by omega)
  map_add' := map_add _
  map_smul' a b := shiftRaw_reduction_mul R (2 * m) m (3 * m) (by omega) a b

/-- Its target is the actual regular finite module. -/
abbrev regular (m : ℕ) : FGModuleCat (algebra R m) :=
  FGModuleCat.of (algebra R m) (algebra R m)

instance regular_projective (m : ℕ) : Projective (regular R m) := by
  apply (forget₂ (FGModuleCat (algebra R m)) (ModuleCat (algebra R m))).projective_of_map_projective
  exact ModuleCat.projective_of_free (Module.Free.chooseBasis (algebra R m) (algebra R m))

def regularLift (m : ℕ) : M₀ R m ⟶ regular R m := FGModuleCat.ofHom (regularLiftLinear R m)

/-- Multiplication out of the regular module is an actual A-linear map. -/
def regularMultiply (m : ℕ) (b : M₀ R m) : regular R m ⟶ M₀ R m :=
  FGModuleCat.ofHom ((LinearMap.mul (algebra R m)
    (Carrier R (3 * m) (2 * m) (by omega)) b).comp
      (Algebra.linearMap (algebra R m) (Carrier R (3 * m) (2 * m) (by omega))))

/-- Multiplication by x^m annihilates precisely the discarded part of a
quotient representative. -/
theorem iotaRaw_projection (m : ℕ) (b : Trunc R (2 * m)) :
    iotaRaw R m (reduction (show m ≤ 2 * m by omega) b) = b * x R (2 * m) ^ m := by
  obtain ⟨a, rfl⟩ := reduction_surjective (R := R) (show 2 * m ≤ 3 * m by omega) b
  rw [reduction_comp_apply]
  have hi : iotaRaw R m 1 = x R (2 * m) ^ m := by
    simpa only [pow_zero, Nat.add_zero] using iotaRaw_pow R m 0
  simpa only [mul_one, hi] using iotaRaw_reduction_mul R m a (1 : Trunc R m)

/-- Every composition M₀→L₀→M₀ factors through the actual regular projective
module, using a genuine lift of its image of one. -/
theorem hom_M₀_iota₀_factors (m : ℕ) (f : M₀ R m ⟶ L₀ R m) :
    PretriangulatedV2.IdealQuotient.FactorsThrough
      (CategoryTheory.Projective : FGModuleCat (algebra R m) → Prop) (f ≫ iota₀ R m) := by
  obtain ⟨b, hb⟩ := reduction_surjective (R := R) (show m ≤ 2 * m by omega)
    (show Trunc R m from f.hom.hom 1)
  let b' : M₀ R m := b
  refine ⟨regular R m, inferInstance, regularLift R m, regularMultiply R m b', ?_⟩
  apply hom_ext_one (by omega) (by omega)
  change b * reduction (show 2 * m ≤ 3 * m by omega)
    (shiftRaw R (2 * m) m (3 * m) (by omega) 1) = iotaRaw R m (f.hom.hom 1)
  have hs : shiftRaw R (2 * m) m (3 * m) (by omega) 1 = x R (3 * m) ^ m := by
    simpa only [pow_zero, Nat.add_zero] using
      shiftRaw_pow R (2 * m) m (3 * m) (by omega) 0
  calc
    b * reduction (show 2 * m ≤ 3 * m by omega)
        (shiftRaw R (2 * m) m (3 * m) (by omega) 1) = b * x R (2 * m) ^ m := by
      rw [hs, map_pow, reduction_x]
    _ = iotaRaw R m (reduction (show m ≤ 2 * m by omega) b) :=
      (iotaRaw_projection R m b).symm
    _ = iotaRaw R m (f.hom.hom 1) := congrArg (iotaRaw R m) hb


/-- More generally a shifted coefficient detects a low coordinate. -/
theorem coefficient_mul_shift (N t : ℕ) (i : Fin (N - t)) (b : Trunc R N) :
    coefficient (R := R) N ⟨t + (i : ℕ), by omega⟩ (b * x R N ^ t) =
      coefficient (R := R) N ⟨i, by omega⟩ b := by
  rw [coefficient_mul_pow]
  have heq : ∀ j : Fin N, (j : ℕ) + t = t + (i : ℕ) ↔ j = ⟨i, by omega⟩ := by
    intro j
    constructor
    · intro h
      apply Fin.ext
      change (j : ℕ) = (i : ℕ)
      omega
    · intro h
      subst j
      change (i : ℕ) + t = t + (i : ℕ)
      omega
  simp only [heq]
  simp

/-- Annihilation by the complementary power implies vanishing after the
actual quotient reduction. -/
theorem reduction_zero_of_complementary_annihilator {N n : ℕ} (hn : n ≤ N)
    (b : Trunc R N) (hb : x R N ^ (N - n) * b = 0) : reduction hn b = 0 := by
  apply (basis (R := R) n).repr.injective
  ext i
  change coefficient (R := R) n i (reduction hn b) = coefficient (R := R) n i 0
  rw [coefficient_reduction, map_zero]
  let j : Fin (N - (N - n)) := ⟨i, by omega⟩
  have h := congrArg (coefficient (R := R) N ⟨(N - n) + (j : ℕ), by omega⟩) hb
  rw [mul_comm (x R N ^ (N - n)) b, coefficient_mul_shift, map_zero] at h
  exact h

omit [Nontrivial R] in
/-- A map out of a finite free module vanishes on any vector whose
coordinates vanish under the quotient action on L₀. -/
theorem free_to_L₀_vanish (m d : ℕ)
    (f : (Fin d → algebra R m) →ₗ[algebra R m] Carrier R (3 * m) m (by omega))
    (v : Fin d → algebra R m)
    (hv : ∀ j, reduction (show m ≤ 3 * m by omega) (v j) = 0) : f v = 0 := by
  conv_lhs => rw [← (Pi.basisFun (algebra R m) (Fin d)).sum_repr v]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j _
  change ((Pi.basisFun (algebra R m) (Fin d)).repr v j) •
      f (Pi.basisFun (algebra R m) (Fin d) j) = 0
  have hj : (Pi.basisFun (algebra R m) (Fin d)).repr v j = v j := by simp
  rw [hj, carrier_smul]
  change reduction (show m ≤ 3 * m by omega) (v j) *
    (show Trunc R m from f (Pi.basisFun (algebra R m) (Fin d) j)) = 0
  rw [hv, zero_mul]

/-- The kernel of the stable quotient on endomorphisms is contained in the
kernel of reduction of their actual image of one. Projective objects are
handled by a genuine finite-free cover and its projective splitting. -/
theorem reduction_value_zero_of_factors (m : ℕ) (f : End (M₀ R m))
    (hf : PretriangulatedV2.IdealQuotient.FactorsThrough
      (CategoryTheory.Projective : FGModuleCat (algebra R m) → Prop) f) :
    reduction (R := R) (show m ≤ 2 * m by omega) (show Trunc R (2 * m) from f.hom.hom 1) = 0 := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  have : Projective P := hP
  obtain ⟨d, p, hp⟩ := FiniteModuleCategory.exists_finiteFree_presentation P
  have : Epi p := hp
  let s := Projective.factorThru (𝟙 P) p
  have hs : s ≫ p = 𝟙 P := Projective.factorThru_comp _ _
  let u := a ≫ s
  let g := p ≫ b ≫ q₀ R m
  have hu : ∀ j : Fin d,
      reduction (show m ≤ 3 * m by omega) (u.hom.hom 1 j) = 0 := by
    intro j
    apply reduction_zero_of_complementary_annihilator
    let c : algebra R m := x R (3 * m) ^ (2 * m)
    have hc : c • (1 : M₀ R m) = 0 := by
      rw [carrier_smul]
      change reduction (show 2 * m ≤ 3 * m by omega) c * 1 = 0
      simp [c]
    have h := u.hom.hom.map_smul c (1 : M₀ R m)
    rw [hc, map_zero] at h
    have hj := congrArg (fun v : Fin d → algebra R m => v j) h
    change 0 = c * u.hom.hom 1 j at hj
    simpa only [c, show 3 * m - m = 2 * m by omega] using hj.symm
  have hz := free_to_L₀_vanish R m d g.hom.hom (u.hom.hom 1) hu
  have heq : u ≫ g = f ≫ q₀ R m := by
    dsimp [u, g]
    simp only [← Category.assoc]
    rw [Category.assoc a s p, hs, Category.comp_id, hab]
  have hz' : (u ≫ g).hom.hom 1 = 0 := hz
  rw [heq] at hz'
  exact hz'

/-- Conversely, every endomorphism with zero reduced value is a composition
through iota₀, hence factors through the genuine regular projective. -/
theorem factors_of_reduction_value_zero (m : ℕ) (f : End (M₀ R m))
    (hf : reduction (R := R) (show m ≤ 2 * m by omega)
      (show Trunc R (2 * m) from f.hom.hom 1) = 0) :
    PretriangulatedV2.IdealQuotient.FactorsThrough
      (CategoryTheory.Projective : FGModuleCat (algebra R m) → Prop) f := by
  obtain ⟨b, hb⟩ := (mem_range_iotaRaw_iff R m (show Trunc R (2 * m) from f.hom.hom 1)).mpr hf
  let glin : Carrier R (3 * m) (2 * m) (by omega) →ₗ[algebra R m]
      Carrier R (3 * m) m (by omega) := {
    toFun := fun v => b * reduction (show m ≤ 2 * m by omega) (show Trunc R (2 * m) from v)
    map_add' := by intros; simp [map_add, mul_add]
    map_smul' := by
      intro a v
      change b * reduction (show m ≤ 2 * m by omega)
        (reduction (show 2 * m ≤ 3 * m by omega) a * (show Trunc R (2 * m) from v)) =
          reduction (show m ≤ 3 * m by omega) a *
            (b * reduction (show m ≤ 2 * m by omega) (show Trunc R (2 * m) from v))
      rw [map_mul, reduction_comp_apply]
      ring }
  let g : M₀ R m ⟶ L₀ R m := FGModuleCat.ofHom glin
  have heq : g ≫ iota₀ R m = f := by
    apply hom_ext_one (N := 3 * m) (n := 2 * m) (l := 2 * m) (by omega) (by omega)
    change iotaRaw R m (glin 1) = (show Trunc R (2 * m) from f.hom.hom 1)
    simpa [glin] using hb
  rw [← heq]
  exact hom_M₀_iota₀_factors R m g


/-- Reduction of the actual endomorphism value, as a genuine ring map. -/
def endReductionHom (m : ℕ) : End (M₀ R m) →+* Trunc R m :=
  (reduction (show m ≤ 2 * m by omega)).toRingHom.comp
    (show End (M₀ R m) →+* Trunc R (2 * m) from
      (endValueRingEquiv (R := R) (show 2 * m ≤ 3 * m by omega)).toRingHom)

omit [Nontrivial R] in
@[simp] theorem endReductionHom_apply (m : ℕ) (f : End (M₀ R m)) :
    endReductionHom R m f =
      reduction (show m ≤ 2 * m by omega) (show Trunc R (2 * m) from f.hom.hom 1) := rfl

omit [Nontrivial R] in
theorem endReductionHom_surjective (m : ℕ) : Function.Surjective (endReductionHom R m) := by
  intro b
  obtain ⟨a, ha⟩ := reduction_surjective (R := R) (show m ≤ 2 * m by omega) b
  refine ⟨(endValueRingEquiv (R := R) (show 2 * m ≤ 3 * m by omega)).symm a, ?_⟩
  change reduction (show m ≤ 2 * m by omega)
    ((endValueRingEquiv (R := R) (show 2 * m ≤ 3 * m by omega))
      ((endValueRingEquiv (R := R) (show 2 * m ≤ 3 * m by omega)).symm a)) = b
  rw [RingEquiv.apply_symm_apply]
  exact ha

section Noetherian

variable [IsNoetherianRing R]

/-- Consequently the stable Hom-composition with the projection vanishes,
proved for every actual quotient morphism by the quotient functor's fullness. -/
theorem stableHom_L₀_q₀_zero (m : ℕ)
    (f : (projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (L₀ R m) ⟶
      (projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m)) :
    f ≫ (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map (q₀ R m) = 0 := by
  let Q := projectiveStableQuotient (C := FGModuleCat (algebra R m))
  obtain ⟨f, rfl⟩ := Q.map_surjective f
  rw [← Q.map_comp, hom_L₀_q₀_zero, Q.map_zero]


/-- The second stable Hom-composition vanishes because its actual morphism
factors through the categorical projective regular module. -/
theorem stableHom_M₀_iota₀_zero (m : ℕ)
    (f : (projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m) ⟶
      (projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (L₀ R m)) :
    f ≫ (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map (iota₀ R m) = 0 := by
  let Q := projectiveStableQuotient (C := FGModuleCat (algebra R m))
  obtain ⟨f, rfl⟩ := Q.map_surjective f
  rw [← Q.map_comp, PretriangulatedV2.IdealQuotient.functor_map_eq_zero_iff]
  exact hom_M₀_iota₀_factors R m f


/-- The actual quotient functor on endomorphism rings. -/
def stableEndProjection (m : ℕ) : End (M₀ R m) →+*
    End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m)) :=
  { toFun := (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map
    map_one' := (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map_id _
    map_mul' := fun f g => (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map_comp g f
    map_zero' := by simp
    map_add' := fun _ _ => (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map_add }

omit [Nontrivial R] in
theorem stableEndProjection_surjective (m : ℕ) : Function.Surjective (stableEndProjection R m) :=
  (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map_surjective

/-- The projective ideal and the computed coefficient kernel agree. -/
theorem stableEndProjection_zero_iff (m : ℕ) (f : End (M₀ R m)) :
    stableEndProjection R m f = 0 ↔ endReductionHom R m f = 0 := by
  change (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map f = 0 ↔
    reduction (show m ≤ 2 * m by omega) (show Trunc R (2 * m) from f.hom.hom 1) = 0
  rw [PretriangulatedV2.IdealQuotient.functor_map_eq_zero_iff]
  exact ⟨reduction_value_zero_of_factors R m f, factors_of_reduction_value_zero R m f⟩

/-- The coefficient reduction descends to the actual stable endomorphism
ring via the proved kernel inclusion and the quotient's actual fullness. -/
def stableEndValueHom (m : ℕ) :
    End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m)) →+* Trunc R m :=
  (stableEndProjection R m).liftOfSurjective (stableEndProjection_surjective R m)
    ⟨endReductionHom R m, fun f hf =>
      (stableEndProjection_zero_iff R m f).mp hf⟩

@[simp]
theorem stableEndValueHom_map (m : ℕ) (f : End (M₀ R m)) :
    stableEndValueHom R m (stableEndProjection R m f) = endReductionHom R m f :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

theorem stableEndValueHom_surjective (m : ℕ) : Function.Surjective (stableEndValueHom R m) := by
  intro b
  obtain ⟨f, hf⟩ := endReductionHom_surjective R m b
  exact ⟨stableEndProjection R m f, (stableEndValueHom_map R m f).trans hf⟩

theorem stableEndValueHom_injective (m : ℕ) : Function.Injective (stableEndValueHom R m) := by
  intro f g h
  have hz : stableEndValueHom R m (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨a, ha⟩ := stableEndProjection_surjective R m (f - g)
  rw [← ha, stableEndValueHom_map] at hz
  have hq := (stableEndProjection_zero_iff R m a).mpr hz
  exact sub_eq_zero.mp (ha.symm.trans hq)

/-- The actual stable endomorphism ring is the literal truncated polynomial
quotient of length m, with no stable-Hom calculation assumed. -/
def stableEndRingEquiv (m : ℕ) :
    End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m)) ≃+* Trunc R m :=
  RingEquiv.ofBijective (stableEndValueHom R m)
    ⟨stableEndValueHom_injective R m, stableEndValueHom_surjective R m⟩


section Field

variable {k : Type u} [Field k] [Algebra k R]

/-- The computed stable endomorphism ring identification respects the actual
coefficient-field action, and hence is an algebra equivalence. -/
def stableEndAlgEquiv (m : ℕ) :
    End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m)) ≃ₐ[k] Trunc R m where
  toRingEquiv := stableEndRingEquiv R m
  commutes' r := by
    let Q := projectiveStableQuotient (C := FGModuleCat (algebra R m))
    have hs : algebraMap k (End (Q.obj (M₀ R m))) r =
        stableEndProjection R m (algebraMap k (End (M₀ R m)) r) := by
      change r • (𝟙 (Q.obj (M₀ R m))) = Q.map (r • (𝟙 (M₀ R m)))
      simp
    rw [hs]
    change stableEndValueHom R m
      (stableEndProjection R m (algebraMap k (End (M₀ R m)) r)) = algebraMap k (Trunc R m) r
    rw [stableEndValueHom_map, endReductionHom_apply]
    change reduction (show m ≤ 2 * m by omega)
      (reduction (show 2 * m ≤ 3 * m by omega) (algebraMap k (algebra R m) r) * 1) =
        algebraMap k (Trunc R m) r
    rw [mul_one, reduction_comp_apply]
    exact ((reduction (R := R) (show m ≤ 3 * m by omega)).restrictScalars k).commutes r

end Field


omit [IsNoetherianRing R] in
/-- A projective-factor endomorphism of L₀ is already zero before passing to
any stable quotient. The free-cover coordinates are annihilated by x^m. -/
theorem end_L₀_zero_of_factors (m : ℕ) (f : End (L₀ R m))
    (hf : PretriangulatedV2.IdealQuotient.FactorsThrough
      (CategoryTheory.Projective : FGModuleCat (algebra R m) → Prop) f) : f = 0 := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  have : Projective P := hP
  obtain ⟨d, p, hp⟩ := FiniteModuleCategory.exists_finiteFree_presentation P
  have : Epi p := hp
  let s := Projective.factorThru (𝟙 P) p
  have hs : s ≫ p = 𝟙 P := Projective.factorThru_comp _ _
  let u := a ≫ s
  let g := p ≫ b
  have hu : ∀ j : Fin d,
      reduction (show m ≤ 3 * m by omega) (u.hom.hom 1 j) = 0 := by
    intro j
    have hred : reduction (show 2 * m ≤ 3 * m by omega) (u.hom.hom 1 j) = 0 := by
      apply reduction_zero_of_complementary_annihilator
      let c : algebra R m := x R (3 * m) ^ m
      have hc : c • (1 : L₀ R m) = 0 := by
        rw [carrier_smul]
        change reduction (show m ≤ 3 * m by omega) c * 1 = 0
        simp [c]
      have h := u.hom.hom.map_smul c (1 : L₀ R m)
      rw [hc, map_zero] at h
      have hj := congrArg (fun v : Fin d → algebra R m => v j) h
      change 0 = c * u.hom.hom 1 j at hj
      simpa only [c, show 3 * m - 2 * m = m by omega] using hj.symm
    rw [← reduction_comp_apply (show 2 * m ≤ 3 * m by omega)
      (show m ≤ 2 * m by omega), hred, map_zero]
  have hz := free_to_L₀_vanish R m d g.hom.hom (u.hom.hom 1) hu
  have heq : u ≫ g = f := by
    dsimp [u, g]
    simp only [← Category.assoc]
    rw [Category.assoc a s p, hs, Category.comp_id, hab]
  apply hom_ext_one (N := 3 * m) (n := m) (l := m) (by omega) (by omega)
  change f.hom.hom 1 = 0
  simpa only [heq] using (show (u ≫ g).hom.hom 1 = 0 from hz)

omit [Nontrivial R] in
/-- The actual quotient functor on endomorphisms of L₀. -/
def stableEndLProjection (m : ℕ) : End (L₀ R m) →+*
    End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (L₀ R m)) :=
  { toFun := (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map
    map_one' := (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map_id _
    map_mul' := fun f g => (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map_comp g f
    map_zero' := by simp
    map_add' := fun _ _ => (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map_add }

/-- Every endomorphism of L₀ survives faithfully in the stable category. -/
theorem stableEndLProjection_injective (m : ℕ) : Function.Injective (stableEndLProjection R m) := by
  intro f g h
  have hz : stableEndLProjection R m (f - g) = 0 := by rw [map_sub, h, sub_self]
  have hf : PretriangulatedV2.IdealQuotient.FactorsThrough
      (CategoryTheory.Projective : FGModuleCat (algebra R m) → Prop) (f - g) :=
    (PretriangulatedV2.IdealQuotient.functor_map_eq_zero_iff _ _).mp hz
  exact sub_eq_zero.mp (end_L₀_zero_of_factors R m (f - g) hf)

/-- The actual stable endomorphism ring of L₀ is the length-m quotient. -/
def stableEndLRingEquiv (m : ℕ) :
    End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (L₀ R m)) ≃+* Trunc R m :=
  (RingEquiv.ofBijective (stableEndLProjection R m)
    ⟨stableEndLProjection_injective R m,
      (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map_surjective⟩).symm.trans
    (show End (L₀ R m) ≃+* Trunc R m from
      endValueRingEquiv (R := R) (show m ≤ 3 * m by omega))

/-- Local rings have only the two trivial idempotents. -/
theorem idempotent_trivial_of_local {T : Type u} [CommRing T] [IsLocalRing T]
    (a : T) (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · right
    exact h.mul_left_cancel (by simpa only [mul_one] using ha.eq)
  · left
    apply h.mul_right_cancel
    simpa [mul_sub, ha] using (show a * (1 - a) = 0 by rw [mul_sub, mul_one, ha, sub_self])

/-- A computed local endomorphism ring implies genuine categorical
indecomposability; the ring isomorphism also certifies the object is nonzero. -/
theorem indecomposable_of_local_endEquiv {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {T : Type u} [CommRing T] [IsLocalRing T]
    (X : C) (e : End X ≃+* T) : Indecomposable X := by
  apply AlmostSplitSequences.indecomposable_of_idempotents_trivial
  · intro hX
    have hz : (1 : End X) = 0 := (IsZero.iff_id_eq_zero X).mp hX
    have h := congrArg e hz
    simp only [map_one, map_zero] at h
    exact one_ne_zero h
  · intro a ha
    have hid : IsIdempotentElem (e a) := by
      change e a * e a = e a
      rw [← map_mul, ha]
    rcases idempotent_trivial_of_local (e a) hid with h | h
    · left
      apply e.injective
      simpa using h
    · right
      apply e.injective
      simpa using h

omit [Nontrivial R] in
/-- Under the actual local coefficient-ring hypothesis, M₀ is stably
indecomposable. No stable indecomposability assumption is used. -/
theorem stableM₀_indecomposable [IsLocalRing R] (m : ℕ) (hm : 0 < m) :
    Indecomposable ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m)) := by
  let : IsLocalRing (Trunc R m) := isLocalRing (R := R) m hm
  exact indecomposable_of_local_endEquiv _ (stableEndRingEquiv R m)

omit [Nontrivial R] in
/-- Under the actual local coefficient-ring hypothesis, L₀ is stably
indecomposable, as shown by its separately computed stable endomorphisms. -/
theorem stableL₀_indecomposable [IsLocalRing R] (m : ℕ) (hm : 0 < m) :
    Indecomposable ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (L₀ R m)) := by
  let : IsLocalRing (Trunc R m) := isLocalRing (R := R) m hm
  exact indecomposable_of_local_endEquiv _ (stableEndLRingEquiv R m)

/-- The actual stable endomorphism multiplication is commutative. -/
theorem stableEnd_comm (m : ℕ)
    (f g : End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m))) :
    f * g = g * f := by
  apply (stableEndRingEquiv R m).injective
  simp only [map_mul, mul_comm]

omit [Nontrivial R] in
/-- Locality is also transferred to the actual stable endomorphism ring. -/
theorem stableEnd_isLocalRing [IsLocalRing R] (m : ℕ) (hm : 0 < m) :
    IsLocalRing (End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m))) := by
  let : IsLocalRing (Trunc R m) := isLocalRing (R := R) m hm
  let : Nontrivial (End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj
    (M₀ R m))) := (stableEndRingEquiv R m).toEquiv.nontrivial
  exact IsLocalRing.of_surjective' (stableEndRingEquiv R m).symm.toRingHom
    (stableEndRingEquiv R m).symm.surjective

/-- The actual stable endomorphism ring of M₀ is not a field for m≥2. -/
theorem stableEnd_not_isField (m : ℕ) (hm : 2 ≤ m) :
    ¬ IsField (End ((projectiveStableQuotient (C := FGModuleCat (algebra R m))).obj (M₀ R m))) := by
  intro h
  apply not_isField (R := R) m hm
  exact (stableEndRingEquiv R m).symm.toMulEquiv.isField h


omit [Nontrivial R] [IsNoetherianRing R] in
/-- Actual maps out of finite free modules kill vectors whose coordinates
act as zero on the specified quotient module. -/
theorem free_to_truncated_vanish {N l : ℕ} (hl : l ≤ N) (d : ℕ)
    (f : (Fin d → Trunc R N) →ₗ[Trunc R N] Carrier R N l hl)
    (v : Fin d → Trunc R N) (hv : ∀ j, reduction hl (v j) = 0) : f v = 0 := by
  conv_lhs => rw [← (Pi.basisFun (Trunc R N) (Fin d)).sum_repr v]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j _
  change ((Pi.basisFun (Trunc R N) (Fin d)).repr v j) •
    f (Pi.basisFun (Trunc R N) (Fin d) j) = 0
  have hj : (Pi.basisFun (Trunc R N) (Fin d)).repr v j = v j := by simp
  rw [hj, carrier_smul]
  change reduction hl (v j) * (show Trunc R l from f (Pi.basisFun (Trunc R N) (Fin d) j)) = 0
  rw [hv, zero_mul]

omit [IsNoetherianRing R] in
/-- When the sum of the two quotient lengths is at most the ambient length,
any actual map through a projective object is already zero. -/
theorem hom_zero_of_factors {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ N) (hnl : n + l ≤ N)
    (f : truncatedModule R N n hn ⟶ truncatedModule R N l hl)
    (hf : PretriangulatedV2.IdealQuotient.FactorsThrough
      (CategoryTheory.Projective : FGModuleCat (Trunc R N) → Prop) f) : f = 0 := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  have : Projective P := hP
  obtain ⟨d, p, hp⟩ := FiniteModuleCategory.exists_finiteFree_presentation P
  have : Epi p := hp
  let s := Projective.factorThru (𝟙 P) p
  have hs : s ≫ p = 𝟙 P := Projective.factorThru_comp _ _
  let u := a ≫ s
  let g := p ≫ b
  have hu : ∀ j : Fin d, reduction hl (u.hom.hom 1 j) = 0 := by
    intro j
    have hred : reduction (show N - n ≤ N by omega) (u.hom.hom 1 j) = 0 := by
      apply reduction_zero_of_complementary_annihilator
      let c : Trunc R N := x R N ^ n
      have hc : c • (1 : Carrier R N n hn) = 0 := by
        rw [carrier_smul]
        change reduction hn c * 1 = 0
        simp [c]
      have h := u.hom.hom.map_smul c (1 : Carrier R N n hn)
      rw [hc, map_zero] at h
      have hj := congrArg (fun v : Fin d → Trunc R N => v j) h
      change 0 = c * u.hom.hom 1 j at hj
      simpa only [c, show N - (N - n) = n by omega] using hj.symm
    rw [← reduction_comp_apply (show N - n ≤ N by omega)
      (show l ≤ N - n by omega), hred, map_zero]
  have hz := free_to_truncated_vanish R hl d g.hom.hom (u.hom.hom 1) hu
  have heq : u ≫ g = f := by
    dsimp [u, g]
    simp only [← Category.assoc]
    rw [Category.assoc a s p, hs, Category.comp_id, hab]
  apply hom_ext_one hn hl
  change f.hom.hom 1 = 0
  simpa only [heq] using (show (u ≫ g).hom.hom 1 = 0 from hz)

omit [IsNoetherianRing R] in
/-- Multiplication by x^m is an actual nonzero map for positive m. -/
theorem iota₀_nonzero (m : ℕ) (hm : 0 < m) : iota₀ R m ≠ 0 := by
  intro h
  have he := congrArg (fun f : L₀ R m ⟶ M₀ R m => f.hom.hom 1) h
  change iotaRaw R m 1 = 0 at he
  have hp : iotaRaw R m 1 = x R (2 * m) ^ m := by
    simpa using iotaRaw_pow R m 0
  rw [hp] at he
  have hc := congrArg (coefficient (R := R) (2 * m) ⟨m, by omega⟩) he
  simp only [coefficient_pow, map_zero] at hc
  exact one_ne_zero hc

omit [IsNoetherianRing R] in
/-- The actual quotient projection retains one, hence is nonzero. -/
theorem q₀_nonzero (m : ℕ) (hm : 0 < m) : q₀ R m ≠ 0 := by
  let : Nontrivial (Trunc R m) := nontrivial_of_pos m hm
  intro h
  have he := congrArg (fun f : M₀ R m ⟶ L₀ R m =>
    (show Trunc R m from f.hom.hom 1)) h
  change reduction (R := R) (show m ≤ 2 * m by omega) 1 = 0 at he
  rw [map_one] at he
  exact one_ne_zero he

/-- The actual inclusion remains nonzero in the quotient by all projectives. -/
theorem stable_iota₀_nonzero (m : ℕ) (hm : 0 < m) :
    (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map (iota₀ R m) ≠ 0 := by
  intro h
  have hf := (PretriangulatedV2.IdealQuotient.functor_map_eq_zero_iff _ _).mp h
  exact iota₀_nonzero R m hm (hom_zero_of_factors R (by omega) (by omega) (by omega) _ hf)

/-- The actual projection remains nonzero in the quotient by all projectives. -/
theorem stable_q₀_nonzero (m : ℕ) (hm : 0 < m) :
    (projectiveStableQuotient (C := FGModuleCat (algebra R m))).map (q₀ R m) ≠ 0 := by
  intro h
  have hf := (PretriangulatedV2.IdealQuotient.functor_map_eq_zero_iff _ _).mp h
  exact q₀_nonzero R m hm (hom_zero_of_factors R (by omega) (by omega) (by omega) _ hf)

end Noetherian

end PretriangulatedV2.TruncatedStableHom
