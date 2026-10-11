import PretriangulatedV2.TruncatedPolynomialSymmetry
import PretriangulatedV2.FiniteModuleCategory
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Actual modules over the truncated polynomial algebra

Each shorter polynomial quotient carries the restricted action through the
actual reduction homomorphism. The separate carrier records the ambient
truncation, while its elements remain exactly the quotient-ring elements.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators
namespace PretriangulatedV2.TruncatedModules

open TruncatedPolynomialAlgebra

universe u

variable (R : Type u) [CommRing R]

/-- The actual shorter quotient, with a distinct carrier for its restricted
module structure over the specified larger quotient. -/
def Carrier (N n : ℕ) (_hn : n ≤ N) := Trunc R n

instance carrierCommRing (N n : ℕ) (hn : n ≤ N) : CommRing (Carrier R N n hn) :=
  inferInstanceAs (CommRing (Trunc R n))

instance carrierBaseAlgebra (N n : ℕ) (hn : n ≤ N) : Algebra R (Carrier R N n hn) :=
  inferInstanceAs (Algebra R (Trunc R n))

instance carrierAlgebra (N n : ℕ) (hn : n ≤ N) :
    Algebra (Trunc R N) (Carrier R N n hn) :=
  (reduction (R := R) hn).toRingHom.toAlgebra

@[simp]
theorem carrier_smul (N n : ℕ) (hn : n ≤ N)
    (a : Trunc R N) (b : Carrier R N n hn) :
    a • b = (show Carrier R N n hn from reduction hn a) * b := rfl

instance carrierScalarTower (N n : ℕ) (hn : n ≤ N) :
    IsScalarTower R (Trunc R N) (Carrier R N n hn) :=
  IsScalarTower.of_algebraMap_eq (fun r => (reduction hn).commutes r |>.symm)

instance carrierFinite (N n : ℕ) (hn : n ≤ N) :
    Module.Finite (Trunc R N) (Carrier R N n hn) :=
  Module.Finite.of_surjective (Algebra.linearMap (Trunc R N) (Carrier R N n hn))
    (reduction_surjective hn)

instance carrierBaseFinite (N n : ℕ) (hn : n ≤ N) :
    Module.Finite R (Carrier R N n hn) :=
  inferInstanceAs (Module.Finite R (Trunc R n))

/-- The genuine finitely generated module over the ambient truncated algebra. -/
abbrev truncatedModule (N n : ℕ) (hn : n ≤ N) : FGModuleCat (Trunc R N) :=
  FGModuleCat.of (Trunc R N) (Carrier R N n hn)

variable {R}

/-- Genuine quotient reductions compose, by the polynomial quotient universal
property and their value on the residue class of X. -/
theorem reduction_comp {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ n) :
    (reduction (R := R) hl).comp (reduction hn) = reduction (Nat.le_trans hl hn) := by
  apply AdjoinRoot.algHom_ext
  change reduction hl (reduction hn (x R N)) = reduction (Nat.le_trans hl hn) (x R N)
  simp

@[simp]
theorem reduction_comp_apply {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ n) (a : Trunc R N) :
    reduction hl (reduction hn a) = reduction (Nat.le_trans hl hn) a :=
  congrArg (fun f => f a) (reduction_comp hn hl)

/-- Reduction is linear for the actual restricted ambient scalar actions. -/
def reductionLinear {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ n) :
    Carrier R N n hn →ₗ[Trunc R N] Carrier R N l (Nat.le_trans hl hn) where
  toFun := reduction hl
  map_add' := map_add _
  map_smul' a b := by
    change reduction hl (reduction hn a * (show Trunc R n from b)) =
      reduction (Nat.le_trans hl hn) a * reduction hl (show Trunc R n from b)
    rw [map_mul, reduction_comp_apply]

@[simp]
theorem reductionLinear_apply {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ n)
    (a : Carrier R N n hn) : reductionLinear hn hl a = reduction hl a := rfl

theorem reductionLinear_surjective {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ n) :
    Function.Surjective (reductionLinear (R := R) hn hl) := reduction_surjective hl

/-- The actual quotient morphism in the finitely generated module category. -/
def reductionHom {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ n) :
    truncatedModule R N n hn ⟶ truncatedModule R N l (Nat.le_trans hl hn) :=
  FGModuleCat.ofHom (reductionLinear hn hl)

instance reductionHom_epi {N n l : ℕ} (hn : n ≤ N) (hl : l ≤ n) :
    Epi (reductionHom (R := R) hn hl) := by
  apply Functor.epi_of_epi_map (forget₂ (FGModuleCat (Trunc R N)) (ModuleCat (Trunc R N)))
  exact (ModuleCat.epi_iff_surjective _).mpr (reductionLinear_surjective hn hl)

variable (R)

abbrev algebra (m : ℕ) := Trunc R (3 * m)

/-- The first concrete cyclic module R[x]/(x^m). -/
abbrev L₀ (m : ℕ) : FGModuleCat (algebra R m) :=
  truncatedModule R (3 * m) m (by omega)

/-- The middle concrete cyclic module R[x]/(x^(2m)). -/
abbrev M₀ (m : ℕ) : FGModuleCat (algebra R m) :=
  truncatedModule R (3 * m) (2 * m) (by omega)

/-- The actual projection M₀ → L₀. -/
def q₀ (m : ℕ) : M₀ R m ⟶ L₀ R m :=
  reductionHom (by omega) (by omega)

instance q₀_epi (m : ℕ) : Epi (q₀ R m) := by
  unfold q₀
  infer_instance


section Coordinates

variable [Nontrivial R]

/-- Multiplication by x^m after choosing the canonical polynomial remainder:
the quotient basis vector x^i maps to x^(m+i) in the longer quotient. -/
def iotaRaw (m : ℕ) : Trunc R m →ₗ[R] Trunc R (2 * m) :=
  (basis (R := R) m).constr R (fun i => x R (2 * m) ^ (m + (i : ℕ)))

@[simp]
theorem iotaRaw_basis (m : ℕ) (i : Fin m) :
    iotaRaw R m (x R m ^ (i : ℕ)) = x R (2 * m) ^ (m + (i : ℕ)) := by
  rw [← basis_apply (R := R) m i]
  simp only [iotaRaw, Basis.constr_basis]

theorem iotaRaw_injective (m : ℕ) : Function.Injective (iotaRaw R m) := by
  let j : Fin m → Fin (2 * m) := fun i => ⟨m + (i : ℕ), by omega⟩
  have hj : Function.Injective j := by
    intro i k hik
    apply Fin.ext
    have := congrArg Fin.val hik
    dsimp [j] at this
    omega
  have hli : LinearIndependent R (fun i : Fin m => x R (2 * m) ^ (m + (i : ℕ))) := by
    simpa only [Function.comp_def, basis_apply, j] using
      (basis (R := R) (2 * m)).linearIndependent.comp j hj
  exact (basis (R := R) m).injective_constr_of_linearIndependent hli

/-- Coordinates of the actual shifted quotient element. -/
theorem coefficient_iotaRaw (m : ℕ) (i : Fin (2 * m)) (a : Trunc R m) :
    coefficient (R := R) (2 * m) i (iotaRaw R m a) =
      ∑ j : Fin m, coefficient (R := R) m j a *
        (if m + (j : ℕ) = (i : ℕ) then 1 else 0) := by
  rw [iotaRaw, Basis.constr_apply_fintype]
  simp only [map_sum, map_smul, coefficient_pow, smul_eq_mul]
  simp only [coefficient, Basis.coord_apply, Basis.equivFun_apply]

@[simp]
theorem coefficient_iotaRaw_low (m : ℕ) (i : Fin m) (a : Trunc R m) :
    coefficient (R := R) (2 * m) ⟨i, by omega⟩ (iotaRaw R m a) = 0 := by
  rw [coefficient_iotaRaw]
  apply Finset.sum_eq_zero
  intro j _
  simp only [if_neg (show m + (j : ℕ) ≠ (i : ℕ) by omega), mul_zero]

@[simp]
theorem coefficient_iotaRaw_high (m : ℕ) (i : Fin m) (a : Trunc R m) :
    coefficient (R := R) (2 * m) ⟨m + (i : ℕ), by omega⟩ (iotaRaw R m a) =
      coefficient (R := R) m i a := by
  rw [coefficient_iotaRaw]
  have heq : ∀ j : Fin m, m + (j : ℕ) = m + (i : ℕ) ↔ j = i := by
    intro j
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      subst j
      rfl
  simp only [heq]
  simp

/-- Reduction retains exactly the coordinates below the new cutoff. -/
theorem coefficient_reduction {N n : ℕ} (hn : n ≤ N) (i : Fin n) (a : Trunc R N) :
    coefficient (R := R) n i (reduction hn a) =
      coefficient (R := R) N ⟨i, by omega⟩ a := by
  conv_lhs => rw [← (basis (R := R) N).sum_repr a]
  simp only [map_sum, map_smul, basis_apply, map_pow, reduction_x,
    coefficient_pow, smul_eq_mul]
  have heq : ∀ j : Fin N, (j : ℕ) = (i : ℕ) ↔ j = ⟨i, by omega⟩ := by
    intro j
    constructor
    · intro h
      apply Fin.ext
      exact h
    · intro h
      exact congrArg Fin.val h
  simp only [heq]
  simp [coefficient, Basis.coord_apply]


/-- The shifted map on every monomial, including vanishing high powers. -/
theorem iotaRaw_pow (m t : ℕ) :
    iotaRaw R m (x R m ^ t) = x R (2 * m) ^ (m + t) := by
  by_cases ht : t < m
  · exact iotaRaw_basis R m ⟨t, ht⟩
  · rw [x_pow_eq_zero_of_le (by omega), map_zero,
      x_pow_eq_zero_of_le (by omega)]

@[simp]
theorem reduction_iotaRaw (m : ℕ) (a : Trunc R m) :
    reduction (R := R) (show m ≤ 2 * m by omega) (iotaRaw R m a) = 0 := by
  apply (basis (R := R) m).repr.injective
  ext i
  change coefficient (R := R) m i
    (reduction (show m ≤ 2 * m by omega) (iotaRaw R m a)) =
      coefficient (R := R) m i 0
  rw [coefficient_reduction, coefficient_iotaRaw_low, map_zero]

/-- The range of multiplication by x^m is exactly the kernel of the actual
quotient projection, proved by recovering all higher coordinates. -/
theorem mem_range_iotaRaw_iff (m : ℕ) (a : Trunc R (2 * m)) :
    a ∈ LinearMap.range (iotaRaw R m) ↔
      reduction (R := R) (show m ≤ 2 * m by omega) a = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact reduction_iotaRaw R m b
  · intro ha
    let b : Trunc R m := ∑ j : Fin m,
      coefficient (R := R) (2 * m) ⟨m + (j : ℕ), by omega⟩ a • x R m ^ (j : ℕ)
    have hb : ∀ j : Fin m, coefficient (R := R) m j b =
        coefficient (R := R) (2 * m) ⟨m + (j : ℕ), by omega⟩ a := by
      intro j
      dsimp [b]
      simp only [map_sum, map_smul, coefficient_x_pow, smul_eq_mul]
      simp
    refine ⟨b, ?_⟩
    apply (basis (R := R) (2 * m)).repr.injective
    ext i
    change coefficient (R := R) (2 * m) i (iotaRaw R m b) =
      coefficient (R := R) (2 * m) i a
    by_cases hi : (i : ℕ) < m
    · have hz := congrArg (coefficient (R := R) m ⟨i, hi⟩) ha
      rw [coefficient_reduction, map_zero] at hz
      exact (coefficient_iotaRaw_low R m ⟨i, hi⟩ b).trans hz.symm
    · let j : Fin m := ⟨(i : ℕ) - m, by omega⟩
      have hij : (⟨m + (j : ℕ), by omega⟩ : Fin (2 * m)) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      rw [← hij, coefficient_iotaRaw_high, hb]


/-- The actual shifted quotient map commutes with multiplication by X. -/
theorem iotaRaw_mul_x (m : ℕ) (a : Trunc R m) :
    iotaRaw R m (x R m * a) = x R (2 * m) * iotaRaw R m a := by
  have h : (iotaRaw R m).comp (LinearMap.mul R (Trunc R m) (x R m)) =
      (LinearMap.mul R (Trunc R (2 * m)) (x R (2 * m))).comp (iotaRaw R m) := by
    apply (basis (R := R) m).ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.mul_apply', basis_apply]
    rw [← pow_succ', iotaRaw_pow, iotaRaw_pow, ← pow_succ']
    congr 1
  exact congrArg (fun f => f a) h

theorem iotaRaw_mul_pow (m t : ℕ) (a : Trunc R m) :
    iotaRaw R m (x R m ^ t * a) = x R (2 * m) ^ t * iotaRaw R m a := by
  induction t with
  | zero => simp
  | succ t ht =>
    rw [pow_succ', mul_assoc, iotaRaw_mul_x, ht, ← mul_assoc, ← pow_succ']

/-- The shifted map is linear for the actual ambient quotient action. -/
theorem iotaRaw_reduction_mul (m : ℕ) (a : algebra R m) (b : Trunc R m) :
    iotaRaw R m (reduction (show m ≤ 3 * m by omega) a * b) =
      reduction (show 2 * m ≤ 3 * m by omega) a * iotaRaw R m b := by
  conv_lhs => rw [← (basis (R := R) (3 * m)).sum_repr a]
  conv_rhs => rw [← (basis (R := R) (3 * m)).sum_repr a]
  simp only [map_sum, map_smul, basis_apply, map_pow, reduction_x,
    Finset.sum_mul, Algebra.smul_mul_assoc, iotaRaw_mul_pow]

/-- Multiplication by x^m as an actual A-linear map between the shorter
quotients carrying their restricted module structures. -/
def iotaLinear (m : ℕ) :
    Carrier R (3 * m) m (by omega) →ₗ[algebra R m]
      Carrier R (3 * m) (2 * m) (by omega) where
  toFun := iotaRaw R m
  map_add' := map_add _
  map_smul' a b := iotaRaw_reduction_mul R m a b

/-- The actual inclusion L₀ → M₀ in the finite-module category. -/
def iota₀ (m : ℕ) : L₀ R m ⟶ M₀ R m := FGModuleCat.ofHom (iotaLinear R m)

instance iota₀_mono (m : ℕ) : Mono (iota₀ R m) := by
  apply Functor.mono_of_mono_map (forget₂ (FGModuleCat (algebra R m)) (ModuleCat (algebra R m)))
  exact (ModuleCat.mono_iff_injective _).mpr (iotaRaw_injective R m)

@[simp]
theorem iota₀_q₀ (m : ℕ) : iota₀ R m ≫ q₀ R m = 0 := by
  apply FGModuleCat.hom_ext
  ext a
  exact reduction_iotaRaw R m a

/-- The literal short complex L₀ → M₀ → L₀ of the example. -/
def shortSequence (m : ℕ) : ShortComplex (FGModuleCat (algebra R m)) :=
  ShortComplex.mk (iota₀ R m) (q₀ R m) (iota₀_q₀ R m)

section Noetherian

variable [IsNoetherianRing R]

/-- Its exactness follows from the actual coordinate computation of image and
kernel under the faithful finite-module inclusion. -/
theorem shortSequence_exact (m : ℕ) : (shortSequence R m).Exact := by
  apply ((shortSequence R m).exact_map_iff_of_faithful
    (forget₂ (FGModuleCat (algebra R m)) (ModuleCat (algebra R m)))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  exact (mem_range_iotaRaw_iff R m a).mpr ha

/-- The concrete sequence is genuinely short exact. -/
theorem shortSequence_shortExact (m : ℕ) : (shortSequence R m).ShortExact :=
  { exact := shortSequence_exact R m
    mono_f := inferInstanceAs (Mono (iota₀ R m))
    epi_g := inferInstanceAs (Epi (q₀ R m)) }

end Noetherian

end Coordinates

end PretriangulatedV2.TruncatedModules
