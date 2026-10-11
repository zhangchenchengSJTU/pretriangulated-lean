import PretriangulatedV2.TruncatedPolynomialAlgebra
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Coefficient computations for the actual truncated quotient. The top
coefficient of a complementary monomial product isolates a chosen coefficient;
this gives the symmetric trace needed for the concrete module category.
-/

noncomputable section

open Module
open scoped BigOperators

namespace PretriangulatedV2.TruncatedPolynomialAlgebra

universe u w

variable {R : Type u} [CommRing R] [Nontrivial R]

omit [Nontrivial R] in
theorem x_pow_eq_zero_of_le {n t : ℕ} (hnt : n ≤ t) : x R n ^ t = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hnt
  rw [pow_add, x_pow, zero_mul]

/-- The coordinate formula also covers powers beyond the truncation length. -/
theorem coefficient_pow (n : ℕ) (i : Fin n) (t : ℕ) :
    coefficient (R := R) n i (x R n ^ t) = if t = (i : ℕ) then 1 else 0 := by
  by_cases ht : t < n
  · simpa only [Fin.ext_iff, Fin.val_mk] using
      coefficient_x_pow (R := R) n i ⟨t, ht⟩
  · have hi : t ≠ (i : ℕ) := by omega
    rw [x_pow_eq_zero_of_le (by omega), map_zero, if_neg hi]

/-- Multiplying a quotient element by a monomial and taking a coordinate. -/
theorem coefficient_mul_pow (n : ℕ) (i : Fin n) (a : Trunc R n) (t : ℕ) :
    coefficient (R := R) n i (a * x R n ^ t) =
      ∑ j : Fin n, coefficient (R := R) n j a *
        (if (j : ℕ) + t = (i : ℕ) then 1 else 0) := by
  conv_lhs => rw [← (basis (R := R) n).sum_repr a]
  simp only [Finset.sum_mul, basis_apply, Algebra.smul_mul_assoc, ← pow_add,
    map_sum, map_smul, coefficient_pow, smul_eq_mul]
  rfl

/-- A complementary monomial detects exactly one coefficient of `a`. -/
theorem coefficient_mul_complement (n : ℕ) (hn : 0 < n) (i : Fin n)
    (a : Trunc R n) :
    coefficient (R := R) n ⟨n - 1, by omega⟩
      (a * x R n ^ (n - 1 - (i : ℕ))) = coefficient (R := R) n i a := by
  rw [coefficient_mul_pow]
  have heq : ∀ j : Fin n,
      (j : ℕ) + (n - 1 - (i : ℕ)) = n - 1 ↔ j = i := by
    intro j
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      subst j
      omega
  simp only [heq]
  simp

section Trace

variable {k : Type w} [Field k] [Algebra k R]

/-- The trace on a truncation obtained from its top coefficient. -/
def traceOfCoefficients (τ : R →ₗ[k] k) (n : ℕ) (hn : 0 < n) : Trunc R n →ₗ[k] k :=
  τ.comp ((coefficient (R := R) n ⟨n - 1, by omega⟩).restrictScalars k)

/-- A scalar complementary monomial tests the original trace on any desired
coefficient. -/
theorem traceOfCoefficients_mul_complement (τ : R →ₗ[k] k)
    (n : ℕ) (hn : 0 < n) (i : Fin n) (a : Trunc R n) (c : R) :
    traceOfCoefficients τ n hn (a * (c • x R n ^ (n - 1 - (i : ℕ)))) =
      τ (coefficient (R := R) n i a * c) := by
  simp only [traceOfCoefficients, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Algebra.mul_smul_comm, map_smul, smul_eq_mul]
  rw [coefficient_mul_complement n hn i a, mul_comm c]

/-- Nondegeneracy of the coefficient trace is proved on the actual quotient,
using complementary monomials for every basis coordinate. -/
theorem traceOfCoefficients_nondegenerate (τ : R →ₗ[k] k)
    (hτ : ∀ a : R, (∀ b : R, τ (a * b) = 0) → a = 0)
    (n : ℕ) (hn : 0 < n) (a : Trunc R n)
    (ha : ∀ b : Trunc R n, traceOfCoefficients τ n hn (a * b) = 0) : a = 0 := by
  apply (basis (R := R) n).repr.injective
  ext i
  have hi : coefficient (R := R) n i a = 0 := by
    apply hτ
    intro c
    rw [← traceOfCoefficients_mul_complement τ n hn i a c]
    exact ha _
  simpa only [coefficient, Basis.coord_apply, map_zero, Finsupp.zero_apply] using hi

end Trace

end PretriangulatedV2.TruncatedPolynomialAlgebra
