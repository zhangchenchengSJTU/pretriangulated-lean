import PretriangulatedV2.TruncatedPolynomialSymmetry
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Field.IsField

/-!
Locality and failure to be a field for the actual quotient R[x]/(x^n).
The augmentation has nilpotent kernel, proved by the actual monomial basis.
-/

noncomputable section

open Polynomial Module
open scoped BigOperators

namespace PretriangulatedV2.TruncatedPolynomialLocal

theorem isUnit_iff_isUnit_augmentation
    {A R : Type*} [CommRing A] [CommRing R]
    (φ : A →+* R) (ι : R →+* A)
    (hsection : ∀ r : R, φ (ι r) = r)
    (hnil : ∀ a : A, φ a = 0 → IsNilpotent a)
    (a : A) : IsUnit a ↔ IsUnit (φ a) := by
  constructor
  · intro ha
    exact ha.map φ
  · intro ha
    have hnil' : IsNilpotent (a - ι (φ a)) := hnil _ (by
      rw [map_sub, hsection, sub_self])
    rw [← sub_add_cancel a (ι (φ a)), add_comm]
    exact hnil'.isUnit_add_left_of_commute (ha.map ι) (Commute.all _ _)

theorem isLocalRing_of_isLocalRing_augmentation
    {A R : Type*} [CommRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (ι : R →+* A)
    (hsection : ∀ r : R, φ (ι r) = r)
    (hnil : ∀ a : A, φ a = 0 → IsNilpotent a) : IsLocalRing A := by
  have : Nontrivial A := φ.domain_nontrivial
  refine IsLocalRing.of_is_unit_or_is_unit_of_add_one ?_
  intro a b hab
  have hab' : φ a + φ b = 1 := by
    rw [← φ.map_add, hab, φ.map_one]
  obtain ha | hb := IsLocalRing.isUnit_or_isUnit_of_add_one hab'
  · exact Or.inl ((isUnit_iff_isUnit_augmentation φ ι hsection hnil a).mpr ha)
  · exact Or.inr ((isUnit_iff_isUnit_augmentation φ ι hsection hnil b).mpr hb)

theorem not_isField_of_nonzero_nilpotent
    {A : Type*} [CommRing A] [Nontrivial A] {x : A}
    (hx : x ≠ 0) (hnil : IsNilpotent x) : ¬ IsField A := by
  intro hfield
  let : Field A := hfield.toField
  exact hx (isNilpotent_iff_eq_zero.mp hnil)

end PretriangulatedV2.TruncatedPolynomialLocal

namespace PretriangulatedV2.TruncatedPolynomialAlgebra

universe u

variable {R : Type u} [CommRing R]

/-- Evaluation at zero, constructed from the genuine quotient relation. -/
def augmentation (n : ℕ) (hn : 0 < n) : Trunc R n →ₐ[R] R :=
  AdjoinRoot.liftAlgHom (X ^ n : R[X]) (Algebra.ofId R R) 0 (by
    simp only [eval₂_pow, eval₂_X, zero_pow (by omega : n ≠ 0)])

@[simp] theorem augmentation_x (n : ℕ) (hn : 0 < n) :
    augmentation (R := R) n hn (x R n) = 0 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp] theorem augmentation_algebraMap (n : ℕ) (hn : 0 < n) (r : R) :
    augmentation (R := R) n hn (algebraMap R (Trunc R n) r) = r :=
  AlgHom.commutes _ _

theorem augmentation_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (augmentation (R := R) n hn) := by
  intro r
  exact ⟨algebraMap R (Trunc R n) r, augmentation_algebraMap n hn r⟩

/-- A positive-length truncation retains the constants faithfully. -/
instance nontrivial [Nontrivial R] (n : ℕ) [Fact (0 < n)] : Nontrivial (Trunc R n) :=
  (augmentation_surjective (R := R) n (Fact.out)).nontrivial

theorem nontrivial_of_pos [Nontrivial R] (n : ℕ) (hn : 0 < n) : Nontrivial (Trunc R n) :=
  (augmentation_surjective (R := R) n hn).nontrivial

section Nontrivial

variable [Nontrivial R]

/-- Augmentation is exactly the ordinary constant coefficient. -/
theorem augmentation_eq_coefficient_zero (n : ℕ) (hn : 0 < n) (a : Trunc R n) :
    augmentation (R := R) n hn a = coefficient (R := R) n ⟨0, hn⟩ a := by
  calc
    augmentation (R := R) n hn a =
        ∑ i : Fin n, coefficient (R := R) n i a * (0 : R) ^ (i : ℕ) := by
      conv_lhs => rw [← (basis (R := R) n).sum_repr a]
      simp only [map_sum, map_smul, basis_apply, map_pow, augmentation_x,
        coefficient, Basis.coord_apply, smul_eq_mul]
    _ = coefficient (R := R) n ⟨0, hn⟩ a := by
      rw [Finset.sum_eq_single ⟨0, hn⟩]
      · simp
      · intro i _ hi
        have hi' : (i : ℕ) ≠ 0 := by
          intro h
          apply hi
          exact Fin.ext h
        simp [zero_pow hi']
      · simp

/-- Shift every monomial coefficient down one degree. Its constant term is
irrelevant when this is used to factor a zero-augmentation element. -/
def coefficientTail (n : ℕ) (a : Trunc R n) : Trunc R n :=
  ∑ i : Fin n, coefficient (R := R) n i a • x R n ^ ((i : ℕ) - 1)

/-- Every zero-augmentation element is actually divisible by the variable. -/
theorem x_mul_coefficientTail (n : ℕ) (hn : 0 < n) (a : Trunc R n)
    (ha : augmentation (R := R) n hn a = 0) : x R n * coefficientTail n a = a := by
  have hc : coefficient (R := R) n ⟨0, hn⟩ a = 0 := by
    rw [← augmentation_eq_coefficient_zero n hn a]
    exact ha
  conv_rhs => rw [← (basis (R := R) n).sum_repr a]
  rw [coefficientTail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change x R n * (coefficient n i a • x R n ^ ((i : ℕ) - 1)) =
    coefficient n i a • basis (R := R) n i
  by_cases hi : (i : ℕ) = 0
  · have he : i = ⟨0, hn⟩ := Fin.ext hi
    simp [he, hc]
  · rw [basis_apply, Algebra.mul_smul_comm, ← pow_succ']
    congr 2
    omega

/-- The whole augmentation kernel is nilpotent, with the uniform exponent n. -/
theorem pow_eq_zero_of_augmentation_eq_zero (n : ℕ) (hn : 0 < n) (a : Trunc R n)
    (ha : augmentation (R := R) n hn a = 0) : a ^ n = 0 := by
  rw [← x_mul_coefficientTail n hn a ha, mul_pow, x_pow, zero_mul]

theorem isNilpotent_of_augmentation_eq_zero (n : ℕ) (hn : 0 < n) (a : Trunc R n)
    (ha : augmentation (R := R) n hn a = 0) : IsNilpotent a :=
  ⟨n, pow_eq_zero_of_augmentation_eq_zero n hn a ha⟩

/-- At length at least two the variable is an actual nonzero element. -/
theorem x_ne_zero (n : ℕ) (hn : 2 ≤ n) : x R n ≠ 0 := by
  intro hx
  have hc := coefficient_pow (R := R) n ⟨1, by omega⟩ 1
  rw [pow_one, hx, map_zero] at hc
  simp at hc

omit [Nontrivial R] in
/-- The variable itself is nilpotent in the actual polynomial quotient. -/
theorem x_isNilpotent (n : ℕ) : IsNilpotent (x R n) := ⟨n, x_pow R n⟩

omit [Nontrivial R] in
/-- Positive-length augmentation sends units to units by its actual ring map. -/
theorem isUnit_augmentation_of_isUnit (n : ℕ) (hn : 0 < n) (a : Trunc R n)
    (ha : IsUnit a) : IsUnit (augmentation (R := R) n hn a) :=
  ha.map (augmentation (R := R) n hn).toRingHom

/-- A quotient element is invertible exactly when its constant coefficient is. -/
theorem isUnit_iff_augmentation (n : ℕ) (hn : 0 < n) (a : Trunc R n) :
    IsUnit a ↔ IsUnit (augmentation (R := R) n hn a) :=
  TruncatedPolynomialLocal.isUnit_iff_isUnit_augmentation
    (augmentation (R := R) n hn).toRingHom (algebraMap R (Trunc R n))
    (augmentation_algebraMap n hn) (isNilpotent_of_augmentation_eq_zero n hn) a

theorem isUnit_iff_coefficient_zero (n : ℕ) (hn : 0 < n) (a : Trunc R n) :
    IsUnit a ↔ IsUnit (coefficient (R := R) n ⟨0, hn⟩ a) := by
  rw [isUnit_iff_augmentation n hn a, augmentation_eq_coefficient_zero]

end Nontrivial

/-- A positive-length actual truncated polynomial quotient of a commutative
local ring is itself a local ring. -/
theorem isLocalRing [IsLocalRing R] (n : ℕ) (hn : 0 < n) : IsLocalRing (Trunc R n) := by
  have : Nontrivial R := IsLocalRing.toNontrivial
  exact TruncatedPolynomialLocal.isLocalRing_of_isLocalRing_augmentation
    (augmentation (R := R) n hn).toRingHom (algebraMap R (Trunc R n))
    (augmentation_algebraMap n hn) (isNilpotent_of_augmentation_eq_zero n hn)

instance localRing [IsLocalRing R] (n : ℕ) [Fact (0 < n)] : IsLocalRing (Trunc R n) :=
  isLocalRing n Fact.out

section Nontrivial

variable [Nontrivial R]

/-- For length at least two, the actual nonzero nilpotent variable prevents
the quotient ring from being a field. -/
theorem not_isField (n : ℕ) (hn : 2 ≤ n) : ¬ IsField (Trunc R n) := by
  have : Nontrivial (Trunc R n) := nontrivial_of_pos n (by omega)
  exact TruncatedPolynomialLocal.not_isField_of_nonzero_nilpotent
    (x_ne_zero n hn) (x_isNilpotent n)

theorem x_not_isUnit (n : ℕ) (hn : 0 < n) : ¬ IsUnit (x R n) := by
  have : Nontrivial (Trunc R n) := nontrivial_of_pos n hn
  exact (x_isNilpotent n).not_isUnit

end Nontrivial

end PretriangulatedV2.TruncatedPolynomialAlgebra
