import PretriangulatedV2.StableIdempotents
import PretriangulatedV2.AlmostVanishingSerre

/-! Fitting's alternative in a finite-dimensional, possibly noncommutative
algebra with no nontrivial idempotents. Only the single-element subalgebra is
commutative. This is the form needed for indecomposable endomorphism algebras. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped IsMulCommutative

namespace PretriangulatedV2

universe w v u

variable {k : Type w} [Field k]

include k in
theorem nilpotent_or_isUnit_of_idempotents_trivial
    {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) (a : A) :
    IsNilpotent a ∨ IsUnit a := by
  let B : Subalgebra k A := Algebra.adjoin k ({a} : Set A)
  let x : B := ⟨a, Algebra.self_mem_adjoin_singleton k a⟩
  have : FiniteDimensional k B := inferInstance
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes B x
  let N := n + 1
  have hN : n ≤ N := Nat.le_succ n
  have hNN : n ≤ N + N := hN.trans (Nat.le_add_right N N)
  have hrange :
      LinearMap.range (x ^ N • LinearMap.id : B →ₗ[B] B) =
        LinearMap.range (x ^ (N + N) • LinearMap.id : B →ₗ[B] B) :=
    (hn N hN).symm.trans (hn (N + N) hNN)
  have hmem : x ^ N ∈ LinearMap.range (x ^ N • LinearMap.id : B →ₗ[B] B) :=
    ⟨1, by simp⟩
  rw [hrange] at hmem
  obtain ⟨b, hb⟩ := hmem
  change x ^ (N + N) * b = x ^ N at hb
  have he : IsIdempotentElem (x ^ N * b) := by
    change (x ^ N * b) * (x ^ N * b) = x ^ N * b
    calc
      (x ^ N * b) * (x ^ N * b) = (x ^ N * x ^ N * b) * b := by ring
      _ = x ^ N * b := by rw [← pow_add, hb]
  rcases hidem _ (he.map B.subtype.toMonoidHom) with hzero | hone
  · left
    have hzero' : x ^ N * b = 0 := Subtype.ext hzero
    have hxzero : x ^ N = 0 := by
      rw [← hb, pow_add, mul_assoc, hzero', mul_zero]
    refine ⟨N, ?_⟩
    simpa only [Subalgebra.coe_pow, Subalgebra.coe_zero] using
      congrArg (fun z : B => (z : A)) hxzero
  · right
    have hone' : x ^ N * b = 1 := Subtype.ext hone
    have hunit : IsUnit x := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨x ^ n * b, ?_⟩
      simpa only [N, pow_succ, mul_assoc, mul_left_comm x] using hone'
    exact hunit.map B.subtype.toMonoidHom

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasBinaryBiproducts C] [IsIdempotentComplete C]

include k in
theorem end_nilpotent_or_isUnit {X : C} [FiniteDimensional k (X ⟶ X)]
    (hX : Indecomposable X) (a : End X) : IsNilpotent a ∨ IsUnit a := by
  have : FiniteDimensional k (End X) :=
    inferInstanceAs (FiniteDimensional k (X ⟶ X))
  exact nilpotent_or_isUnit_of_idempotents_trivial (k := k)
    (AlmostVanishingSerre.idempotent_eq_zero_or_one hX) a

end PretriangulatedV2
