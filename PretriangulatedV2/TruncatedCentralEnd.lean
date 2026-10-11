import PretriangulatedV2.FiniteModuleCentre
import PretriangulatedV2.TruncatedStableHom

/-! The actual central diagonal condition in Example 7.2: every stable
endomorphism of M₀ lifts to multiplication by a ring element on all modules. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.TruncatedCentralEnd

open TruncatedPolynomialAlgebra TruncatedModules TruncatedStableHom
open StableCategory FiniteModuleCategory

universe u

variable (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R]

abbrev Q (m : ℕ) := projectiveStableQuotient (C := FGModuleCat (algebra R m))
abbrev M (m : ℕ) := (Q R m).obj (M₀ R m)
abbrev L (m : ℕ) := (Q R m).obj (L₀ R m)

/-- The computed stable endomorphism equivalence sends genuine scalar
multiplication to the actual quotient reduction. -/
theorem stableEnd_scalar (m : ℕ) (a : algebra R m) :
    stableEndRingEquiv R m (stableScalarEnd a (M R m)) =
      reduction (show m ≤ 3 * m by omega) a := by
  change stableEndValueHom R m (stableEndProjection R m (scalarEnd a (M₀ R m))) = _
  rw [stableEndValueHom_map, endReductionHom_apply]
  change reduction (show m ≤ 2 * m by omega)
    (reduction (show 2 * m ≤ 3 * m by omega) a * 1) = _
  rw [mul_one, reduction_comp_apply]

/-- Every stable endomorphism of M₀ is the restriction of an actual central
endomorphism of M₀ ⊞ L₀. No centrality or endomorphism-surjectivity hypothesis
is supplied: both come from the ring action and the computed stable End. -/
theorem exists_central_diagonal (m : ℕ) (a : End (M R m)) :
    ∃ c : End (M R m ⊞ L R m),
      (∀ z : End (M R m ⊞ L R m), c * z = z * c) ∧
      (biprod.inl : M R m ⟶ M R m ⊞ L R m) ≫ c ≫ biprod.fst = a := by
  obtain ⟨b, hb⟩ := reduction_surjective (R := R)
    (show m ≤ 3 * m by omega) (stableEndRingEquiv R m a)
  refine ⟨stableScalarEnd b (M R m ⊞ L R m), stableScalar_central b _, ?_⟩
  change (biprod.inl : M R m ⟶ M R m ⊞ L R m) ≫
    (stableScalar b).app (M R m ⊞ L R m) ≫ biprod.fst = a
  rw [stableScalar_restrict]
  apply (stableEndRingEquiv R m).injective
  exact (stableEnd_scalar R m b).trans hb

end PretriangulatedV2.TruncatedCentralEnd
