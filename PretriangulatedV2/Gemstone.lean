import PretriangulatedV2.AlmostVanishing
import PretriangulatedV2.HomFinite

/-!
Definition 5.3 of arXiv:2608.09777v2, using mathlib's actual triangles.
`X⟦1⟧⟦1⟧` denotes the iterated suspension Σ²X. The choice of an
almost-split triangle is retained explicitly, rather than hiding its existence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace PretriangulatedV2

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- The right almost-split triangle definition in the opening of Section 5. -/
def IsAlmostSplitTriangle (T : Triangle C) : Prop :=
  T ∈ distTriang C ∧ Indecomposable T.obj₁ ∧ Indecomposable T.obj₃ ∧
    T.mor₃ ≠ 0 ∧
    ∀ {W : C} (t : W ⟶ T.obj₃), ¬ IsSplitEpi t →
      ∃ p : W ⟶ T.obj₂, t = p ≫ T.mor₂

/-- Gemstone data, including all three conditions (G1), (G2), (G3).
This definition alone does not construct a gemstone. -/
structure Gemstone (X : C) where
  indecomposable : Indecomposable X
  periodicity : X ≅ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧
  rigid : ∀ f : X ⟶ X⟦(1 : ℤ)⟧, f = 0
  alpha : X ⟶ X
  almostVanishing : IsAlmostVanishing alpha
  not_isIso : ¬ IsIso alpha
  central : ∀ f : X ⟶ X, alpha ≫ f = f ≫ alpha
  compatible : alpha ≫ periodicity.hom =
    periodicity.hom ≫ alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧'
  middle : C
  first : X ⟶ middle
  second : middle ⟶ X⟦(1 : ℤ)⟧
  almostSplit : IsAlmostSplitTriangle
    (Triangle.mk first second ((shiftFunctor C (1 : ℤ)).map alpha))
  middle_not_periodic : ¬ Nonempty (middle ≅ middle⟦(1 : ℤ)⟧)

namespace Gemstone

variable {X : C} (G : Gemstone X)

include G

/-- Remark 5.4(1): rigidity also holds in the other direction. -/
theorem reverse_rigid (f : X⟦(1 : ℤ)⟧ ⟶ X) : f = 0 := by
  have h := G.rigid (G.periodicity.hom ≫ f⟦(1 : ℤ)⟧')
  have hf : f⟦(1 : ℤ)⟧' = 0 := by
    apply (cancel_epi G.periodicity.hom).mp
    simpa using h
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simpa using hf

/-- The exact triangle appearing in (G3). -/
def triangle : Triangle C :=
  Triangle.mk G.first G.second ((shiftFunctor C (1 : ℤ)).map G.alpha)

theorem triangle_distinguished : G.triangle ∈ distTriang C := G.almostSplit.1

variable {k : Type w} [Field k] [Linear k C] [FiniteDimensional k (X ⟶ X)]

include k

/-- Remark 5.4(3), with the finite dimensional step fully justified. -/
theorem alpha_sq_eq_zero : G.alpha ≫ G.alpha = 0 := by
  exact G.almostVanishing.endomorphism_sq_eq_zero
    (not_isSplitMono_of_not_isIso (k := k) G.alpha G.not_isIso)

theorem shifted_alpha_sq_eq_zero :
    G.alpha⟦(1 : ℤ)⟧' ≫ G.alpha⟦(1 : ℤ)⟧' = 0 := by
  rw [← Functor.map_comp, G.alpha_sq_eq_zero (k := k), Functor.map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Equation (5.2): the shifted almost-vanishing map factors through `v`.
The factor is nonzero, as required before constructing triangle (5.3). -/
theorem exists_nonzero_factor :
    ∃ s : X⟦(1 : ℤ)⟧ ⟶ G.middle,
      s ≫ G.second = G.alpha⟦(1 : ℤ)⟧' ∧ s ≠ 0 := by
  obtain ⟨s, hs⟩ := G.triangle.coyoneda_exact₃ G.triangle_distinguished
    ((shiftFunctor C (1 : ℤ)).map G.alpha) (G.shifted_alpha_sq_eq_zero (k := k))
  change (shiftFunctor C (1 : ℤ)).map G.alpha = s ≫ G.second at hs
  refine ⟨s, hs.symm, ?_⟩
  intro hzero
  have hmap : G.alpha⟦(1 : ℤ)⟧' = 0 := by
    calc
      G.alpha⟦(1 : ℤ)⟧' = s ≫ G.second := hs
      _ = (0 : X⟦(1 : ℤ)⟧ ⟶ G.middle) ≫ G.second := by rw [hzero]
      _ = 0 := zero_comp
  apply G.almostVanishing.nonzero
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simpa using hmap

end Gemstone

end PretriangulatedV2
