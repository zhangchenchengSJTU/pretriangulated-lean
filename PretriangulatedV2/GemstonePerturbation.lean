import PretriangulatedV2.SupportedCentre

/-!
The explicit obstruction used in Theorem 6.2: the supported perturbation
vanishes on the first two vertices of the rotated gemstone cone, and its
component on the third vertex is nonzero and is not a lightning flash.
This is the contradiction's gemstone side; it does not assume or assert
Proposition 4.2 or the completed Heller classification.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace PretriangulatedV2.Gemstone

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsIdempotentComplete C] {k : Type w} [Field k] [Linear k C]
  [∀ Y Z : C, FiniteDimensional k (Y ⟶ Z)]
  {X : C} (G : Gemstone X)

/-- The paper's natural perturbation `η = u - Id`. -/
def perturbation : 𝟭 C ⟶ 𝟭 C :=
  (G.triangleCenterUnit (k := k)).iso.hom - 𝟙 (𝟭 C)

theorem perturbation_app_self : (G.perturbation (k := k)).app X = G.alpha := by
  change (G.triangleCenterUnit (k := k)).iso.hom.app X - 𝟙 _ = G.alpha
  rw [G.triangleCenterUnit_app_self]
  simp

theorem perturbation_app_double_shift :
    (G.perturbation (k := k)).app (X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) =
      G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' := by
  change (G.triangleCenterUnit (k := k)).iso.hom.app
    (X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) - 𝟙 _ = _
  rw [← (G.triangleCenterUnit (k := k)).commutes (X⟦(1 : ℤ)⟧),
    ← (G.triangleCenterUnit (k := k)).commutes X, G.triangleCenterUnit_app_self]
  simp

variable [Functor.Linear k (shiftFunctor C (1 : ℤ))]

theorem perturbation_app_middle :
    (G.perturbation (k := k)).app G.middle = 0 := by
  change (G.triangleCenterUnit (k := k)).iso.hom.app G.middle - 𝟙 _ = 0
  rw [G.triangleCenterUnit_app_middle]
  exact sub_self _

theorem perturbation_app_cone (K : GemstoneCone G) :
    (G.perturbation (k := k)).app K.Y = 0 := by
  change (G.triangleCenterUnit (k := k)).iso.hom.app K.Y - 𝟙 _ = 0
  rw [G.triangleCenterUnit_app_cone K]
  exact sub_self _

omit [Functor.Linear k (shiftFunctor C (1 : ℤ))] in
theorem perturbation_app_double_shift_nonzero :
    (G.perturbation (k := k)).app (X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) ≠ 0 := by
  rw [G.perturbation_app_double_shift]
  intro h
  apply G.almostVanishing.nonzero
  apply (shiftFunctor C (1 : ℤ)).map_injective
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simpa using h

/-- The actual distinguished triangle used in the contradiction of
Theorem 6.2 has the two zero perturbation components and a third component
which cannot be a lightning flash. -/
theorem exists_perturbation_obstruction :
    ∃ (T : Triangle C), T ∈ distTriang C ∧
      (G.perturbation (k := k)).app T.obj₁ = 0 ∧
      (G.perturbation (k := k)).app T.obj₂ = 0 ∧
      (G.perturbation (k := k)).app T.obj₃ ≠ 0 ∧
      ¬ IsLightningFlash T T ((G.perturbation (k := k)).app T.obj₃) := by
  let K := G.cone (k := k)
  let T := (Triangle.mk K.s K.w K.z).rotate
  refine ⟨T, rot_of_distTriang _ K.distinguished,
    G.perturbation_app_middle, G.perturbation_app_cone K,
    G.perturbation_app_double_shift_nonzero, ?_⟩
  exact G.proposition_5_8_not_lightning (k := k) K _
    G.perturbation_app_double_shift_nonzero

end PretriangulatedV2.Gemstone
