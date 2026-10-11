import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Finite-dimensional consequences of the Hom exact sequences attached to a distinguished
triangle.  These are the linear-algebra ingredients used in Lemma 5.5 of
arXiv:2608.09777v2.

The additive-shift hypothesis is explicit: it is required by mathlib's definition of a
pretriangulated category, and it is used by the exactness theorem for the shifted Hom term.
-/

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits FiniteDimensional

namespace PretriangulatedV2

universe w v u

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- A split monomorphism is injective after applying `Hom(W, -)`, hence cannot lower the
finite dimension of that Hom space. -/
theorem finrank_hom_le_of_isSplitMono {W X Y : C} (f : X ⟶ Y) [IsSplitMono f]
    [FiniteDimensional k (W ⟶ Y)] :
    Module.finrank k (W ⟶ X) ≤ Module.finrank k (W ⟶ Y) := by
  refine LinearMap.finrank_le_finrank_of_injective (f := Linear.rightComp k W f) ?_
  intro a b hab
  change a ≫ f = b ≫ f at hab
  exact (cancel_mono f).mp hab

/-- A strict dimension drop on a single represented Hom space rules out a split
monomorphism. -/
theorem not_isSplitMono_of_finrank_hom_lt {W X Y : C} (f : X ⟶ Y)
    [FiniteDimensional k (W ⟶ Y)]
    (h : Module.finrank k (W ⟶ Y) < Module.finrank k (W ⟶ X)) : ¬ IsSplitMono f := by
  intro hf
  let _ := hf
  exact (not_lt_of_ge (finrank_hom_le_of_isSplitMono (k := k) f)) h

/-- If one represented Hom space is strictly smaller at `Y` than at `X`, no morphism
`X ⟶ Y` can exhibit `X` as a retract of `Y`. -/
theorem forall_not_isSplitMono_of_finrank_hom_lt {W X Y : C}
    [FiniteDimensional k (W ⟶ Y)]
    (h : Module.finrank k (W ⟶ Y) < Module.finrank k (W ⟶ X)) :
    ∀ f : X ⟶ Y, ¬ IsSplitMono f :=
  fun f ↦ not_isSplitMono_of_finrank_hom_lt (k := k) f h

variable [HasShift C ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]

/-- Shifting both arguments by one gives a *linear* equivalence of Hom spaces.
The `Functor.Linear` hypothesis is essential here: additivity of the shift alone does not
make this an equivalence of `k`-vector spaces. -/
def shiftHomLinearEquiv (X Y : C) [Functor.Linear k (shiftFunctor C (1 : ℤ))] :
    (X ⟶ Y) ≃ₗ[k] (X⟦(1 : ℤ)⟧ ⟶ Y⟦(1 : ℤ)⟧) :=
  LinearEquiv.ofBijective ((shiftFunctor C (1 : ℤ)).mapLinearMap k)
    ⟨(shiftFunctor C (1 : ℤ)).map_injective, (shiftFunctor C (1 : ℤ)).map_surjective⟩

@[simp]
theorem shiftHomLinearEquiv_apply (X Y : C) [Functor.Linear k (shiftFunctor C (1 : ℤ))]
    (f : X ⟶ Y) : shiftHomLinearEquiv (k := k) X Y f = f⟦(1 : ℤ)⟧' :=
  rfl

/-- The finite-dimensional equality used in the first line of the proof of Lemma 5.5:
shifting both source and target preserves the Hom dimension, provided that the shift is
`k`-linear. -/
theorem finrank_hom_shift_eq (X Y : C) [Functor.Linear k (shiftFunctor C (1 : ℤ))] :
    Module.finrank k (X ⟶ Y) = Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ Y⟦(1 : ℤ)⟧) :=
  (shiftHomLinearEquiv (k := k) X Y).finrank_eq

theorem finrank_end_shift_eq (X : C) [Functor.Linear k (shiftFunctor C (1 : ℤ))] :
    Module.finrank k (X ⟶ X) = Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧) :=
  finrank_hom_shift_eq (k := k) X X

/-- The rank-nullity calculation underlying Lemma 5.5(1).  The two linear
equivalences make every needed dimension identification explicit. -/
theorem finrank_eq_of_surjective_of_injective_of_ker_equiv
    {V₁ V₂ V₃ V₄ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
    [AddCommGroup V₃] [AddCommGroup V₄] [Module k V₁] [Module k V₂]
    [Module k V₃] [Module k V₄] [FiniteDimensional k V₁] [FiniteDimensional k V₄]
    (a : V₁ →ₗ[k] V₂) (ha : Function.Surjective a)
    (b : V₃ →ₗ[k] V₄) (hb : Function.Injective b)
    (c : V₄ →ₗ[k] V₄) (e₁₄ : V₁ ≃ₗ[k] V₄)
    (eker : LinearMap.ker a ≃ₗ[k] LinearMap.range c)
    (hrange : LinearMap.range b = LinearMap.ker c) :
    Module.finrank k V₂ = Module.finrank k V₃ := by
  have harank := a.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 ha, finrank_top] at harank
  have hbrank := LinearMap.finrank_range_of_inj hb
  have hcrank := c.finrank_range_add_finrank_ker
  rw [← hrange] at hcrank
  have h₁₄ := e₁₄.finrank_eq
  have hker := eker.finrank_eq
  omega

variable [HasZeroObject C] [Pretriangulated C]

/-- If the two adjacent Hom spaces vanish, the middle morphism of a distinguished
triangle induces an isomorphism on Hom spaces. -/
def rightCompMor₂LinearEquiv {T : Triangle C} (hT : T ∈ distTriang C) (W : C)
    (h₁ : ∀ f : W ⟶ T.obj₁, f = 0) (h₁shift : ∀ f : W ⟶ T.obj₁⟦(1 : ℤ)⟧, f = 0) :
    (W ⟶ T.obj₂) ≃ₗ[k] (W ⟶ T.obj₃) :=
  LinearEquiv.ofBijective (Linear.rightComp k W T.mor₂) (by
    constructor
    · intro f g hfg
      have hzero : (f - g) ≫ T.mor₂ = 0 := by
        simpa only [Linear.rightComp_apply, CategoryTheory.Preadditive.sub_comp] using
          sub_eq_zero.mpr hfg
      obtain ⟨q, hq⟩ := T.coyoneda_exact₂ hT (f - g) hzero
      rw [h₁ q, zero_comp] at hq
      exact sub_eq_zero.mp hq
    · intro f
      obtain ⟨q, hq⟩ := T.coyoneda_exact₃ hT f (by
        rw [h₁shift (f ≫ T.mor₃)])
      exact ⟨q, hq.symm⟩)

@[simp]
theorem rightCompMor₂LinearEquiv_apply {T : Triangle C} (hT : T ∈ distTriang C) (W : C)
    (h₁ : ∀ f : W ⟶ T.obj₁, f = 0) (h₁shift : ∀ f : W ⟶ T.obj₁⟦(1 : ℤ)⟧, f = 0)
    (f : W ⟶ T.obj₂) : rightCompMor₂LinearEquiv (k := k) hT W h₁ h₁shift f = f ≫ T.mor₂ :=
  rfl

/-- A nonzero first morphism makes the Hom space at the second vertex strictly larger
than that at the third vertex whenever the shifted first Hom space vanishes. -/
theorem finrank_hom_obj₃_lt_hom_obj₂_of_mor₁_ne_zero {T : Triangle C}
    (hT : T ∈ distTriang C) (hshift : ∀ f : T.obj₁ ⟶ T.obj₁⟦(1 : ℤ)⟧, f = 0)
    (h₁ : T.mor₁ ≠ 0) [FiniteDimensional k (T.obj₁ ⟶ T.obj₂)]
    [FiniteDimensional k (T.obj₁ ⟶ T.obj₃)] :
    Module.finrank k (T.obj₁ ⟶ T.obj₃) < Module.finrank k (T.obj₁ ⟶ T.obj₂) := by
  let L := Linear.rightComp k T.obj₁ T.mor₂
  have hsurj : Function.Surjective L := by
    intro f
    obtain ⟨q, hq⟩ := T.coyoneda_exact₃ hT f (by
      rw [hshift (f ≫ T.mor₃)])
    exact ⟨q, hq.symm⟩
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hmem : T.mor₁ ∈ LinearMap.ker L := by
      simp [L, comp_distTriang_mor_zero₁₂ T hT]
    have : T.mor₁ = 0 := by simpa [hbot] using hmem
    exact h₁ this
  have hker_pos : 0 < Module.finrank k (LinearMap.ker L) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hker_ne (Submodule.finrank_eq_zero.mp hzero)
  have hrank := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrank
  omega

/-- A nonzero connecting morphism prevents the preceding Hom map from being surjective;
combined with exactness at the second vertex, this gives the reverse strict inequality. -/
theorem finrank_hom_obj₂_lt_end_obj₃_of_mor₃_ne_zero {T : Triangle C}
    (hT : T ∈ distTriang C) (h₁ : ∀ f : T.obj₃ ⟶ T.obj₁, f = 0) (h₃ : T.mor₃ ≠ 0)
    [FiniteDimensional k (T.obj₃ ⟶ T.obj₂)] [FiniteDimensional k (T.obj₃ ⟶ T.obj₃)] :
    Module.finrank k (T.obj₃ ⟶ T.obj₂) < Module.finrank k (T.obj₃ ⟶ T.obj₃) := by
  let L := Linear.rightComp k T.obj₃ T.mor₂
  have hinj : Function.Injective L := by
    intro f g hfg
    have hzero : (f - g) ≫ T.mor₂ = 0 := by
      simpa only [L, Linear.rightComp_apply, CategoryTheory.Preadditive.sub_comp] using
        sub_eq_zero.mpr hfg
    obtain ⟨q, hq⟩ := T.coyoneda_exact₂ hT (f - g) hzero
    rw [h₁ q, zero_comp] at hq
    exact sub_eq_zero.mp hq
  have hnot_surj : ¬ Function.Surjective L := by
    intro hsurj
    obtain ⟨q, hq⟩ := hsurj (𝟙 T.obj₃)
    change q ≫ T.mor₂ = 𝟙 T.obj₃ at hq
    have : T.mor₃ = 0 := by
      calc
        T.mor₃ = (𝟙 T.obj₃) ≫ T.mor₃ := (Category.id_comp _).symm
        _ = (q ≫ T.mor₂) ≫ T.mor₃ := by rw [hq]
        _ = q ≫ (T.mor₂ ≫ T.mor₃) := Category.assoc _ _ _
        _ = 0 := by rw [comp_distTriang_mor_zero₂₃ T hT, comp_zero]
    exact h₃ this
  have hrange_lt : LinearMap.range L < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro hrange
    exact hnot_surj (LinearMap.range_eq_top.mp hrange)
  have hfinrank_lt := Submodule.finrank_lt_finrank_of_lt hrange_lt
  rw [LinearMap.finrank_range_of_inj hinj, finrank_top] at hfinrank_lt
  exact hfinrank_lt

end PretriangulatedV2
