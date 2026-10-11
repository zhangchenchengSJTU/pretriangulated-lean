import PretriangulatedV2.IndecomposableSplitting
import PretriangulatedV2.NatTransExtension
import PretriangulatedV2.HomFinite
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
Existence of finite indecomposable decompositions in a Hom-finite additive
category. This proves the generation input needed for Section 6; it does not
assert the uniqueness part of the Krull--Schmidt theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace PretriangulatedV2

universe w v u

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [HasBinaryBiproducts C] [Linear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Diagonal endomorphisms form a linear subspace of the endomorphism space
of an actual biproduct decomposition. -/
def decompositionDiagonal {A B D : C} (e : A ≅ B ⊞ D) :
    ((B ⟶ B) × (D ⟶ D)) →ₗ[k] (A ⟶ A) where
  toFun fg := e.hom ≫ biprod.map fg.1 fg.2 ≫ e.inv
  map_add' x y := by
    dsimp
    apply (cancel_epi e.inv).mp
    apply (cancel_mono e.hom).mp
    ext <;> simp [Category.assoc]
  map_smul' r x := by
    dsimp
    apply (cancel_epi e.inv).mp
    apply (cancel_mono e.hom).mp
    ext <;> simp [Category.assoc]

omit [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
theorem decompositionDiagonal_injective {A B D : C} (e : A ≅ B ⊞ D) :
    Function.Injective (decompositionDiagonal (k := k) e) := by
  intro x y h
  apply Prod.ext
  · have hh := congrArg (fun f : A ⟶ A =>
        (biprod.inl : B ⟶ B ⊞ D) ≫ e.inv ≫ f ≫ e.hom ≫ biprod.fst) h
    simpa [decompositionDiagonal, Category.assoc] using hh
  · have hh := congrArg (fun f : A ⟶ A =>
        (biprod.inr : D ⟶ B ⊞ D) ≫ e.inv ≫ f ≫ e.hom ≫ biprod.snd) h
    simpa [decompositionDiagonal, Category.assoc] using hh

theorem finrank_end_biprod_le {A B D : C} (e : A ≅ B ⊞ D) :
    Module.finrank k (B ⟶ B) + Module.finrank k (D ⟶ D) ≤
      Module.finrank k (A ⟶ A) := by
  simpa only [Module.finrank_prod] using
    LinearMap.finrank_le_finrank_of_injective
      (decompositionDiagonal_injective (k := k) e)

omit [HasBinaryBiproducts C] in
theorem finrank_end_pos_of_not_isZero {A : C} (hA : ¬ IsZero A) :
    0 < Module.finrank k (A ⟶ A) := by
  have hi : (𝟙 A : A ⟶ A) ≠ 0 := by
    intro h
    exact hA ((IsZero.iff_id_eq_zero A).mpr h)
  exact Module.finrank_pos_iff.mpr ⟨⟨𝟙 A, 0, hi⟩⟩

theorem finrank_end_lt_of_nonzero_biprod {A B D : C} (e : A ≅ B ⊞ D)
    (hB : ¬ IsZero B) (hD : ¬ IsZero D) :
    Module.finrank k (B ⟶ B) < Module.finrank k (A ⟶ A) ∧
      Module.finrank k (D ⟶ D) < Module.finrank k (A ⟶ A) := by
  have hle := finrank_end_biprod_le (k := k) e
  have hposB := finrank_end_pos_of_not_isZero (k := k) hB
  have hposD := finrank_end_pos_of_not_isZero (k := k) hD
  constructor <;> omega

include k in
/-- Every object has a finite binary direct-sum decomposition into
indecomposable objects. Existence uses strict descent of endomorphism dimension;
it does not assume a Krull--Schmidt decomposition as input. -/
theorem nonempty_indecomposable_decomposition (A : C) :
    Nonempty (BinaryDecomposition Indecomposable A) := by
  classical
  suffices h : ∀ n : ℕ, ∀ A : C, Module.finrank k (A ⟶ A) = n →
      Nonempty (BinaryDecomposition Indecomposable A) from h _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hn
    by_cases hzero : IsZero A
    · exact ⟨.zero A hzero⟩
    by_cases hi : Indecomposable A
    · exact ⟨.atom A hi⟩
    have hex : ∃ (B D : C) (e : A ≅ B ⊞ D), ¬ IsZero B ∧ ¬ IsZero D := by
      by_contra h
      apply hi
      refine ⟨hzero, ?_⟩
      intro B D e
      by_contra hBD
      apply h
      exact ⟨B, D, e, fun hB => hBD (Or.inl hB), fun hD => hBD (Or.inr hD)⟩
    obtain ⟨B, D, e, hB, hD⟩ := hex
    have hlt := finrank_end_lt_of_nonzero_biprod (k := k) e hB hD
    obtain ⟨dB⟩ := ih (Module.finrank k (B ⟶ B)) (by omega) B rfl
    obtain ⟨dD⟩ := ih (Module.finrank k (D ⟶ D)) (by omega) D rfl
    exact ⟨.iso e (.sum dB dD)⟩

end PretriangulatedV2
