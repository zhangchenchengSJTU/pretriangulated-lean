import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.EpiMono
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Finite dimensional endomorphism spaces make every split endomorphism invertible.
This supplies the finite dimensional justification used in Section 5 of
arXiv:2608.09777v2 when a section endomorphism is called an automorphism.
-/

noncomputable section

open CategoryTheory

namespace PretriangulatedV2

universe w v u

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

theorem isIso_of_isSplitMono_endo {X : C} [FiniteDimensional k (X ⟶ X)]
    (f : X ⟶ X) [IsSplitMono f] : IsIso f := by
  have hinj : Function.Injective (CategoryTheory.Linear.rightComp k X f) := by
    intro a b h
    exact (cancel_mono f).mp h
  obtain ⟨g, hg⟩ := LinearMap.surjective_of_injective hinj (𝟙 X)
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨g, hg⟩
  exact isIso_of_mono_of_isSplitEpi f

theorem isIso_of_isSplitEpi_endo {X : C} [FiniteDimensional k (X ⟶ X)]
    (f : X ⟶ X) [IsSplitEpi f] : IsIso f := by
  have hinj : Function.Injective (CategoryTheory.Linear.leftComp k X f) := by
    intro a b h
    exact (cancel_epi f).mp h
  obtain ⟨g, hg⟩ := LinearMap.surjective_of_injective hinj (𝟙 X)
  have : IsSplitMono f := IsSplitMono.mk' ⟨g, hg⟩
  exact isIso_of_epi_of_isSplitMono f

theorem not_isSplitMono_of_not_isIso {X : C} [FiniteDimensional k (X ⟶ X)]
    (f : X ⟶ X) (hf : ¬ IsIso f) : ¬ IsSplitMono f := by
  intro h
  let := h
  exact hf (isIso_of_isSplitMono_endo (k := k) f)

theorem not_isSplitEpi_of_not_isIso {X : C} [FiniteDimensional k (X ⟶ X)]
    (f : X ⟶ X) (hf : ¬ IsIso f) : ¬ IsSplitEpi f := by
  intro h
  let := h
  exact hf (isIso_of_isSplitEpi_endo (k := k) f)

end PretriangulatedV2
