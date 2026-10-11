import PretriangulatedV2.Lightning
import PretriangulatedV2.AlmostVanishing

/-!
The final factorisation argument in Proposition 5.8 of arXiv:2608.09777v2.
The hypotheses here are the explicit inputs of that argument, not a claim that
the preceding gemstone/AR lemmas have already been proved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace PretriangulatedV2

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Irreducibility with respect to arbitrary factorizations. -/
def IsIrreducibleMorphism {X Z : C} (f : X ⟶ Z) : Prop :=
  ¬ IsSplitMono f ∧ ¬ IsSplitEpi f ∧
    ∀ {Y : C} (a : X ⟶ Y) (b : Y ⟶ Z), f = a ≫ b →
      IsSplitMono a ∨ IsSplitEpi b

variable [HasShift C ℤ] {k : Type w} [Field k] [Linear k C]

/-- The last paragraph of Proposition 5.8, separated from the AR and dimension
arguments supplying its hypotheses.

For the paper's triangle take `b = -Σv`, `a = Σ²α`, and `T.mor₃ = -Σs`.
The absence of sections/retractions is exactly the two direct-summand exclusions
used there. No octahedral axiom is used in this argument. -/
theorem not_lightning_of_irreducible_factorization (T : Triangle C)
    [FiniteDimensional k (T.obj₃ ⟶ T.obj₃)]
    (b : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃) (a : T.obj₃ ⟶ T.obj₃)
    (ha : IsAlmostVanishing a)
    (hba : T.mor₃ ≫ b = a)
    (hb : IsIrreducibleMorphism b)
    (hfactor : ∀ phi : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₂,
      ∃ eps : T.obj₃ ⟶ T.obj₃, phi ≫ T.mor₂ = b ≫ eps)
    (hsection : ∀ phi : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₂, ¬ IsSplitMono phi)
    (hretraction : ∀ p : T.obj₂ ⟶ T.obj₃, ¬ IsSplitEpi p)
    (f : T.obj₃ ⟶ T.obj₃) (hf : f ≠ 0) : ¬ IsLightningFlash T T f := by
  rintro ⟨phi, hphi⟩
  obtain ⟨eps, heps⟩ := hfactor phi
  have hfeps : f = a ≫ eps := by
    rw [hphi, heps, ← Category.assoc, hba]
  have hmono : IsSplitMono eps := by
    by_contra h
    exact hf (hfeps.trans (ha.postcomp_eq_zero eps h))
  have : IsSplitMono eps := hmono
  have : IsIso eps := isIso_of_isSplitMono_endo (k := k) eps
  have hfact : b = phi ≫ (T.mor₂ ≫ inv eps) := by
    calc
      b = (b ≫ eps) ≫ inv eps := by simp
      _ = (phi ≫ T.mor₂) ≫ inv eps := by rw [← heps]
      _ = phi ≫ (T.mor₂ ≫ inv eps) := Category.assoc _ _ _
  rcases hb.2.2 phi (T.mor₂ ≫ inv eps) hfact with hs | hr
  · exact hsection phi hs
  · exact hretraction (T.mor₂ ≫ inv eps) hr

end PretriangulatedV2
