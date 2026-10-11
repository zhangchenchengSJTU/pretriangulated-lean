import PretriangulatedV2.AcyclicNullHomotopy

/-!
The global assembly of the two half-line recursions from
`AcyclicNullHomotopy`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PretriangulatedV2.StableCategory.AcyclicNullHomotopyCompletion

open AcyclicNullHomotopy

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [FrobeniusAbelian C]

section

variable {P R : CochainComplex C ℤ} (f : P ⟶ R)
  (hP : P.Acyclic) (hR : R.Acyclic)
  (projP : ∀ k : ℤ, Projective (P.X k))
  (projR : ∀ k : ℤ, Projective (R.X k))
  {J : C} [Projective J] (a : P.cycles 0 ⟶ J) (b : J ⟶ R.cycles 0)
  (hab : cyclesMap f 0 = a ≫ b)

private noncomputable def diag (j : ℤ) : P.X (j + 1) ⟶ R.X j :=
  match j with
  | Int.ofNat n => (positiveStates f hP hR projR a b hab n).1
  | Int.negSucc n => (negativeStates f hP hR projP projR a b hab n).1

private noncomputable def step (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) :
    P.X i ⟶ R.X j := by
  change j + 1 = i at hij
  subst i
  exact diag f hP hR projP projR a b hab j

private lemma step_succ (j : ℤ) (h : (ComplexShape.up ℤ).Rel j (j + 1)) :
    step f hP hR projP projR a b hab (j + 1) j h =
      diag f hP hR projP projR a b hab j := by
  simp [step]

private lemma positive_next (n : ℕ) :
    (positiveStates f hP hR projR a b hab (n + 1)).1 =
      (positiveStates f hP hR projR a b hab n).2.1 := by
  rfl

private lemma negative_next (n : ℕ) :
    (negativeStates f hP hR projP projR a b hab (n + 1)).2.1 =
      (negativeStates f hP hR projP projR a b hab n).1 := by
  rfl

private lemma positive_equation (n : ℕ) :
    f.f ((n : ℤ) + 1) = P.d ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) ≫
      diag f hP hR projP projR a b hab ((n : ℤ) + 1) +
      diag f hP hR projP projR a b hab (n : ℤ) ≫ R.d (n : ℤ) ((n : ℤ) + 1) := by
  have hn := (positiveStates f hP hR projR a b hab n).2.2
  have he := positive_next (f := f) (hP := hP) (hR := hR) (projR := projR)
    (a := a) (b := b) (hab := hab) n
  simp only [Int.natCast_add, Int.natCast_one] at he
  rw [← he] at hn
  change f.f ((n : ℤ) + 1) = P.d ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) ≫
    (show P.X ((n : ℤ) + 1 + 1) ⟶ R.X ((n : ℤ) + 1) from
      (positiveStates f hP hR projR a b hab (n + 1)).1) +
    (positiveStates f hP hR projR a b hab n).1 ≫ R.d (n : ℤ) ((n : ℤ) + 1)
  exact hn

private lemma negative_equation (n : ℕ) :
    f.f (Int.negSucc n) = P.d (Int.negSucc n) (Int.negSucc n + 1) ≫
      diag f hP hR projP projR a b hab (Int.negSucc n) +
      step (f := f) (hP := hP) (hR := hR) (projP := projP) (projR := projR)
        (a := a) (b := b) (hab := hab) (Int.negSucc n) (Int.negSucc n - 1)
        (by change Int.negSucc n - 1 + 1 = Int.negSucc n; omega) ≫
        R.d (Int.negSucc n - 1) (Int.negSucc n) := by
  have hn := (negativeStates f hP hR projP projR a b hab (n + 1)).2.2
  have he := negative_next (f := f) (hP := hP) (hR := hR) (projP := projP)
    (projR := projR) (a := a) (b := b) (hab := hab) n
  simp only [Int.natCast_add, Int.natCast_one] at he
  rw [he] at hn
  change f.f (Int.negSucc n) = P.d (Int.negSucc n) (Int.negSucc n + 1) ≫
    (show P.X (Int.negSucc n + 1) ⟶ R.X (Int.negSucc n) from
      (negativeStates f hP hR projP projR a b hab n).1) +
    (show P.X (Int.negSucc n) ⟶ R.X (Int.negSucc n - 1) from
      (negativeStates f hP hR projP projR a b hab (n + 1)).1) ≫
        R.d (Int.negSucc n - 1) (Int.negSucc n)
  exact hn

private lemma zero_equation :
    f.f 0 = P.d 0 1 ≫
      (show P.X 1 ⟶ R.X 0 from (positiveStates f hP hR projR a b hab 0).1) +
      (show P.X 0 ⟶ R.X (-1) from (negativeStates f hP hR projP projR a b hab 0).1) ≫
        R.d (-1) 0 := by
  exact (negativeStates f hP hR projP projR a b hab 0).2.2

theorem nullHomotopyOfCycleFactorization
    (hP : P.Acyclic) (hR : R.Acyclic)
    (projP : ∀ k : ℤ, Projective (P.X k)) (projR : ∀ k : ℤ, Projective (R.X k))
    {J : C} [Projective J] (a : P.cycles 0 ⟶ J) (b : J ⟶ R.cycles 0)
    (hab : cyclesMap f 0 = a ≫ b) :
    Nonempty (Homotopy f 0) := by
  let h : ∀ i j, (ComplexShape.up ℤ).Rel j i → (P.X i ⟶ R.X j) :=
    fun i j hij => step f hP hR projP projR a b hab i j hij
  have hf : f = Homotopy.nullHomotopicMap' h := by
    ext k
    cases k with
    | ofNat n =>
      cases n with
      | zero =>
        erw [show Int.ofNat 0 = (0 : ℤ) by rfl]
        rw [Homotopy.nullHomotopicMap'_f
          (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
          (show (ComplexShape.up ℤ).Rel 0 1 by simp) h]
        dsimp [h]
        change f.f 0 = P.d 0 1 ≫
          (show P.X 1 ⟶ R.X 0 from (positiveStates f hP hR projR a b hab 0).1) +
          (show P.X 0 ⟶ R.X (-1) from (negativeStates f hP hR projP projR a b hab 0).1) ≫
            R.d (-1) 0
        exact zero_equation f hP hR projP projR a b hab
      | succ n =>
        erw [show Int.ofNat (n + 1) = (n : ℤ) + 1 by norm_num]
        rw [Homotopy.nullHomotopicMap'_f
          (show (ComplexShape.up ℤ).Rel (n : ℤ) ((n : ℤ) + 1) by simp)
          (show (ComplexShape.up ℤ).Rel ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) by simp) h]
        dsimp [h]
        rw [step_succ (f := f) (hP := hP) (hR := hR) (projP := projP) (projR := projR)
          (a := a) (b := b) (hab := hab) ((n : ℤ) + 1) (by simp)]
        rw [step_succ (f := f) (hP := hP) (hR := hR) (projP := projP) (projR := projR)
          (a := a) (b := b) (hab := hab) (n : ℤ) (by simp)]
        exact positive_equation f hP hR projP projR a b hab n
    | negSucc n =>
      rw [Homotopy.nullHomotopicMap'_f
        (show (ComplexShape.up ℤ).Rel (Int.negSucc n - 1) (Int.negSucc n) by
          change Int.negSucc n - 1 + 1 = Int.negSucc n
          omega)
        (show (ComplexShape.up ℤ).Rel (Int.negSucc n) (Int.negSucc n + 1) by simp) h]
      dsimp [h]
      rw [step_succ (f := f) (hP := hP) (hR := hR) (projP := projP) (projR := projR)
        (a := a) (b := b) (hab := hab) (Int.negSucc n) (by simp)]
      exact negative_equation f hP hR projP projR a b hab n
  refine ⟨?_⟩
  exact (Homotopy.ofEq hf).trans (Homotopy.nullHomotopy' h)

end

end PretriangulatedV2.StableCategory.AcyclicNullHomotopyCompletion
