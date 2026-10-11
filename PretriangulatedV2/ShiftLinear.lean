import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Data.Int.Basic

/-! Linearity of all integer suspensions follows from linearity of shift by one. -/

open CategoryTheory

namespace PretriangulatedV2

universe w v u

variable {k : Type w} [Semiring k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasShift C ℤ]
  [Functor.Linear k (shiftFunctor C (1 : ℤ))]

/-- The inverse suspension is linear by cancelling the full, essentially
surjective linear shift-by-one from its composite with the inverse shift. -/
theorem shiftMinusOne_linear : Functor.Linear k (shiftFunctor C (-1 : ℤ)) := by
  have : Functor.Linear k
      (shiftFunctor C (1 : ℤ) ⋙ shiftFunctor C (-1 : ℤ)) :=
    Functor.linear_of_iso k (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by simp)).symm
  exact Functor.linear_of_full_essSurj_comp
    (shiftFunctor C (1 : ℤ)) (shiftFunctor C (-1 : ℤ))

/-- No separate linearity hypothesis for higher or negative shifts is needed. -/
theorem shift_linear_of_one (n : ℤ) : Functor.Linear k (shiftFunctor C n) := by
  have hminus := shiftMinusOne_linear (k := k) (C := C)
  induction n using Int.induction_on with
  | zero =>
      exact Functor.linear_of_iso k (shiftFunctorZero C ℤ).symm
  | succ n ih =>
      have := ih
      exact Functor.linear_of_iso k (shiftFunctorAdd C (n : ℤ) (1 : ℤ)).symm
  | pred n ih =>
      have := ih
      simpa only [sub_eq_add_neg] using
        (Functor.linear_of_iso k (shiftFunctorAdd C (-(n : ℤ)) (-1 : ℤ)).symm)

end PretriangulatedV2
