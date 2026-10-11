import PretriangulatedV2.TruncatedPolynomialSymmetry
import PretriangulatedV2.FiniteModuleFrobenius

/-!
The actual symmetric trace on R[x]/(x^n), and the resulting Frobenius
finite-module category. Both are constructed from the original trace on R.
-/

noncomputable section

namespace PretriangulatedV2.TruncatedPolynomialAlgebra

universe u

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Nontrivial R]

/-- The nondegenerate top-coefficient trace on the actual truncated quotient. -/
def symmetricTrace (t : FiniteModuleCategory.SymmetricTrace k R)
    (n : ℕ) (hn : 0 < n) : FiniteModuleCategory.SymmetricTrace k (Trunc R n) where
  trace := traceOfCoefficients t.trace n hn
  nondegenerate a ha := traceOfCoefficients_nondegenerate t.trace t.nondegenerate n hn a ha

variable [FiniteDimensional k R]

/-- The concrete finite-module Frobenius property follows from the constructed
trace and actual covers, rather than from a Frobenius hypothesis. -/
theorem finiteModuleCategory_frobenius
    (t : FiniteModuleCategory.SymmetricTrace k R) (n : ℕ) (hn : 0 < n) :
    letI : IsNoetherianRing (Trunc R n) := IsNoetherianRing.of_finite k (Trunc R n)
    FrobeniusAbelian (FGModuleCat.{u} (Trunc R n)) := by
  have : IsNoetherianRing (Trunc R n) := IsNoetherianRing.of_finite k (Trunc R n)
  exact FiniteModuleCategory.frobeniusAbelian (symmetricTrace t n hn)

end PretriangulatedV2.TruncatedPolynomialAlgebra
