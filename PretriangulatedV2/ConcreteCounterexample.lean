import PretriangulatedV2.MainTheorem
import PretriangulatedV2.CoherentCalabiYau
import PretriangulatedV2.SymmetricModuleSerre
import PretriangulatedV2.StableIdempotents
import PretriangulatedV2.TruncatedSymmetricTrace
import PretriangulatedV2.TruncatedCentralEnd
import PretriangulatedV2.YonedaPeriodicData
import PretriangulatedV2.CalabiYauGemstone
import PretriangulatedV2.TruncatedStableTriangle

/-!
# The actual truncated-polynomial counterexample

The original finite-dimensional symmetric algebra supplies the Frobenius
finite-module category and the canonical stable triangulation. Its genuine
negative-shift Serre duality transports to the generated Heller action on
the actual projective coherent functors.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.ConcreteCounterexample

open TruncatedPolynomialAlgebra TruncatedModules StableCategory FiniteModuleCategory

universe u

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  [FiniteDimensional k R] [IsLocalRing R]

section Noetherian

variable [IsNoetherianRing R]

/-- The paper's actual module algebra is the quotient by `x^(3*m)`. -/
abbrev ModuleAlgebra (m : ℕ) := algebra R m

/-- The category is the actual projective stable quotient of finite modules. -/
abbrev D (m : ℕ) := projectiveStableCategory (FGModuleCat.{u} (ModuleAlgebra (R := R) m))

abbrev Q (m : ℕ) := projectiveStableQuotient (C := FGModuleCat.{u} (ModuleAlgebra (R := R) m))
abbrev M (m : ℕ) := (Q (R := R) m).obj (M₀ R m)
abbrev L (m : ℕ) := (Q (R := R) m).obj (L₀ R m)

/-- The original symmetric multiplication pairing supplies the actual top
coefficient symmetric trace on the larger polynomial quotient. -/
def algebraTrace (t : SymmetricTrace k R) (m : ℕ) (hm : 0 < m) :
    SymmetricTrace k (ModuleAlgebra (R := R) m) :=
  symmetricTrace t (3 * m) (by omega)

include k in
omit [IsLocalRing R] in
/-- Idempotents split in the actual stable category by finite-dimensional
endomorphism lifting, with no completeness assumption on that quotient. -/
theorem stable_idempotent_complete (m : ℕ) : IsIdempotentComplete (D (R := R) m) :=
  projectiveStableCategory_isIdempotentComplete (k := k)
    (C := FGModuleCat.{u} (ModuleAlgebra (R := R) m))

/-- Genuine Serre duality on coherent projectives, obtained from the original
symmetric trace, for precisely the generated Heller suspension. -/
def coherentSerre (t : SymmetricTrace k R) (m : ℕ) (hm : 0 < m) :
    letI := frobeniusAbelian (algebraTrace t m hm)
    letI := stable_idempotent_complete (k := k) (R := R) m
    SerreDuality k (CoherentCalabiYau.Projectives (D (R := R) m)) := by
  have := frobeniusAbelian (algebraTrace t m hm)
  have := stable_idempotent_complete (k := k) (R := R) m
  exact CoherentCalabiYau.serreDuality (D (R := R) m)
    (SymmetricSerre.minusOneSerre (algebraTrace t m hm)) (-1 : ℤ)
    (SymmetricSerre.minusOneSerreIso (algebraTrace t m hm))

/-- The resulting Calabi--Yau comparison uses the actual generated action,
not the distinct action transported through Yoneda. -/
def coherentSerreIso (t : SymmetricTrace k R) (m : ℕ) (hm : 0 < m) :
    letI := frobeniusAbelian (algebraTrace t m hm)
    letI := stable_idempotent_complete (k := k) (R := R) m
    letI := HellerClassification.projectiveHasShift
      (CoherentFunctors.suspension (C := D (R := R) m))
    (coherentSerre t m hm).equivalence.functor ≅
      shiftFunctor (CoherentCalabiYau.Projectives (D (R := R) m)) (-1 : ℤ) := by
  have := frobeniusAbelian (algebraTrace t m hm)
  have := stable_idempotent_complete (k := k) (R := R) m
  exact CoherentCalabiYau.serreIsoShift (D (R := R) m)
    (SymmetricSerre.minusOneSerre (algebraTrace t m hm)) (-1 : ℤ)
    (SymmetricSerre.minusOneSerreIso (algebraTrace t m hm))

/-- The actual signed stable triangle makes the two representables an
alternating exact sequence; the computed Hom vanishings give its annihilation
properties. No periodic-resolution premise is supplied. -/
def periodicData (t : SymmetricTrace k R) (m : ℕ) (hm : 2 ≤ m) :
    letI := frobeniusAbelian (algebraTrace t m (by omega))
    PeriodicResolution.Data
      ((CoherentFunctors.yoneda (C := D (R := R) m)).obj (M (R := R) m))
      ((CoherentFunctors.yoneda (C := D (R := R) m)).obj (L (R := R) m)) := by
  have := frobeniusAbelian (algebraTrace t m (by omega))
  exact YonedaPeriodicData.data
    ((Q (R := R) m).map (iota₀ R m)) ((Q (R := R) m).map (q₀ R m))
    (TruncatedStableTriangle.signedMShiftIso R t m hm)
    (TruncatedStableTriangle.concrete_distinguished R t m hm)
    (TruncatedStableHom.stableHom_M₀_iota₀_zero R m)
    (TruncatedStableHom.stableHom_L₀_q₀_zero R m)

/-- The concrete calculation, the original symmetric duality and the actual
recovered Heller parameter give a gemstone in the stable coherent-functor
category. All conditions in Proposition 7.1 are derived internally. -/
theorem exists_gemstone (t : SymmetricTrace k R) (m : ℕ) (hm : 2 ≤ m) :
    letI := frobeniusAbelian (algebraTrace t m (by omega))
    letI := stable_idempotent_complete (k := k) (R := R) m
    Nonempty (Gemstone ((projectiveStableQuotient
      (C := CoherentFunctors.Mod (D (R := R) m))).obj (periodicData t m hm).X)) := by
  have := frobeniusAbelian (algebraTrace t m (by omega))
  have := stable_idempotent_complete (k := k) (R := R) m
  apply CalabiYauGemstone.exists_gemstone
    (CoherentFunctors.suspension (C := D (R := R) m))
    (HellerRecovery.coherentBaselineParameter (D (R := R) m)) (-1 : ℤ) (by decide)
    (coherentSerre t m (by omega)) (coherentSerreIso t m (by omega)) (periodicData t m hm)
  · exact YonedaPeriodicData.yoneda_indecomposable _
      (TruncatedStableHom.stableM₀_indecomposable R m (by omega))
  · exact YonedaPeriodicData.yoneda_indecomposable _
      (TruncatedStableHom.stableL₀_indecomposable R m (by omega))
  · exact YonedaPeriodicData.yoneda_map_ne_zero _
      (TruncatedStableHom.stable_iota₀_nonzero R m (by omega))
  · exact YonedaPeriodicData.yoneda_map_ne_zero _
      (TruncatedStableHom.stable_q₀_nonzero R m (by omega))
  · exact YonedaPeriodicData.end_commutative (k := k) _
      (TruncatedStableHom.stableEnd_comm R m)
  · exact YonedaPeriodicData.end_not_isField (k := k) _
      (TruncatedStableHom.stableEnd_not_isField R m hm)
  · exact YonedaPeriodicData.central_extension _ _
      (TruncatedCentralEnd.exists_central_diagonal R m)

end Noetherian

/-- Corollary 1.2: for the actual finite-module stable category over
`R[x]/(x^(3*m))`, the original finite-dimensional commutative local symmetric
algebra and `m ≥ 2` suffice to construct a pretriangulation that fails TR4.
The underlying category and canonical integer suspension are retained. -/
theorem corollary_1_2 (t : SymmetricTrace k R) (m : ℕ) (hm : 2 ≤ m) :
    letI := IsNoetherianRing.of_finite k R
    letI := frobeniusAbelian (algebraTrace t m (by omega))
    ∃ p : Pretriangulated (D (R := R) m), letI := p; ¬ IsTriangulated (D (R := R) m) := by
  let := IsNoetherianRing.of_finite k R
  have := frobeniusAbelian (algebraTrace t m (by omega))
  have := stable_idempotent_complete (k := k) (R := R) m
  exact MainTheorem.theorem_1_1 (k := k) (D (R := R) m)
    (Classical.choice (exists_gemstone t m hm))

end PretriangulatedV2.ConcreteCounterexample
