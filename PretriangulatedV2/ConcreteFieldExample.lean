import PretriangulatedV2.ConcreteCounterexample

/-! The specialization R = k supplies an actual symmetric trace internally,
so the counterexample needs no symmetric-algebra witness as an input. -/

noncomputable section

open CategoryTheory

namespace PretriangulatedV2.ConcreteFieldExample

universe u

/-- A field is a commutative symmetric algebra over itself. -/
def fieldTrace (k : Type u) [Field k] : FiniteModuleCategory.SymmetricTrace k k where
  trace := LinearMap.id
  nondegenerate a ha := by simpa using ha 1

/-- For every field and every m ≥ 2, the actual stable finite-module category
over k[x]/(x^(3*m)) admits a pretriangulation failing TR4. Its original
canonical suspension is retained. -/
theorem counterexample (k : Type u) [Field k] (m : ℕ) (hm : 2 ≤ m) :
    letI := IsNoetherianRing.of_finite k k
    letI := FiniteModuleCategory.frobeniusAbelian
      (ConcreteCounterexample.algebraTrace (fieldTrace k) m (by omega))
    ∃ p : Pretriangulated (ConcreteCounterexample.D (R := k) m),
      letI := p; ¬ IsTriangulated (ConcreteCounterexample.D (R := k) m) :=
  ConcreteCounterexample.corollary_1_2 (fieldTrace k) m hm

end PretriangulatedV2.ConcreteFieldExample
