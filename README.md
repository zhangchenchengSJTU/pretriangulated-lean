# Pretriangulated categories failing (TR4)

Lean formalization of [*Pretriangulated categories failing (TR4)*, arXiv:2608.09777v2](https://arxiv.org/abs/2608.09777v2).

The completed scope comprises Theorems 1.1 and 6.4, Corollary 1.2, the concrete field specialization, and their full proof dependencies. The main theorem constructs a pretriangulation failing the octahedral axiom on a Hom-finite, idempotent-complete, `k`-linear triangulated category whose stable category of coherent functors admits a gemstone. The category and its given suspension are retained.

Corollary 1.2 applies to the stable finite-module category of `R[x]/(x^(3*m))`, where `R` is a finite-dimensional commutative local symmetric algebra and `m ≥ 2`. Symmetry is represented by `FiniteModuleCategory.SymmetricTrace`, a linear trace with nondegenerate multiplication pairing. The field specialization constructs this trace internally for `R = k`.

All declarations below lie in the namespace `PretriangulatedV2`.

| Result | Declaration | Source |
| --- | --- | --- |
| Theorems 1.1 and 6.4 | `MainTheorem.theorem_1_1`, `MainTheorem.theorem_6_4` | [MainTheorem.lean](PretriangulatedV2/MainTheorem.lean) |
| Corollary 1.2 / Example 7.2 | `ConcreteCounterexample.corollary_1_2` | [ConcreteCounterexample.lean](PretriangulatedV2/ConcreteCounterexample.lean) |
| Field specialization | `ConcreteFieldExample.counterexample` | [ConcreteFieldExample.lean](PretriangulatedV2/ConcreteFieldExample.lean) |
| Heller classification (§3.3) | `HellerParameterRecovery.classification` | [HellerParameterRecovery.lean](PretriangulatedV2/HellerParameterRecovery.lean) |

The project uses **Lean 4.33.0-rc2** and mathlib commit **`639923353ff2a58e9976a254e0d40f4bebae36bc`**, pinned by the project configuration. Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/zhangchenchengSJTU/pretriangulated-lean.git
cd pretriangulated-lean
lake exe cache get
lake build --wfail
lake env lean AxiomAudit.lean
```

[PretriangulatedV2.lean](PretriangulatedV2.lean) imports the complete development. The audit recursively checks the axioms of every declaration from the project's modules, including private declarations and namespace extensions, and permits only `propext`, `Classical.choice`, and `Quot.sound`. The proofs contain no `sorry`, `admit`, or additional axioms.
