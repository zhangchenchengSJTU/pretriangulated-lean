import PretriangulatedV2.StableCocycles
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Equivalence

/-!
Actual three-periodic cochain complexes relative to an autoequivalence.
Periodicity is recorded by specified isomorphisms, so that object equalities
in the paper do not rely on definitional equality of Lean expressions.
The operation `twistMap` is the paper's cochain map `f_S`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PretriangulatedV2.StableCategory.PeriodicComplexes

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] (S : C ≌ C)

/-- An actual complex of projective objects with three-periodicity under `S`.
The differential compatibility is required for all integer indices. -/
structure SComplex where
  complex : CochainComplex C ℤ
  projective : ∀ n : ℤ, Projective (complex.X n)
  period : ∀ n : ℤ, S.functor.obj (complex.X (n - 3)) ≅ complex.X n
  period_comm (n m : ℤ) :
    S.functor.map (complex.d (n - 3) (m - 3)) ≫ (period m).hom =
      (period n).hom ≫ complex.d n m

namespace SComplex

variable {S} (P R : SComplex S)

def toProjectiveComplex : StableCocycles.ProjectiveComplex C :=
  ⟨P.complex, P.projective⟩

theorem period_inv_comm (n m : ℤ) :
    P.complex.d n m ≫ (P.period m).inv =
      (P.period n).inv ≫ S.functor.map (P.complex.d (n - 3) (m - 3)) := by
  apply (cancel_epi (P.period n).hom).mp
  rw [← Category.assoc, ← P.period_comm]
  simp [Category.assoc]

/-- Reindexing an arbitrary actual cochain map by one `S`-period. -/
def twistMap (f : P.complex ⟶ R.complex) : P.complex ⟶ R.complex where
  f n := (P.period n).inv ≫ S.functor.map (f.f (n - 3)) ≫ (R.period n).hom
  comm' n m _ := by
    calc
      ((P.period n).inv ≫ S.functor.map (f.f (n - 3)) ≫ (R.period n).hom) ≫
          R.complex.d n m =
        (P.period n).inv ≫
          S.functor.map (f.f (n - 3) ≫ R.complex.d (n - 3) (m - 3)) ≫
          (R.period m).hom := by
            simp only [Functor.map_comp, Category.assoc, R.period_comm]
      _ = (P.period n).inv ≫
          S.functor.map (P.complex.d (n - 3) (m - 3) ≫ f.f (m - 3)) ≫
          (R.period m).hom := by rw [f.comm]
      _ = P.complex.d n m ≫
          ((P.period m).inv ≫ S.functor.map (f.f (m - 3)) ≫ (R.period m).hom) := by
            simp only [Functor.map_comp, ← Category.assoc, ← P.period_inv_comm]

@[simp]
theorem twistMap_f (f : P.complex ⟶ R.complex) (n : ℤ) :
    (P.twistMap R f).f n =
      (P.period n).inv ≫ S.functor.map (f.f (n - 3)) ≫ (R.period n).hom := rfl

@[simp]
theorem twistMap_id : P.twistMap P (𝟙 P.complex) = 𝟙 P.complex := by
  ext n
  simp [twistMap]

@[simp]
theorem twistMap_comp (T : SComplex S)
    (f : P.complex ⟶ R.complex) (g : R.complex ⟶ T.complex) :
    P.twistMap T (f ≫ g) = P.twistMap R f ≫ R.twistMap T g := by
  ext n
  simp [twistMap, Functor.map_comp, Category.assoc]

variable [S.functor.Additive]

/-- The actual kernel comparison induced by the periodicity of the
differential. Equivalences preserve this kernel by their proved limit
preservation, without assuming the desired cycle isomorphism. -/
def cyclePeriod (n : ℤ) :
    S.functor.obj (P.complex.cycles (n - 3)) ≅ P.complex.cycles n :=
  KernelFork.mapIsoOfIsLimit
    (KernelFork.mapIsLimit _
      (P.complex.cyclesIsKernel (n - 3) ((n + 1) - 3)
        (ComplexShape.next_eq' _ (by
          change (n - 3) + 1 = (n + 1) - 3
          omega))) S.functor)
    (P.complex.cyclesIsKernel n (n + 1)
      (ComplexShape.next_eq' _ (by change n + 1 = n + 1; rfl)))
    (Arrow.isoMk (P.period n) (P.period (n + 1))
      (P.period_comm n (n + 1)).symm)

@[reassoc (attr := simp)]
theorem cyclePeriod_hom_iCycles (n : ℤ) :
    (P.cyclePeriod n).hom ≫ P.complex.iCycles n =
      S.functor.map (P.complex.iCycles (n - 3)) ≫ (P.period n).hom := by
  simpa only [cyclePeriod, KernelFork.mapIsoOfIsLimit_hom, KernelFork.map_ι,
    KernelFork.ι_ofι, Arrow.isoMk_hom_left] using
    (KernelFork.mapOfIsLimit_ι
      ((KernelFork.ofι (P.complex.iCycles (n - 3))
        (P.complex.iCycles_d (n - 3) ((n + 1) - 3))).map S.functor)
      (P.complex.cyclesIsKernel n (n + 1)
        (ComplexShape.next_eq' _ (by change n + 1 = n + 1; rfl)))
      (Arrow.isoMk (P.period n) (P.period (n + 1))
        (P.period_comm n (n + 1)).symm).hom)

/-- The map on periodic cycles is derived from the actual differential
squares of the cochain map. -/
theorem cyclePeriod_naturality (f : P.complex ⟶ R.complex) (n : ℤ) :
    S.functor.map (cyclesMap f (n - 3)) ≫ (R.cyclePeriod n).hom =
      (P.cyclePeriod n).hom ≫ cyclesMap (P.twistMap R f) n := by
  apply (cancel_mono (R.complex.iCycles n)).mp
  rw [Category.assoc, cyclePeriod_hom_iCycles, ← Category.assoc,
    ← Functor.map_comp, cyclesMap_i, Functor.map_comp]
  rw [Category.assoc, Category.assoc, cyclesMap_i, cyclePeriod_hom_iCycles_assoc]
  simp [twistMap]

/-- At degree three the kernel comparison identifies `S Z⁰(P)` with `Z³(P)`.
This is the endpoint identification in the comparison diagram of Lemma 4.1. -/
def periodicityCycleIso :
    S.functor.obj (P.complex.cycles 0) ≅ P.complex.cycles 3 := P.cyclePeriod 3

@[reassoc (attr := simp)]
theorem periodicityCycleIso_hom_iCycles :
    P.periodicityCycleIso.hom ≫ P.complex.iCycles 3 =
      S.functor.map (P.complex.iCycles 0) ≫ (P.period 3).hom := by
  exact P.cyclePeriod_hom_iCycles 3

theorem periodicityCycleIso_naturality (f : P.complex ⟶ R.complex) :
    S.functor.map (cyclesMap f 0) ≫ R.periodicityCycleIso.hom =
      P.periodicityCycleIso.hom ≫ cyclesMap (P.twistMap R f) 3 := by
  exact P.cyclePeriod_naturality R f 3

end SComplex

end PretriangulatedV2.StableCategory.PeriodicComplexes
