import PretriangulatedV2.PeriodicTriangleConstruction
import PretriangulatedV2.PeriodicExactnessBridge

/-!
Exactness and actual zero-cycle realization for the periodic complexes built
from projective triangles. Every cycle comparison uses the ordinary kernel
universal property and the original three short exact rows.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PretriangulatedV2.StableCategory.InjectiveComparison
open PretriangulatedV2.StableCategory.PeriodicComplexes
open PretriangulatedV2.StableCategory.PeriodicTriangleConstruction

namespace PretriangulatedV2.StableCategory.PeriodicComplexes.SComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : C ≌ C} [S.functor.Additive]
variable (P : SComplex S)

noncomputable def periodShortComplexIso (n : ℤ) :
    (P.complex.sc' ((n - 1) - 3) (n - 3) ((n + 1) - 3)).map S.functor ≅
      P.complex.sc' (n - 1) n (n + 1) :=
  ShortComplex.isoMk (P.period (n - 1)) (P.period n) (P.period (n + 1))
    (P.period_comm (n - 1) n).symm
    (P.period_comm n (n + 1)).symm

theorem period_exactAt_iff (n : ℤ) :
    P.complex.ExactAt n ↔ P.complex.ExactAt (n - 3) := by
  rw [HomologicalComplex.exactAt_iff' P.complex (n - 1) n (n + 1) (by simp) (by simp),
    HomologicalComplex.exactAt_iff' P.complex ((n - 1) - 3) (n - 3) ((n + 1) - 3)
      (by simp only [CochainComplex.prev]; omega)
      (by simp only [CochainComplex.next]; omega),
    ← ShortComplex.exact_iff_of_iso (P.periodShortComplexIso n)]
  exact ShortComplex.exact_map_iff_of_faithful _ S.functor

theorem acyclic_of_exactAt_one_two_three (h₁ : P.complex.ExactAt 1) (h₂ : P.complex.ExactAt 2)
    (h₃ : P.complex.ExactAt 3) : P.complex.Acyclic := by
  let Q : ℤ → Prop := fun q => P.complex.ExactAt q ∧
    P.complex.ExactAt (q + 1) ∧ P.complex.ExactAt (q + 2)
  have hbase : Q 1 := by
    exact ⟨h₁, h₂, h₃⟩
  have hsucc : ∀ q : ℤ, Q q → Q (q + 1) := by
    intro q hq
    refine ⟨hq.2.1,
      by convert hq.2.2 using 1 ; omega, ?_⟩
    have h := (P.period_exactAt_iff (q + 3)).mpr (by
      convert hq.1 using 1 ; omega)
    convert h using 1 ; omega
  have hpred : ∀ q : ℤ, Q q → Q (q - 1) := by
    intro q hq
    refine ⟨?_, by convert hq.1 using 1 ; omega,
      by convert hq.2.1 using 1; omega⟩
    have h := (P.period_exactAt_iff (q + 2)).mp (by
      convert hq.2.2 using 1)
    convert h using 1 ; omega
  intro n
  have hn : Q n := Int.inductionOn' n 1 hbase (fun q _ hq => hsucc q hq)
    (fun q _ hq => hpred q hq)
  exact hn.1

end PretriangulatedV2.StableCategory.PeriodicComplexes.SComplex

namespace PretriangulatedV2.StableCategory.PeriodicTriangleExactness

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C] (S : C ≌ C) [S.functor.Additive]

/-- The three finite exactness obligations in the actual δ-exact witness
force exactness in every positive and negative integer degree. -/
theorem deltaExact_acyclic (p : HellerExactness.Parameter S) (P : SComplex S)
    (hP : HellerExactness.DeltaExactTruncation S p (P.complex.d 0 1)
      (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv)) : P.complex.Acyclic := by
  obtain ⟨h₁, h₂, h₃, _⟩ := PeriodicExactnessBridge.periodic_of_deltaExactTruncation S p P hP
  exact P.acyclic_of_exactAt_one_two_three h₁ h₂ h₃

/-- Splice an actual three-step injective extension into the three arrows
which generate its genuine bi-infinite periodic projective complex. -/
def ofExtension {M : C} (E : Extension3 M (S.functor.obj M)) : ThreeTerm S where
  X₀ := E.I₀
  X₁ := E.I₁
  X₂ := E.I₂
  projective₀ := (FrobeniusAbelian.projective_iff_injective _).mpr E.injective₀
  projective₁ := (FrobeniusAbelian.projective_iff_injective _).mpr E.injective₁
  projective₂ := (FrobeniusAbelian.projective_iff_injective _).mpr E.injective₂
  f := E.d₀
  g := E.d₁
  h := E.p₂ ≫ S.functor.map E.i₀
  fg := by
    simp only [Extension3.d₀, Extension3.d₁, Category.assoc,
      ← Category.assoc E.i₁ E.p₁ E.i₂, E.zero₁, zero_comp, comp_zero]
  gh := by
    simp only [Extension3.d₁, Category.assoc,
      ← Category.assoc E.i₂ E.p₂ (S.functor.map E.i₀), E.zero₂, zero_comp, comp_zero]
  hSf := by
    rw [Category.assoc, ← S.functor.map_comp]
    have hh : E.i₀ ≫ E.d₀ = 0 := by
      simp only [Extension3.d₀, ← Category.assoc, E.zero₀, zero_comp]
    rw [hh, S.functor.map_zero, comp_zero]

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem period_three_inv (D : ThreeTerm S) :
    (D.period 3).inv = 𝟙 (S.functor.obj D.X₀) := by
  calc
    (D.period 3).inv = (D.period 3).inv ≫ (D.period 3).hom := by
      rw [D.period_three]
      exact (Category.comp_id _).symm
    _ = 𝟙 _ := (D.period 3).inv_hom_id

/-- The original finite δ-exact triangle gives exactly the truncation of the
constructed periodic complex, including the actual degree-three period. -/
theorem truncation_of_threeTerm (p : HellerExactness.Parameter S) (D : ThreeTerm S)
    (hD : HellerExactness.DeltaExactTruncation S p D.f D.g D.h) :
    HellerExactness.DeltaExactTruncation S p (D.sComplex.complex.d 0 1)
      (D.sComplex.complex.d 1 2)
      (D.sComplex.complex.d 2 3 ≫ (D.sComplex.period 3).inv) := by
  change HellerExactness.DeltaExactTruncation S p (D.complex.d 0 1)
    (D.complex.d 1 2) (D.complex.d 2 3 ≫ (D.period 3).inv)
  rw [D.complex_d₀₁, D.complex_d₁₂, D.complex_d₂₃, period_three_inv]
  change HellerExactness.DeltaExactTruncation S p D.f D.g (D.h ≫ 𝟙 _)
  simpa only [Category.comp_id] using hD

/-- The actual extension gives the canonical cycle truncation's δ-exactness. -/
theorem periodic_of_threeTerm (p : HellerExactness.Parameter S) (D : ThreeTerm S)
    (hD : HellerExactness.DeltaExactTruncation S p D.f D.g D.h) :
    ComplexInjectiveExtensions.DeltaExactPeriodic S p D.sComplex :=
  PeriodicExactnessBridge.periodic_of_deltaExactTruncation S p D.sComplex
    (truncation_of_threeTerm S p D hD)

/-- The original extension is an actual row witness for its generated complex. -/
def extensionWitness {M : C} (E : Extension3 M (S.functor.obj M)) :
    PeriodicExactnessBridge.RowWitness S (ofExtension S E).sComplex where
  M := M
  E := E
  e₀ := Iso.refl _
  e₁ := Iso.refl _
  e₂ := Iso.refl _
  comm₀ := by
    change E.d₀ ≫ 𝟙 E.I₁ = 𝟙 E.I₀ ≫ (ofExtension S E).complex.d 0 1
    rw [Category.comp_id, Category.id_comp]
    exact ((ofExtension S E).complex_d₀₁).symm
  comm₁ := by
    change E.d₁ ≫ 𝟙 E.I₂ = 𝟙 E.I₁ ≫ (ofExtension S E).complex.d 1 2
    rw [Category.comp_id, Category.id_comp]
    exact ((ofExtension S E).complex_d₁₂).symm
  comm₂ := by
    change E.p₂ ≫ S.functor.map (E.i₀ ≫ 𝟙 E.I₀) =
      𝟙 E.I₂ ≫ ((ofExtension S E).complex.d 2 3 ≫ ((ofExtension S E).period 3).inv)
    rw [Category.comp_id, Category.id_comp, (ofExtension S E).complex_d₂₃,
      period_three_inv]
    change E.p₂ ≫ S.functor.map E.i₀ = (E.p₂ ≫ S.functor.map E.i₀) ≫ 𝟙 _
    exact (Category.comp_id _).symm

/-- The input object is genuinely the zeroth cycles of the generated complex. -/
def zeroCycleIso {M : C} (E : Extension3 M (S.functor.obj M)) :
    M ≅ (ofExtension S E).complex.cycles 0 :=
  (extensionWitness S E).initialIso

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem zeroCycleIso_hom_iCycles {M : C} (E : Extension3 M (S.functor.obj M)) :
    (zeroCycleIso S E).hom ≫ (ofExtension S E).complex.iCycles 0 = E.i₀ := by
  simpa only [zeroCycleIso, ThreeTerm.sComplex, extensionWitness, Iso.refl_hom, Category.comp_id] using
    (extensionWitness S E).initialIso_hom_iCycles

theorem extension_periodic (p : HellerExactness.Parameter S) {M : C}
    (E : Extension3 M (S.functor.obj M)) (hE : HellerExactness.DeltaExact S p E) :
    ComplexInjectiveExtensions.DeltaExactPeriodic S p (ofExtension S E).sComplex :=
  (extensionWitness S E).deltaExact_canonical p hE

omit [HasBinaryBiproducts C] in
/-- Every actual three-row extension gives an acyclic periodic complex. -/
theorem extension_acyclic {M : C} (E : Extension3 M (S.functor.obj M)) :
    (ofExtension S E).complex.Acyclic :=
  (ofExtension S E).sComplex.acyclic_of_exactAt_one_two_three
    (extensionWitness S E).exactAt₁ (extensionWitness S E).exactAt₂
    (extensionWitness S E).exactAt₃

theorem threeTerm_acyclic (p : HellerExactness.Parameter S) (D : ThreeTerm S)
    (hD : HellerExactness.DeltaExactTruncation S p D.f D.g D.h) : D.complex.Acyclic :=
  deltaExact_acyclic S p D.sComplex (truncation_of_threeTerm S p D hD)

end PretriangulatedV2.StableCategory.PeriodicTriangleExactness
