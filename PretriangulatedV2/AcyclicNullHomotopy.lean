import PretriangulatedV2.ComplexInjectiveExtensions

/-!
The null-homotopy calculation used for the faithfulness of actual zero cycles.

The lemmas in this file deliberately work with the actual `cycles` objects and
the actual short exact rows supplied by `cycleSequence_shortExact`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PretriangulatedV2.StableCategory.AcyclicNullHomotopy

open ComplexInjectiveExtensions

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [FrobeniusAbelian C]

/-- The degree-zero component forced by a stable factorization of the cycle
map.  This is intentionally stated at zero, where the two cycle objects are
the literal objects used by `acyclicStableCycles`. -/
noncomputable def zeroSeed
    {P R : CochainComplex C ℤ} (hR : R.Acyclic) {J : C} [Projective J]
    (a : P.cycles 0 ⟶ J) (b : J ⟶ R.cycles 0) : P.X 0 ⟶ R.X (-1) :=
  letI : Injective J := (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  let e := cycleSequence_shortExact R (-1) (by simpa using hR 0)
  letI : Epi (R.toCycles (-1) 0) := by
    change Epi (cycleSequence R (-1)).g
    exact e.epi_g
  Injective.factorThru a (P.iCycles 0) ≫
    Projective.factorThru b (R.toCycles (-1) 0)

lemma zeroSeed_cycles_zero
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (hR : R.Acyclic) {J : C} [Projective J]
    (a : P.cycles 0 ⟶ J) (b : J ⟶ R.cycles 0)
    (hab : cyclesMap f 0 = a ≫ b) :
    P.iCycles 0 ≫ (f.f 0 - zeroSeed hR a b ≫ R.d (-1) 0) = 0 := by
  let : Injective J := (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  let e := cycleSequence_shortExact R (-1) (by simpa using hR 0)
  let : Epi (R.toCycles (-1) 0) := by
    change Epi (cycleSequence R (-1)).g
    exact e.epi_g
  rw [Preadditive.comp_sub, ← HomologicalComplex.cyclesMap_i, hab]
  apply sub_eq_zero.mpr
  dsimp [zeroSeed]
  simp only [← Category.assoc]
  rw [Injective.comp_factorThru, Category.assoc, ← R.toCycles_i]
  rw [Category.assoc, Projective.factorThru_comp_assoc]

/-- One backward step in the standard null-homotopy recursion.  The residual
is first lifted to the actual cycles of `Rⁿ`, and then across the epimorphism
from `Rⁿ⁻¹`; projectivity of the source supplies that second lift. -/
noncomputable def backwardStep
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ)
    (hR : R.Acyclic) (projP : ∀ i : ℤ, Projective (P.X i))
    (hnext : P.X (i + 1 + 1) ⟶ R.X (i + 1))
    (hr : (f.f (i + 1) - P.d (i + 1) (i + 1 + 1) ≫ hnext) ≫
      R.d (i + 1) (i + 1 + 1) = 0) :
    P.X (i + 1) ⟶ R.X i :=
  let e := cycleSequence_shortExact R i (hR (i + 1))
  letI : Epi (R.toCycles i (i + 1)) := by
    simpa only [cycleSequence] using e.epi_g
  letI : Projective (P.X (i + 1)) := projP (i + 1)
  Projective.factorThru
    (R.liftCycles (f.f (i + 1) - P.d (i + 1) (i + 1 + 1) ≫ hnext) (i + 1 + 1)
      (CochainComplex.next ℤ (i + 1)) hr)
    (R.toCycles i (i + 1))

omit [FrobeniusAbelian C] in
lemma backwardStep_comp_differential
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ)
    (hR : R.Acyclic) (projP : ∀ i : ℤ, Projective (P.X i))
    (hnext : P.X (i + 1 + 1) ⟶ R.X (i + 1))
    (hr : (f.f (i + 1) - P.d (i + 1) (i + 1 + 1) ≫ hnext) ≫
      R.d (i + 1) (i + 1 + 1) = 0) :
    backwardStep f i hR projP hnext hr ≫ R.d i (i + 1) =
      f.f (i + 1) - P.d (i + 1) (i + 1 + 1) ≫ hnext := by
  let e := cycleSequence_shortExact R i (hR (i + 1))
  let : Epi (R.toCycles i (i + 1)) := by
    simpa only [cycleSequence] using e.epi_g
  let : Projective (P.X (i + 1)) := projP (i + 1)
  change Projective.factorThru
      (R.liftCycles (f.f (i + 1) - P.d (i + 1) (i + 1 + 1) ≫ hnext) (i + 1 + 1)
        (CochainComplex.next ℤ (i + 1)) hr)
      (R.toCycles i (i + 1)) ≫ R.d i (i + 1) = _
  rw [← R.toCycles_i i (i + 1), Projective.factorThru_comp_assoc,
    R.liftCycles_i]

/-- The forward recursion in consecutive-index form.  This avoids transports
through expressions such as `(i + 1) - 1` when it is iterated over `ℕ`. -/
noncomputable def forwardStepNext
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ)
    (hP : P.Acyclic) (projR : ∀ k : ℤ, Projective (R.X k))
    (h : P.X (i + 1) ⟶ R.X i)
    (hh : P.iCycles (i + 1) ≫ (f.f (i + 1) - h ≫ R.d i (i + 1)) = 0) :
    P.X (i + 1 + 1) ⟶ R.X (i + 1) :=
  letI : Injective (R.X (i + 1)) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (projR (i + 1))
  let e := cycleSequence_shortExact P (i + 1) (hP (i + 1 + 1))
  let k : P.cycles (i + 1 + 1) ⟶ R.X (i + 1) :=
    e.exact.descToInjective (f.f (i + 1) - h ≫ R.d i (i + 1)) hh
  Injective.factorThru k (P.iCycles (i + 1 + 1))

/-- The boundary version of the forward step, with the actual indices `-1,0,1`
written explicitly so that it accepts `zeroSeed` without index transport. -/
noncomputable def forwardStepZero
    {P R : CochainComplex C ℤ} (f : P ⟶ R)
    (hP : P.Acyclic) (projR : ∀ k : ℤ, Projective (R.X k))
    (h : P.X 0 ⟶ R.X (-1))
    (hh : P.iCycles 0 ≫ (f.f 0 - h ≫ R.d (-1) 0) = 0) :
    P.X 1 ⟶ R.X 0 :=
  letI : Injective (R.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (projR 0)
  let e := cycleSequence_shortExact P 0 (hP 1)
  let k : P.cycles 1 ⟶ R.X 0 := e.exact.descToInjective (f.f 0 - h ≫ R.d (-1) 0) hh
  Injective.factorThru k (P.iCycles 1)

lemma differential_comp_forwardStepZero
    {P R : CochainComplex C ℤ} (f : P ⟶ R)
    (hP : P.Acyclic) (projR : ∀ k : ℤ, Projective (R.X k))
    (h : P.X 0 ⟶ R.X (-1))
    (hh : P.iCycles 0 ≫ (f.f 0 - h ≫ R.d (-1) 0) = 0) :
    P.d 0 1 ≫ forwardStepZero f hP projR h hh = f.f 0 - h ≫ R.d (-1) 0 := by
  let : Injective (R.X 0) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (projR 0)
  let e := cycleSequence_shortExact P 0 (hP 1)
  let k : P.cycles 1 ⟶ R.X 0 := e.exact.descToInjective (f.f 0 - h ≫ R.d (-1) 0) hh
  change P.d 0 1 ≫ Injective.factorThru k (P.iCycles 1) = _
  rw [← P.toCycles_i 0 1, Category.assoc, Injective.comp_factorThru]
  dsimp [k]
  simpa [e, cycleSequence] using e.exact.comp_descToInjective _ _

lemma differential_comp_forwardStepNext
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ)
    (hP : P.Acyclic) (projR : ∀ k : ℤ, Projective (R.X k))
    (h : P.X (i + 1) ⟶ R.X i)
    (hh : P.iCycles (i + 1) ≫ (f.f (i + 1) - h ≫ R.d i (i + 1)) = 0) :
    P.d (i + 1) (i + 1 + 1) ≫ forwardStepNext f i hP projR h hh =
      f.f (i + 1) - h ≫ R.d i (i + 1) := by
  let : Injective (R.X (i + 1)) :=
    (FrobeniusAbelian.projective_iff_injective _).mp (projR (i + 1))
  let e := cycleSequence_shortExact P (i + 1) (hP (i + 1 + 1))
  let k : P.cycles (i + 1 + 1) ⟶ R.X (i + 1) :=
    e.exact.descToInjective (f.f (i + 1) - h ≫ R.d i (i + 1)) hh
  change P.d (i + 1) (i + 1 + 1) ≫ Injective.factorThru k (P.iCycles (i + 1 + 1)) = _
  rw [← P.toCycles_i (i + 1) (i + 1 + 1), Category.assoc, Injective.comp_factorThru]
  dsimp [k]
  simpa [e, cycleSequence] using e.exact.comp_descToInjective _ _

omit [FrobeniusAbelian C] in
lemma cycles_zero_next_of_homotopy_equation
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ)
    (h : P.X (i + 1) ⟶ R.X i) (hnext : P.X (i + 1 + 1) ⟶ R.X (i + 1))
    (heq : f.f (i + 1) = P.d (i + 1) (i + 1 + 1) ≫ hnext + h ≫ R.d i (i + 1))
    (hP : P.Acyclic) :
    P.iCycles (i + 1 + 1) ≫
      (f.f (i + 1 + 1) - hnext ≫ R.d (i + 1) (i + 1 + 1)) = 0 := by
  let e := cycleSequence_shortExact P (i + 1) (hP (i + 1 + 1))
  let : Epi (P.toCycles (i + 1) (i + 1 + 1)) := by
    change Epi (cycleSequence P (i + 1)).g
    exact e.epi_g
  apply (cancel_epi (P.toCycles (i + 1) (i + 1 + 1))).mp
  rw [← Category.assoc, P.toCycles_i, Preadditive.comp_sub, ← f.comm,
    heq, Preadditive.add_comp]
  have hz : (h ≫ R.d i (i + 1)) ≫ R.d (i + 1) (i + 1 + 1) = 0 := by
    rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
  rw [hz, add_zero, Category.assoc, sub_self]
  simp

/-- A positive-side recursion state based at the pair of consecutive degrees
`i+1,i+2`. -/
abbrev PositiveState {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ) :=
  Σ' h : P.X (i + 1) ⟶ R.X i,
  Σ' hnext : P.X (i + 1 + 1) ⟶ R.X (i + 1),
    f.f (i + 1) = P.d (i + 1) (i + 1 + 1) ≫ hnext + h ≫ R.d i (i + 1)

noncomputable def positiveStateSucc
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ)
    (hP : P.Acyclic) (projR : ∀ k : ℤ, Projective (R.X k))
    (x : PositiveState f i) : PositiveState f (i + 1) := by
  let h' := forwardStepNext f (i + 1) hP projR x.2.1
    (cycles_zero_next_of_homotopy_equation f i x.1 x.2.1 x.2.2 hP)
  refine ⟨x.2.1, h', ?_⟩
  rw [← sub_eq_iff_eq_add, ← differential_comp_forwardStepNext]

noncomputable def positiveStateZero
    {P R : CochainComplex C ℤ} (f : P ⟶ R)
    (hP : P.Acyclic) (hR : R.Acyclic) (projR : ∀ k : ℤ, Projective (R.X k))
    {J : C} [Projective J] (a : P.cycles 0 ⟶ J) (b : J ⟶ R.cycles 0)
    (hab : cyclesMap f 0 = a ≫ b) : PositiveState f 0 := by
  let h0 := zeroSeed hR a b
  let h1 := forwardStepZero f hP projR h0 (zeroSeed_cycles_zero f hR a b hab)
  have heq0 : f.f 0 = P.d 0 1 ≫ h1 + h0 ≫ R.d (-1) 0 := by
    rw [← sub_eq_iff_eq_add, ← differential_comp_forwardStepZero]
  have hh1 : P.iCycles 1 ≫ (f.f 1 - h1 ≫ R.d 0 1) = 0 := by
    let e := cycleSequence_shortExact P 0 (hP 1)
    let : Epi (P.toCycles 0 1) := by
      change Epi (cycleSequence P 0).g
      exact e.epi_g
    apply (cancel_epi (P.toCycles 0 1)).mp
    rw [← Category.assoc, P.toCycles_i, Preadditive.comp_sub, ← f.comm,
      heq0, Preadditive.add_comp]
    have hz : (h0 ≫ R.d (-1) 0) ≫ R.d 0 1 = 0 := by
      rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
    rw [hz, add_zero, Category.assoc, sub_self]
    simp
  let h2 := forwardStepNext f 0 hP projR h1 hh1
  refine ⟨h1, h2, ?_⟩
  rw [← sub_eq_iff_eq_add, ← differential_comp_forwardStepNext]

noncomputable def positiveStates
    {P R : CochainComplex C ℤ} (f : P ⟶ R)
    (hP : P.Acyclic) (hR : R.Acyclic) (projR : ∀ k : ℤ, Projective (R.X k))
    {J : C} [Projective J] (a : P.cycles 0 ⟶ J) (b : J ⟶ R.cycles 0)
    (hab : cyclesMap f 0 = a ≫ b) : (n : ℕ) → PositiveState f (n : ℤ)
  | 0 => positiveStateZero f hP hR projR a b hab
  | n + 1 => by
      let x := positiveStates f hP hR projR a b hab n
      convert positiveStateSucc f (n : ℤ) hP projR x using 1; norm_num

/-- A negative-side state, written at the index used by `backwardStep`. -/
abbrev NegativeState {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ) :=
  PositiveState f i

omit [FrobeniusAbelian C] in
lemma negative_residual
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ) (x : NegativeState f i) :
    (f.f i - P.d i (i + 1) ≫ x.1) ≫ R.d i (i + 1) = 0 := by
  rcases x with ⟨hcur, hnext, heq⟩
  change (f.f i - P.d i (i + 1) ≫ hcur) ≫ R.d i (i + 1) = 0
  rw [Preadditive.sub_comp, f.comm i (i + 1), heq, Preadditive.comp_add,
    ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp, zero_add,
    ← Category.assoc, sub_self]

noncomputable def negativeStatePrev
    {P R : CochainComplex C ℤ} (f : P ⟶ R) (i : ℤ)
    (hR : R.Acyclic) (projP : ∀ k : ℤ, Projective (P.X k))
    (x : NegativeState f (i + 1)) : NegativeState f i := by
  let h := backwardStep f i hR projP x.1 (negative_residual f (i + 1) x)
  refine ⟨h, x.1, ?_⟩
  apply sub_eq_iff_eq_add'.mp
  exact (backwardStep_comp_differential f i hR projP x.1
    (negative_residual f (i + 1) x)).symm

noncomputable def negativeStateSeed
    {P R : CochainComplex C ℤ} (f : P ⟶ R)
    (hP : P.Acyclic) (hR : R.Acyclic) (projR : ∀ k : ℤ, Projective (R.X k))
    {J : C} [Projective J] (a : P.cycles 0 ⟶ J) (b : J ⟶ R.cycles 0)
    (hab : cyclesMap f 0 = a ≫ b) : NegativeState f (-1) := by
  let h0 := zeroSeed hR a b
  let h1 := forwardStepZero f hP projR h0 (zeroSeed_cycles_zero f hR a b hab)
  refine ⟨?_, ?_, ?_⟩
  · convert h0 using 1; norm_num
  · convert h1 using 1 <;> norm_num
  · apply sub_eq_iff_eq_add'.mp
    change f.f 0 - P.d 0 1 ≫ h1 = h0 ≫ R.d (-1) 0
    rw [differential_comp_forwardStepZero f hP projR h0
      (zeroSeed_cycles_zero f hR a b hab)]
    exact sub_sub_cancel _ _

noncomputable def negativeStates
    {P R : CochainComplex C ℤ} (f : P ⟶ R)
    (hP : P.Acyclic) (hR : R.Acyclic) (projP : ∀ k : ℤ, Projective (P.X k))
    (projR : ∀ k : ℤ, Projective (R.X k))
    {J : C} [Projective J] (a : P.cycles 0 ⟶ J) (b : J ⟶ R.cycles 0)
    (hab : cyclesMap f 0 = a ≫ b) : (n : ℕ) → NegativeState f (-((n : ℤ) + 1))
  | 0 => by
      convert negativeStateSeed f hP hR projR a b hab using 1; norm_num
  | n + 1 => by
      let x := negativeStates f hP hR projP projR a b hab n
      have hi : -((n : ℤ) + 2) + 1 = -((n : ℤ) + 1) := by
        rw [neg_add, neg_add]
        ac_rfl
      have hx : NegativeState f (-((n : ℤ) + 2) + 1) := by
        rw [hi]
        exact x
      have hout : -(((n + 1 : ℕ) : ℤ) + 1) = -((n : ℤ) + 2) := by
        rw [Int.natCast_add, neg_add, neg_add]
        norm_num
        ac_rfl
      rw [hout]
      exact negativeStatePrev f (-((n : ℤ) + 2)) hR projP hx

end PretriangulatedV2.StableCategory.AcyclicNullHomotopy
