import PretriangulatedV2.StableCocycles
import PretriangulatedV2.Frobenius
import Mathlib.Algebra.Homology.Embedding.Connect
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
Lifting maps of zero cycles to maps of acyclic complexes.  The two one-sided
constructions below are deliberately stated over `ℕ`; they are the pieces
joined by `CochainComplex.ConnectData` for complexes indexed by `ℤ`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PretriangulatedV2.StableCategory.AcyclicMapLifting

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Nonnegative

/-- The consecutive-cycle row for a nonnegative cochain complex. -/
def cycleSequence (P : CochainComplex C ℕ) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (P.iCycles n) (P.toCycles n (n + 1)) (by
    apply (cancel_mono (P.iCycles (n + 1))).mp
    simp)

theorem cycleSequence_shortExact (P : CochainComplex C ℕ) (n : ℕ)
    (hP : P.ExactAt (n + 1)) : (cycleSequence P n).ShortExact := by
  have hex : (P.sc' n (n + 1) (n + 2)).Exact :=
    (P.exactAt_iff' n (n + 1) (n + 2) (by
      apply (ComplexShape.up ℕ).prev_eq'
      change n + 1 = n + 1
      rfl) (by
      apply (ComplexShape.up ℕ).next_eq'
      change (n + 1) + 1 = n + 2
      omega)).mp hP
  let e := P.cyclesIsoSc' n (n + 1) (n + 2) (by
    apply (ComplexShape.up ℕ).prev_eq'
    change n + 1 = n + 1
    rfl) (by
    apply (ComplexShape.up ℕ).next_eq'
    change (n + 1) + 1 = n + 2
    omega)
  have hsc : Epi (P.sc' n (n + 1) (n + 2)).toCycles := hex.epi_toCycles
  have hep : Epi (P.toCycles n (n + 1) ≫ e.hom) := by
    rw [HomologicalComplex.toCycles_cyclesIsoSc'_hom]
    exact hsc
  have hcomp : Epi ((P.toCycles n (n + 1) ≫ e.hom) ≫ e.inv) := by
    let _ : Epi (P.toCycles n (n + 1) ≫ e.hom) := hep
    infer_instance
  have hto : Epi (P.toCycles n (n + 1)) := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      hcomp
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ShortComplex.exact_of_f_is_kernel
    apply KernelFork.isLimitOfIsLimitOfIff'
      (P.cyclesIsKernel n (n + 1) (by
        apply (ComplexShape.up ℕ).next_eq'
        change n + 1 = n + 1
        rfl))
    intro W f
    change f ≫ P.d n (n + 1) = 0 ↔ f ≫ P.toCycles n (n + 1) = 0
    rw [← cancel_mono (P.iCycles (n + 1)), Category.assoc, toCycles_i, zero_comp]
  · dsimp [cycleSequence]; infer_instance
  · dsimp [cycleSequence]; exact hto

structure LiftData (P R : CochainComplex C ℕ) (n : ℕ) where
  f : P.X n ⟶ R.X n
  cycle : P.iCycles n ≫ f ≫ R.d n (n + 1) = 0

variable {P R : CochainComplex C ℕ}

/-- The cycle-level map forced by a component in the preceding degree. -/
noncomputable def cycleLift (n : ℕ) (hP : P.ExactAt (n + 1))
    [Injective (R.X (n + 1))] (x : LiftData P R n) :
    P.cycles (n + 1) ⟶ R.X (n + 1) :=
  (cycleSequence_shortExact P n hP).exact.descToInjective
    (x.f ≫ R.d n (n + 1)) x.cycle

theorem toCycles_cycleLift (n : ℕ) (hP : P.ExactAt (n + 1))
    [Injective (R.X (n + 1))] (x : LiftData P R n) :
    P.toCycles n (n + 1) ≫ cycleLift n hP x = x.f ≫ R.d n (n + 1) := by
  simpa [cycleLift, cycleSequence] using
    (cycleSequence_shortExact P n hP).exact.comp_descToInjective
      (x.f ≫ R.d n (n + 1)) x.cycle

/-- Extend one degree to the right.  Exactness is used only for the actual
cycle row of the source, while injectivity supplies the ambient extension. -/
noncomputable def forward (n : ℕ) (hP : P.ExactAt (n + 1)) [Injective (R.X (n + 1))]
    (x : LiftData P R n) : LiftData P R (n + 1) := by
  letI : Epi (P.toCycles n (n + 1)) := (cycleSequence_shortExact P n hP).epi_g
  refine ⟨Injective.factorThru (cycleLift n hP x) (P.iCycles (n + 1)), ?_⟩
  have ht : cycleLift n hP x ≫ R.d (n + 1) ((n + 1) + 1) = 0 := by
    apply (cancel_epi (P.toCycles n (n + 1))).mp
    rw [← Category.assoc, toCycles_cycleLift,
      Category.assoc, HomologicalComplex.d_comp_d, comp_zero, comp_zero]
  rw [Injective.comp_factorThru_assoc, ht]

theorem forward_comm (n : ℕ) (hP : P.ExactAt (n + 1)) [Injective (R.X (n + 1))]
    (x : LiftData P R n) :
    x.f ≫ R.d n (n + 1) = P.d n (n + 1) ≫ (forward n hP x).f := by
  dsimp [forward]
  rw [← P.toCycles_i n (n + 1)]
  rw [Category.assoc, Injective.comp_factorThru, toCycles_cycleLift]

/-- A map on zero cycles has an ambient degree-zero extension. -/
noncomputable def zero (f : P.cycles 0 ⟶ R.cycles 0) [Injective (R.X 0)] :
    LiftData P R 0 := by
  refine ⟨Injective.factorThru (f ≫ R.iCycles 0) (P.iCycles 0), ?_⟩
  rw [Injective.comp_factorThru_assoc, Category.assoc, R.iCycles_d, comp_zero]

theorem zero_restrict (f : P.cycles 0 ⟶ R.cycles 0) [Injective (R.X 0)] :
    P.iCycles 0 ≫ (zero f).f = f ≫ R.iCycles 0 := by
  exact Injective.comp_factorThru _ _

variable (hP : ∀ n : ℕ, P.ExactAt (n + 1))
  [∀ n : ℕ, Injective (R.X n)]

noncomputable def data (f : P.cycles 0 ⟶ R.cycles 0) : ∀ n : ℕ, LiftData P R n
  | 0 => zero f
  | n + 1 => forward n (hP n) (data f n)

noncomputable def map (f : P.cycles 0 ⟶ R.cycles 0) : P ⟶ R where
  f n := (data hP f n).f
  comm' n m hnm := by
    rw [ComplexShape.up_Rel] at hnm
    subst m
    change (data hP f n).f ≫ R.d n (n + 1) =
      P.d n (n + 1) ≫ (forward n (hP n) (data hP f n)).f
    exact forward_comm n (hP n) (data hP f n)

theorem map_cycles_zero (f : P.cycles 0 ⟶ R.cycles 0) :
    cyclesMap (map hP f) 0 = f := by
  apply (cancel_mono (R.iCycles 0)).mp
  rw [cyclesMap_i]
  change P.iCycles 0 ≫ (zero f).f = f ≫ R.iCycles 0
  exact zero_restrict f

end Nonnegative

namespace Nonpositive

variable {P R : ChainComplex C ℕ}

/-- Exactness of the three consecutive terms of a chain complex. -/
theorem sc'_exact (R : ChainComplex C ℕ) (n : ℕ) (hR : R.ExactAt (n + 1)) :
    (R.sc' (n + 2) (n + 1) n).Exact :=
  (R.exactAt_iff' (n + 2) (n + 1) n (by
    apply (ComplexShape.down ℕ).prev_eq'
    rfl) (by
    apply (ComplexShape.down ℕ).next_eq'
    rfl)).mp hR

/-- One projective lift in the nonpositive direction. -/
noncomputable def next (n : ℕ) (hR : R.ExactAt (n + 1)) [Projective (P.X (n + 2))]
    (p : Σ' (f : P.X n ⟶ R.X n) (f' : P.X (n + 1) ⟶ R.X (n + 1)),
      f' ≫ R.d (n + 1) n = P.d (n + 1) n ≫ f) :
    Σ' f'' : P.X (n + 2) ⟶ R.X (n + 2),
      f'' ≫ R.d (n + 2) (n + 1) = P.d (n + 2) (n + 1) ≫ p.2.1 := by
  let e := sc'_exact R n hR
  refine ⟨e.liftFromProjective (P.d (n + 2) (n + 1) ≫ p.2.1) ?_, ?_⟩
  · change (P.d (n + 2) (n + 1) ≫ p.2.1) ≫ R.d (n + 1) n = 0
    rw [Category.assoc, p.2.2, ← Category.assoc, HomologicalComplex.d_comp_d,
      zero_comp]
  · exact e.liftFromProjective_comp _ _

/-- Extend a prescribed pair of boundary components to an actual chain map.
The target need only be exact and the source degreewise projective. -/
noncomputable def map (hR : ∀ n : ℕ, R.ExactAt (n + 1))
    [∀ n : ℕ, Projective (P.X n)]
    (zero : P.X 0 ⟶ R.X 0) (one : P.X 1 ⟶ R.X 1)
    (one_zero_comm : one ≫ R.d 1 0 = P.d 1 0 ≫ zero) : P ⟶ R :=
  ChainComplex.mkHom P R zero one one_zero_comm
    (fun n p => next n (hR n) p)

@[simp]
theorem map_f_zero (hR : ∀ n : ℕ, R.ExactAt (n + 1))
    [∀ n : ℕ, Projective (P.X n)]
    (zero : P.X 0 ⟶ R.X 0) (one : P.X 1 ⟶ R.X 1)
    (one_zero_comm : one ≫ R.d 1 0 = P.d 1 0 ≫ zero) :
    (map hR zero one one_zero_comm).f 0 = zero :=
  ChainComplex.mkHom_f_0 _ _ _ _ _ _

@[simp]
theorem map_f_one (hR : ∀ n : ℕ, R.ExactAt (n + 1))
    [∀ n : ℕ, Projective (P.X n)]
    (zero : P.X 0 ⟶ R.X 0) (one : P.X 1 ⟶ R.X 1)
    (one_zero_comm : one ≫ R.d 1 0 = P.d 1 0 ≫ zero) :
    (map hR zero one one_zero_comm).f 1 = one :=
  ChainComplex.mkHom_f_1 _ _ _ _ _ _

end Nonpositive

namespace Connecting

/-- The nonpositive chain half of an integer-indexed cochain complex. -/
abbrev K (P : CochainComplex C ℤ) : ChainComplex C ℕ :=
  P.restriction (ComplexShape.embeddingUpIntLE (-1))

/-- The nonnegative cochain half of an integer-indexed cochain complex. -/
abbrev L (P : CochainComplex C ℤ) : CochainComplex C ℕ :=
  P.restriction (ComplexShape.embeddingUpIntGE 0)

/-- The actual connecting differential, transported through Mathlib's
restriction identifications. -/
def data (P : CochainComplex C ℤ) : CochainComplex.ConnectData (K P) (L P) where
  d₀ := (P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1)) (by simp)).hom ≫
    P.d (-1) 0 ≫ (P.restrictionXIso (ComplexShape.embeddingUpIntGE 0) (by simp)).inv
  comp_d₀ := by
    dsimp only [K, L]
    rw [HomologicalComplex.restriction_d_eq (K := P)
      (e := ComplexShape.embeddingUpIntLE (-1)) (i' := -2) (j' := -1) (by simp) (by simp)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [HomologicalComplex.d_comp_d_assoc P (-2) (-1) 0]
    simp
  d₀_comp := by
    dsimp only [K, L]
    rw [HomologicalComplex.restriction_d_eq (K := P)
      (e := ComplexShape.embeddingUpIntGE 0) (i' := 0) (j' := 1) (by simp) (by simp)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [HomologicalComplex.d_comp_d_assoc P (-1) 0 1]
    simp

/-- Acyclicity transports to the nonnegative restriction. -/
theorem L_exactAt (P : CochainComplex C ℤ) (h : P.Acyclic) (n : ℕ) :
    (L P).ExactAt (n + 1) := by
  rw [(L P).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  have hex := (P.exactAt_iff' (n : ℤ) (n + 1) (n + 2) (by
    apply (ComplexShape.up ℤ).prev_eq'
    change (n : ℤ) + 1 = n + 1
    rfl) (by
    apply (ComplexShape.up ℤ).next_eq'
    change (n : ℤ) + 1 + 1 = n + 2
    omega)).mp (h (n + 1))
  let e₁ := P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := n) (i' := (n : ℤ)) (by simp)
  let e₂ := P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := n + 1) (i' := (n + 1 : ℤ)) (by simp)
  let e₃ := P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := n + 2) (i' := (n + 2 : ℤ)) (by simp)
  let e : (L P).sc' n (n + 1) (n + 2) ≅ P.sc' (n : ℤ) (n + 1) (n + 2) :=
    ShortComplex.isoMk e₁ e₂ e₃
      (by
        change e₁.hom ≫ P.d (n : ℤ) (n + 1) =
          (P.restriction (ComplexShape.embeddingUpIntGE 0)).d n (n + 1) ≫ e₂.hom
        rw [HomologicalComplex.restriction_d_eq (K := P)
          (e := ComplexShape.embeddingUpIntGE 0) (i' := (n : ℤ))
          (j' := (n + 1 : ℤ)) (by simp) (by simp)]
        simp [e₁, e₂])
      (by
        change e₂.hom ≫ P.d (n + 1 : ℤ) (n + 2) =
          (P.restriction (ComplexShape.embeddingUpIntGE 0)).d (n + 1) (n + 2) ≫ e₃.hom
        rw [HomologicalComplex.restriction_d_eq (K := P)
          (e := ComplexShape.embeddingUpIntGE 0) (i' := (n + 1 : ℤ))
          (j' := (n + 2 : ℤ)) (by simp) (by simp)]
        simp [e₂, e₃])
  exact ShortComplex.exact_of_iso e.symm hex

/-- Acyclicity transports to the nonpositive restriction. -/
theorem K_exactAt (P : CochainComplex C ℤ) (h : P.Acyclic) (n : ℕ) :
    (K P).ExactAt (n + 1) := by
  rw [(K P).exactAt_iff' (n + 2) (n + 1) n
    (by apply (ComplexShape.down ℕ).prev_eq'; rfl)
    (by apply (ComplexShape.down ℕ).next_eq'; rfl)]
  have hex := (P.exactAt_iff' (Int.negSucc (n + 2)) (Int.negSucc (n + 1)) (Int.negSucc n) (by
    apply (ComplexShape.up ℤ).prev_eq'
    change Int.negSucc (n + 2) + 1 = Int.negSucc (n + 1)
    rfl) (by
    apply (ComplexShape.up ℤ).next_eq'
    change Int.negSucc (n + 1) + 1 = Int.negSucc n
    rfl)).mp (h (Int.negSucc (n + 1)))
  let e₁ := P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := n + 2) (i' := Int.negSucc (n + 2)) (by
      change -1 - (n + 2 : ℤ) = Int.negSucc (n + 2)
      omega)
  let e₂ := P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := n + 1) (i' := Int.negSucc (n + 1)) (by
      change -1 - (n + 1 : ℤ) = Int.negSucc (n + 1)
      omega)
  let e₃ := P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := n) (i' := Int.negSucc n) (by
      change -1 - (n : ℤ) = Int.negSucc n
      omega)
  let e : (K P).sc' (n + 2) (n + 1) n ≅
      P.sc' (Int.negSucc (n + 2)) (Int.negSucc (n + 1)) (Int.negSucc n) :=
    ShortComplex.isoMk e₁ e₂ e₃
      (by
        change e₁.hom ≫ P.d (Int.negSucc (n + 2)) (Int.negSucc (n + 1)) =
          (P.restriction (ComplexShape.embeddingUpIntLE (-1))).d (n + 2) (n + 1) ≫ e₂.hom
        rw [HomologicalComplex.restriction_d_eq (K := P)
          (e := ComplexShape.embeddingUpIntLE (-1)) (i' := Int.negSucc (n + 2))
          (j' := Int.negSucc (n + 1)) (by
            change -1 - (n + 2 : ℤ) = Int.negSucc (n + 2)
            omega) (by
            change -1 - (n + 1 : ℤ) = Int.negSucc (n + 1)
            omega)]
        simp [e₁, e₂])
      (by
        change e₂.hom ≫ P.d (Int.negSucc (n + 1)) (Int.negSucc n) =
          (P.restriction (ComplexShape.embeddingUpIntLE (-1))).d (n + 1) n ≫ e₃.hom
        rw [HomologicalComplex.restriction_d_eq (K := P)
          (e := ComplexShape.embeddingUpIntLE (-1)) (i' := Int.negSucc (n + 1))
          (j' := Int.negSucc n) (by
            change -1 - (n + 1 : ℤ) = Int.negSucc (n + 1)
            omega) (by
            change -1 - (n : ℤ) = Int.negSucc n
            omega)]
        simp [e₂, e₃])
  exact ShortComplex.exact_of_iso e.symm hex

theorem L_projective (P : CochainComplex C ℤ)
    (h : ∀ n : ℤ, Projective (P.X n)) (n : ℕ) : Projective ((L P).X n) := by
  simpa [L] using h n

theorem K_projective (P : CochainComplex C ℤ)
    (h : ∀ n : ℤ, Projective (P.X n)) (n : ℕ) : Projective ((K P).X n) := by
  simpa [K] using h (-1 - n)

/-- Cycles in degree zero commute with the nonnegative restriction. -/
noncomputable def Lcycles0Iso (P : CochainComplex C ℤ) :
    (L P).cycles 0 ≅ P.cycles 0 :=
  P.restrictionCyclesIso (ComplexShape.embeddingUpIntGE 0) 0 1 (by simp)
    (j' := 0) (k' := 1) (by simp) (by simp) (by simp)

theorem Lcycles0Iso_hom_iCycles (P : CochainComplex C ℤ) :
    (Lcycles0Iso P).hom ≫ P.iCycles 0 =
      (L P).iCycles 0 ≫
      (P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
        (i := 0) (i' := (0 : ℤ)) (by simp)).hom := by
  simp [Lcycles0Iso]

/-- In an acyclic complex, a differential has the expected epimorphic
factorisation through the next cycle object. -/
theorem toCycles_epi (P : CochainComplex C ℤ) (h : P.Acyclic) (n : ℤ) :
    Epi (P.toCycles n (n + 1)) := by
  have hex : (P.sc' n (n + 1) (n + 2)).Exact :=
    (P.exactAt_iff' n (n + 1) (n + 2) (by
      apply (ComplexShape.up ℤ).prev_eq'
      change n + 1 = n + 1
      rfl) (by
      apply (ComplexShape.up ℤ).next_eq'
      change n + 1 + 1 = n + 2
      omega)).mp (h (n + 1))
  let e := P.cyclesIsoSc' n (n + 1) (n + 2) (by
    apply (ComplexShape.up ℤ).prev_eq'
    change n + 1 = n + 1
    rfl) (by
    apply (ComplexShape.up ℤ).next_eq'
    change n + 1 + 1 = n + 2
    omega)
  have he : Epi (P.toCycles n (n + 1) ≫ e.hom) := by
    rw [HomologicalComplex.toCycles_cyclesIsoSc'_hom]
    exact hex.epi_toCycles
  have hi : Epi ((P.toCycles n (n + 1) ≫ e.hom) ≫ e.inv) := by
    let _ : Epi (P.toCycles n (n + 1) ≫ e.hom) := he
    infer_instance
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hi

/-- The component in degree `-1` induced by an ambient degree-zero map. -/
noncomputable def negativeZero (P R : CochainComplex C ℤ) (hR : R.Acyclic)
    [Projective (P.X (-1))] (a : P.X 0 ⟶ R.X 0)
    (ha : P.d (-1) 0 ≫ a ≫ R.d 0 1 = 0) : P.X (-1) ⟶ R.X (-1) := by
  letI : Epi (R.toCycles (-1) 0) := toCycles_epi R hR (-1)
  exact Projective.factorThru
    (R.liftCycles (P.d (-1) 0 ≫ a) 1 (by simp)
      (by simpa only [Category.assoc] using ha))
    (R.toCycles (-1) 0)

theorem negativeZero_comm (P R : CochainComplex C ℤ) (hR : R.Acyclic)
    [Projective (P.X (-1))] (a : P.X 0 ⟶ R.X 0)
    (ha : P.d (-1) 0 ≫ a ≫ R.d 0 1 = 0) :
    negativeZero P R hR a ha ≫ R.d (-1) 0 = P.d (-1) 0 ≫ a := by
  dsimp [negativeZero]
  rw [← R.toCycles_i (-1) 0, ← Category.assoc, Projective.factorThru_comp,
    R.liftCycles_i]

/-- The degree `-2` seed for the nonpositive recursion. -/
noncomputable def negativeOne (P R : CochainComplex C ℤ) (hR : R.Acyclic)
    [Projective (P.X (-1))] [Projective (P.X (-2))]
    (a : P.X 0 ⟶ R.X 0) (ha : P.d (-1) 0 ≫ a ≫ R.d 0 1 = 0) :
    P.X (-2) ⟶ R.X (-2) := by
  let b := negativeZero P R hR a ha
  have hb : P.d (-2) (-1) ≫ b ≫ R.d (-1) 0 = 0 := by
    dsimp [b]
    rw [negativeZero_comm]
    rw [HomologicalComplex.d_comp_d_assoc, zero_comp]
  letI : Epi (R.toCycles (-2) (-1)) := toCycles_epi R hR (-2)
  exact Projective.factorThru
    (R.liftCycles (P.d (-2) (-1) ≫ b) 0 (by simp)
      (by simpa only [Category.assoc] using hb))
    (R.toCycles (-2) (-1))

theorem negativeOne_comm (P R : CochainComplex C ℤ) (hR : R.Acyclic)
    [Projective (P.X (-1))] [Projective (P.X (-2))]
    (a : P.X 0 ⟶ R.X 0) (ha : P.d (-1) 0 ≫ a ≫ R.d 0 1 = 0) :
    negativeOne P R hR a ha ≫ R.d (-2) (-1) =
      P.d (-2) (-1) ≫ negativeZero P R hR a ha := by
  dsimp [negativeOne]
  rw [← R.toCycles_i (-2) (-1), ← Category.assoc, Projective.factorThru_comp,
    R.liftCycles_i]

noncomputable def negativeKZero (P R : CochainComplex C ℤ) (hR : R.Acyclic)
    [Projective (P.X (-1))] (a : P.X 0 ⟶ R.X 0)
    (ha : P.d (-1) 0 ≫ a ≫ R.d 0 1 = 0) : (K P).X 0 ⟶ (K R).X 0 :=
  (P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := 0) (i' := (-1 : ℤ)) (by simp)).hom ≫
  negativeZero P R hR a ha ≫
  (R.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := 0) (i' := (-1 : ℤ)) (by simp)).inv

noncomputable def negativeKOne (P R : CochainComplex C ℤ) (hR : R.Acyclic)
    [Projective (P.X (-1))] [Projective (P.X (-2))]
    (a : P.X 0 ⟶ R.X 0)
    (ha : P.d (-1) 0 ≫ a ≫ R.d 0 1 = 0) : (K P).X 1 ⟶ (K R).X 1 :=
  (P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := 1) (i' := (-2 : ℤ)) (by simp)).hom ≫
  negativeOne P R hR a ha ≫
  (R.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := 1) (i' := (-2 : ℤ)) (by simp)).inv

theorem negativeK_comm (P R : CochainComplex C ℤ) (hR : R.Acyclic)
    [Projective (P.X (-1))] [Projective (P.X (-2))]
    (a : P.X 0 ⟶ R.X 0) (ha : P.d (-1) 0 ≫ a ≫ R.d 0 1 = 0) :
    negativeKOne P R hR a ha ≫ (K R).d 1 0 =
      (K P).d 1 0 ≫ negativeKZero P R hR a ha := by
  let eP₁ := P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := 1) (i' := (-2 : ℤ)) (by simp)
  let eP₀ := P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := 0) (i' := (-1 : ℤ)) (by simp)
  let eR₁ := R.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := 1) (i' := (-2 : ℤ)) (by simp)
  let eR₀ := R.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
    (i := 0) (i' := (-1 : ℤ)) (by simp)
  have hPd : eP₁.hom ≫ P.d (-2) (-1) = (K P).d 1 0 ≫ eP₀.hom := by
    change eP₁.hom ≫ P.d (-2) (-1) =
      (P.restriction (ComplexShape.embeddingUpIntLE (-1))).d 1 0 ≫ eP₀.hom
    rw [HomologicalComplex.restriction_d_eq (K := P)
      (e := ComplexShape.embeddingUpIntLE (-1)) (i' := (-2 : ℤ)) (j' := (-1 : ℤ))
      (by simp) (by simp)]
    simp [eP₁, eP₀]
  have hRd : eR₁.hom ≫ R.d (-2) (-1) = (K R).d 1 0 ≫ eR₀.hom := by
    change eR₁.hom ≫ R.d (-2) (-1) =
      (R.restriction (ComplexShape.embeddingUpIntLE (-1))).d 1 0 ≫ eR₀.hom
    rw [HomologicalComplex.restriction_d_eq (K := R)
      (e := ComplexShape.embeddingUpIntLE (-1)) (i' := (-2 : ℤ)) (j' := (-1 : ℤ))
      (by simp) (by simp)]
    simp [eR₁, eR₀]
  have hRd' : eR₁.inv ≫ (K R).d 1 0 = R.d (-2) (-1) ≫ eR₀.inv := by
    apply (cancel_mono eR₀.hom).mp
    simp only [Category.assoc]
    rw [← hRd]
    simp
  dsimp [negativeKOne, negativeKZero]
  simp only [Category.assoc]
  rw [hRd', ← Category.assoc (negativeOne P R hR a ha) (R.d (-2) (-1)) eR₀.inv,
    negativeOne_comm P R hR a ha]
  simp only [← Category.assoc]
  rw [hPd]

variable [FrobeniusAbelian C]

/-- The lift on the nonnegative restriction, transported from a degree-zero
cycle map. -/
noncomputable def positiveMap (P R : CochainComplex C ℤ)
    (hP : P.Acyclic) (hRproj : ∀ n : ℤ, Projective (R.X n))
    (f : P.cycles 0 ⟶ R.cycles 0) : L P ⟶ L R := by
  letI : ∀ n : ℕ, Projective ((L R).X n) := fun n => L_projective R hRproj n
  letI : ∀ n : ℕ, Injective ((L R).X n) := fun n =>
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  exact Nonnegative.map (fun n => L_exactAt P hP n)
    ((Lcycles0Iso P).hom ≫ f ≫ (Lcycles0Iso R).inv)

/-- The ambient degree-zero component underlying `positiveMap`. -/
noncomputable def ambientZero (P R : CochainComplex C ℤ)
    (hP : P.Acyclic) (hRproj : ∀ n : ℤ, Projective (R.X n))
    (f : P.cycles 0 ⟶ R.cycles 0) : P.X 0 ⟶ R.X 0 :=
  (P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := 0) (i' := (0 : ℤ)) (by simp)).inv ≫
  (positiveMap P R hP hRproj f).f 0 ≫
  (R.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := 0) (i' := (0 : ℤ)) (by simp)).hom

theorem ambientZero_cycle (P R : CochainComplex C ℤ)
    (hP : P.Acyclic) (hRproj : ∀ n : ℤ, Projective (R.X n))
    (f : P.cycles 0 ⟶ R.cycles 0) :
    P.d (-1) 0 ≫ ambientZero P R hP hRproj f ≫ R.d 0 1 = 0 := by
  dsimp [ambientZero]
  rw [← Category.assoc]
  let p := positiveMap P R hP hRproj f
  let eP := P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := 0) (i' := (0 : ℤ)) (by simp)
  let eR := R.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := 0) (i' := (0 : ℤ)) (by simp)
  let eR1 := R.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := 1) (i' := (1 : ℤ)) (by simp)
  have hp := p.comm 0 1
  have hRdiff : eR.hom ≫ R.d 0 1 = (L R).d 0 1 ≫ eR1.hom := by
    change eR.hom ≫ R.d 0 1 =
      (R.restriction (ComplexShape.embeddingUpIntGE 0)).d 0 1 ≫ eR1.hom
    rw [HomologicalComplex.restriction_d_eq (K := R)
      (e := ComplexShape.embeddingUpIntGE 0) (i' := (0 : ℤ)) (j' := (1 : ℤ))
      (by simp) (by simp)]
    simp [eR, eR1]
  dsimp [p] at hp
  dsimp [eR] at hRdiff
  rw [Category.assoc, Category.assoc, Category.assoc, hRdiff]
  rw [← Category.assoc ((positiveMap P R hP hRproj f).f 0) ((L R).d 0 1) eR1.hom, hp]
  rw [HomologicalComplex.restriction_d_eq (K := P)
    (e := ComplexShape.embeddingUpIntGE 0) (i' := (0 : ℤ)) (j' := (1 : ℤ))
    (by simp) (by simp)]
  simp

theorem connecting_boundary (P R : CochainComplex C ℤ)
    (hP : P.Acyclic) (hR : R.Acyclic)
    (hPproj : ∀ n : ℤ, Projective (P.X n))
    (hRproj : ∀ n : ℤ, Projective (R.X n))
    (f : P.cycles 0 ⟶ R.cycles 0) :
    let a := ambientZero P R hP hRproj f
    let ha := ambientZero_cycle P R hP hRproj f
    negativeKZero P R hR a ha ≫ (data R).d₀ =
      (data P).d₀ ≫ (positiveMap P R hP hRproj f).f 0 := by
  dsimp only
  rw [show negativeKZero P R hR _ _ =
    (P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
      (i := 0) (i' := (-1 : ℤ)) (by simp)).hom ≫
    negativeZero P R hR _ _ ≫
    (R.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
      (i := 0) (i' := (-1 : ℤ)) (by simp)).inv by rfl]
  dsimp [data]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (negativeZero P R hR _ _) (R.d (-1) 0)
    (R.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
      (i := 0) (i' := (0 : ℤ)) (by simp)).inv,
    negativeZero_comm]
  simp [ambientZero]

/-- The joined map before conjugating back to the original complexes. -/
noncomputable def joinedMap (P R : CochainComplex C ℤ)
    (hP : P.Acyclic) (hR : R.Acyclic)
    (hPproj : ∀ n : ℤ, Projective (P.X n))
    (hRproj : ∀ n : ℤ, Projective (R.X n))
    (f : P.cycles 0 ⟶ R.cycles 0) :
    (data P).cochainComplex ⟶ (data R).cochainComplex := by
  letI : ∀ n : ℕ, Projective ((K P).X n) := fun n => K_projective P hPproj n
  let a := ambientZero P R hP hRproj f
  let ha := ambientZero_cycle P R hP hRproj f
  let k := Nonpositive.map (fun n => K_exactAt R hR n)
    (negativeKZero P R hR a ha) (negativeKOne P R hR a ha)
    (negativeK_comm P R hR a ha)
  exact (data P).map (data R) k (positiveMap P R hP hRproj f)
    (connecting_boundary P R hP hR hPproj hRproj f)


/-- The complex made by joining the two restrictions is canonically the
original integer-indexed complex. -/
noncomputable def connectedIso (P : CochainComplex C ℤ) :
    (data P).cochainComplex ≅ P :=
  Hom.isoOfComponents
    (fun n => match n with
      | .ofNat n => P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
          (i := n) (i' := (n : ℤ)) (by simp)
      | .negSucc n => P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
          (i := n) (i' := Int.negSucc n) (by
            change -1 - (n : ℤ) = Int.negSucc n
            omega))
    (by
      rintro (n | n) j h
      · rw [ComplexShape.up_Rel] at h
        subst j
        change
          (P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
            (i := n) (i' := (n : ℤ)) (by simp)).hom ≫ P.d (n : ℤ) (n + 1) =
          (P.restriction (ComplexShape.embeddingUpIntGE 0)).d n (n + 1) ≫
          (P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
            (i := n + 1) (i' := (n + 1 : ℤ)) (by simp)).hom
        rw [HomologicalComplex.restriction_d_eq (K := P)
          (e := ComplexShape.embeddingUpIntGE 0) (i' := (n : ℤ))
          (j' := (n + 1 : ℤ)) (by simp) (by simp)]
        simp
      · cases n with
        | zero =>
          rw [ComplexShape.up_Rel] at h
          subst j
          change
            (P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
              (i := 0) (i' := (-1 : ℤ)) (by simp)).hom ≫ P.d (-1) 0 =
            (data P).d₀ ≫
            (P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
              (i := 0) (i' := (0 : ℤ)) (by simp)).hom
          simp [data]
        | succ n =>
          rw [ComplexShape.up_Rel] at h
          subst j
          change
            (P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
              (i := n + 1) (i' := Int.negSucc (n + 1)) (by
                change -1 - (n + 1 : ℤ) = Int.negSucc (n + 1)
                omega)).hom ≫ P.d (Int.negSucc (n + 1)) (Int.negSucc n) =
            (P.restriction (ComplexShape.embeddingUpIntLE (-1))).d (n + 1) n ≫
            (P.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
              (i := n) (i' := Int.negSucc n) (by
                change -1 - (n : ℤ) = Int.negSucc n
                omega)).hom
          rw [HomologicalComplex.restriction_d_eq (K := P)
            (e := ComplexShape.embeddingUpIntLE (-1)) (i' := Int.negSucc (n + 1))
            (j' := Int.negSucc n) (by
              change -1 - (n + 1 : ℤ) = Int.negSucc (n + 1)
              omega) (by
              change -1 - (n : ℤ) = Int.negSucc n
              omega)]
          simp)

/-- The actual map of integer-indexed complexes obtained by joining the two
one-sided lifting constructions. -/
noncomputable def liftMap (P R : CochainComplex C ℤ)
    (hP : P.Acyclic) (hR : R.Acyclic)
    (hPproj : ∀ n : ℤ, Projective (P.X n))
    (hRproj : ∀ n : ℤ, Projective (R.X n))
    (f : P.cycles 0 ⟶ R.cycles 0) : P ⟶ R :=
  (connectedIso P).inv ≫ joinedMap P R hP hR hPproj hRproj f ≫ (connectedIso R).hom

end Connecting

end PretriangulatedV2.StableCategory.AcyclicMapLifting
