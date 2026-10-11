import PretriangulatedV2.HellerRecoveryEquivalence

/-!
# The actual Heller classification equivalence

An additive ambient autoequivalence and a compatible projective integer
shift determine a bijection between Heller parameters and actual
pretriangulated structures on the projective full subcategory. Both inverse
identities are proved from the genuine construction and recovery modules.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace PretriangulatedV2.HellerParameterRecovery

open HellerClassification HellerRecovery HellerRecoveryEquivalence
open StableCategory StableCategory.InjectiveComparison StableCategory.FrobeniusCommutation

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]
  [HasShift (Projectives (C := C)) ℤ]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]

variable (S : C ≌ C) [S.functor.Additive]
  (e : shiftFunctor (Projectives (C := C)) (1 : ℤ) ≅
    (projectiveEquivalence S).functor)

section Original

variable [Pretriangulated (Projectives (C := C))]

/-- Equality of distinguished classes determines the Heller comparison. -/
theorem delta_eq_recovered_of_distinguished_eq
    (p : StableHellerParameter S)
    (hclass : HellerClassification.distinguishedTriangles S p e =
      (Pretriangulated.distinguishedTriangles :
        Set (Triangle (Projectives (C := C))))) :
    p.delta = recoveredDelta S e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rcases X with ⟨M⟩
  let T := chosenTriangle M
  have hTorig : T ∈ (Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C)))) := chosenTriangle_distinguished M
  have hTp : T ∈ HellerClassification.distinguishedTriangles S p e := by
    rw [hclass]
    exact hTorig
  rcases hTp with ⟨N, E, a₀, a₁, a₂, h₀, h₁, h₂, hE⟩
  have hrec : E.stableComparison.hom =
      (recoveredDelta S e).hom.app
        ((projectiveStableQuotient (C := C)).obj N) :=
    extensionComparison_eq_recovered S e E T hTorig a₀ a₁ a₂ h₀ h₁ h₂
  have hp : E.stableComparison.hom = p.delta.hom.app
      ((projectiveStableQuotient (C := C)).obj N) :=
    (HellerExactness.deltaExact_iff_stableComparison S p E).mp hE
  have hN : p.delta.hom.app ((projectiveStableQuotient (C := C)).obj N) =
      (recoveredDelta S e).hom.app
        ((projectiveStableQuotient (C := C)).obj N) := hp.symm.trans hrec
  let k := extensionKernelIso S E T a₀ a₁ h₀
  let j : M ≅ N := chosenKernelIso M ≪≫ k.symm
  let qj := (projectiveStableQuotient (C := C)).map j.hom
  have hj : IsIso ((cube Cosyzygy.functor).map qj) :=
    inferInstanceAs (IsIso ((cube Cosyzygy.functor).mapIso
      ((projectiveStableQuotient (C := C)).mapIso j)).hom)
  change p.delta.hom.app ((projectiveStableQuotient (C := C)).obj M) =
    (recoveredDelta S e).hom.app
      ((projectiveStableQuotient (C := C)).obj M)
  apply (cancel_mono ((cube Cosyzygy.functor).map qj)).mp
  rw [← p.delta.hom.naturality qj,
    ← (recoveredDelta S e).hom.naturality qj, hN]

/-- Equality of distinguished classes determines the full Heller parameter;
the anticommutation fields are propositions. -/
theorem parameter_eq_recovered_of_distinguished_eq
    (p : StableHellerParameter S)
    (hclass : HellerClassification.distinguishedTriangles S p e =
      (Pretriangulated.distinguishedTriangles :
        Set (Triangle (Projectives (C := C))))) :
    p = recoveredParameter S e := by
  have hδ := delta_eq_recovered_of_distinguished_eq S e p hclass
  cases p
  simpa only [recoveredParameter, HellerParameter.mk.injEq] using hδ



end Original

/-- Section 3.3: genuine Heller parameters classify actual pretriangulated
structures on the projective category, for the specified compatible shift. -/
def classification :
    StableHellerParameter S ≃ Pretriangulated (Projectives (C := C)) where
  toFun p := HellerClassification.pretriangulated S p e
  invFun q :=
    letI : Pretriangulated (Projectives (C := C)) := q
    recoveredParameter S e
  left_inv p := by
    let _ : Pretriangulated (Projectives (C := C)) :=
      HellerClassification.pretriangulated S p e
    exact (parameter_eq_recovered_of_distinguished_eq S e p rfl).symm
  right_inv q := by
    let _ : Pretriangulated (Projectives (C := C)) := q
    exact recovered_pretriangulated_eq_original S e

@[simp] theorem classification_apply (p : StableHellerParameter S) :
    classification S e p = HellerClassification.pretriangulated S p e := rfl

/-- Distinct Heller parameters produce distinct actual pretriangulations. -/
theorem parameter_to_pretriangulated_injective :
    Function.Injective (fun p : StableHellerParameter S =>
      HellerClassification.pretriangulated S p e) :=
  (classification S e).injective

/-- Every actual compatible pretriangulation is produced by a Heller
parameter; this is surjectivity proved by the genuine recovery construction. -/
theorem parameter_to_pretriangulated_surjective :
    Function.Surjective (fun p : StableHellerParameter S =>
      HellerClassification.pretriangulated S p e) :=
  (classification S e).surjective


omit [HasShift (Projectives (C := C)) ℤ]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive] in
/-- The full classification using the integer shift actually constructed
from the ambient additive autoequivalence; no shift or triangulation is
supplied as a hypothesis. -/
def constructedClassification :
    letI := projectiveHasShift S
    letI : ∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive :=
      fun n => AutoequivalenceShift.shift_additive (projectiveEquivalence S) n
    StableHellerParameter S ≃ Pretriangulated (Projectives (C := C)) :=
  letI := projectiveHasShift S
  letI : ∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive :=
    fun n => AutoequivalenceShift.shift_additive (projectiveEquivalence S) n
  classification S (projectiveShiftOneIso S)

end PretriangulatedV2.HellerParameterRecovery
