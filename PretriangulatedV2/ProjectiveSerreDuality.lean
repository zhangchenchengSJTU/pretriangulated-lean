import PretriangulatedV2.SerreDuality
import PretriangulatedV2.Frobenius
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Extending projective Serre pairings to ambient objects

Only projective-projective Serre pairings are given as data. Chosen projective
covers extend these pairings to arbitrary ambient objects by a proved linear
duality; no ambient or stable Serre conclusion is a structure field.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Preadditive

namespace PretriangulatedV2

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [Abelian C]
  [Linear k C] (S : C ⥤ C) [S.Additive] [Functor.Linear k S]

/-- Raw natural Serre pairings restricted to actual ambient projectives. -/
structure ProjectiveSerreDuality where
  duality (P Q : C) [Projective P] [Projective Q] :
    (Q ⟶ S.obj P) ≃ₗ[k] Module.Dual k (P ⟶ Q)
  naturality_source {P P' Q : C} [Projective P] [Projective P'] [Projective Q]
      (f : P' ⟶ P) (g : P ⟶ Q) (a : Q ⟶ S.obj P') :
    duality P Q (a ≫ S.map f) g = duality P' Q a (f ≫ g)
  naturality_target {P Q Q' : C} [Projective P] [Projective Q] [Projective Q']
      (f : Q ⟶ Q') (g : P ⟶ Q) (a : Q' ⟶ S.obj P) :
    duality P Q (f ≫ a) g = duality P Q' a (g ≫ f)

namespace ProjectiveSerreDuality

variable {k C S} (D : ProjectiveSerreDuality k C S) [EnoughProjectives C]

omit [S.Additive] [Functor.Linear k S]

/-- The cover of the kernel followed by its kernel inclusion. -/
abbrev coverDifferential (W : C) :
    Projective.over (kernel (Projective.π W)) ⟶ Projective.over W :=
  Projective.π (kernel (Projective.π W)) ≫ kernel.ι (Projective.π W)

@[reassoc (attr := simp)]
lemma coverDifferential_π (W : C) : coverDifferential W ≫ Projective.π W = 0 := by
  simp [coverDifferential]

/-- The pairing value is independent of the chosen lift across the cover. -/
lemma pairing_cover_eq_of_lift {P W : C} [Projective P]
    (a : W ⟶ S.obj P) (f : P ⟶ W) (l : P ⟶ Projective.over W)
    (hl : l ≫ Projective.π W = f) :
    D.duality P (Projective.over W) (Projective.π W ≫ a) l =
      D.duality P (Projective.over W) (Projective.π W ≫ a)
        (Projective.factorThru f (Projective.π W)) := by
  let l₀ := Projective.factorThru f (Projective.π W)
  have hδ : (l - l₀) ≫ Projective.π W = 0 := by
    simp [l₀, sub_comp, hl]
  let b := kernel.lift (Projective.π W) (l - l₀) hδ
  let c := Projective.factorThru b (Projective.π (kernel (Projective.π W)))
  have hc : c ≫ coverDifferential W = l - l₀ := by
    simp [c, b, coverDifferential, ← Category.assoc]
  have hpair : D.duality P (Projective.over W) (Projective.π W ≫ a) (l - l₀) = 0 := by
    rw [← hc, ← D.naturality_target]
    simp [Category.assoc]
  simpa only [map_sub, sub_eq_zero] using hpair

/-- A morphism into the Serre image defines a linear functional on Hom from
the projective source. -/
def ambientFunctional {P W : C} [Projective P] (a : W ⟶ S.obj P) :
    Module.Dual k (P ⟶ W) where
  toFun f := D.duality P (Projective.over W) (Projective.π W ≫ a)
    (Projective.factorThru f (Projective.π W))
  map_add' f g := by
    rw [← D.pairing_cover_eq_of_lift a (f + g)
      (Projective.factorThru f (Projective.π W) + Projective.factorThru g (Projective.π W))
      (by simp [add_comp])]
    simp
  map_smul' r f := by
    rw [← D.pairing_cover_eq_of_lift a (r • f)
      (r • Projective.factorThru f (Projective.π W)) (by simp)]
    simp

lemma ambientFunctional_eq_of_lift {P W : C} [Projective P]
    (a : W ⟶ S.obj P) (f : P ⟶ W) (l : P ⟶ Projective.over W)
    (hl : l ≫ Projective.π W = f) :
    D.ambientFunctional a f = D.duality P (Projective.over W) (Projective.π W ≫ a) l :=
  (D.pairing_cover_eq_of_lift a f l hl).symm

/-- The extended pairing as a linear map before proving bijectivity. -/
def ambientDualityMap (P W : C) [Projective P] :
    (W ⟶ S.obj P) →ₗ[k] Module.Dual k (P ⟶ W) where
  toFun := D.ambientFunctional
  map_add' a b := by
    ext f
    simp [ambientFunctional, comp_add]
  map_smul' r a := by
    ext f
    simp [ambientFunctional]

lemma ambientDualityMap_injective (P W : C) [Projective P] :
    Function.Injective (D.ambientDualityMap P W) := by
  intro a b hab
  apply (cancel_epi (Projective.π W)).mp
  apply (D.duality P (Projective.over W)).injective
  ext l
  have h := congrArg (fun ℓ : Module.Dual k (P ⟶ W) ↦ ℓ (l ≫ Projective.π W)) hab
  change D.ambientFunctional a _ = D.ambientFunctional b _ at h
  simpa only [D.ambientFunctional_eq_of_lift a _ l rfl,
    D.ambientFunctional_eq_of_lift b _ l rfl] using h

lemma ambientDualityMap_surjective (P W : C) [Projective P] :
    Function.Surjective (D.ambientDualityMap P W) := by
  intro ℓ
  let μ := ℓ.comp (CategoryTheory.Linear.rightComp k P (Projective.π W))
  let a := (D.duality P (Projective.over W)).symm μ
  have ha : D.duality P (Projective.over W) a = μ :=
    (D.duality P (Projective.over W)).apply_symm_apply μ
  have hd : coverDifferential W ≫ a = 0 := by
    apply (D.duality P (Projective.over (kernel (Projective.π W)))).injective
    ext f
    rw [D.naturality_target, ha]
    simp [μ, Category.assoc]
  have hk : kernel.ι (Projective.π W) ≫ a = 0 := by
    apply (cancel_epi (Projective.π (kernel (Projective.π W)))).mp
    simpa only [coverDifferential, Category.assoc, comp_zero] using hd
  let g := Abelian.epiDesc (Projective.π W) a hk
  have hg : Projective.π W ≫ g = a := Abelian.comp_epiDesc _ _ _
  refine ⟨g, ?_⟩
  ext f
  change D.duality P (Projective.over W) (Projective.π W ≫ g)
    (Projective.factorThru f (Projective.π W)) = ℓ f
  rw [hg, ha]
  simp [μ]

/-- Projective-projective Serre data extend to arbitrary ambient targets. -/
def ambientDuality (P W : C) [Projective P] :
    (W ⟶ S.obj P) ≃ₗ[k] Module.Dual k (P ⟶ W) :=
  LinearEquiv.ofBijective (D.ambientDualityMap P W)
    ⟨D.ambientDualityMap_injective P W, D.ambientDualityMap_surjective P W⟩

@[simp]
lemma ambientDuality_apply {P W : C} [Projective P] (a : W ⟶ S.obj P) (f : P ⟶ W) :
    D.ambientDuality P W a f = D.ambientFunctional a f := rfl

lemma ambientDuality_naturality_source {P P' W : C} [Projective P] [Projective P']
    (f : P' ⟶ P) (g : P ⟶ W) (a : W ⟶ S.obj P') :
    D.ambientDuality P W (a ≫ S.map f) g = D.ambientDuality P' W a (f ≫ g) := by
  let l := Projective.factorThru g (Projective.π W)
  have hl : l ≫ Projective.π W = g := Projective.factorThru_comp _ _
  rw [ambientDuality_apply, ambientDuality_apply,
    D.ambientFunctional_eq_of_lift _ _ l hl,
    D.ambientFunctional_eq_of_lift _ _ (f ≫ l) (by simp [Category.assoc, hl])]
  simpa only [← Category.assoc] using
    D.naturality_source f l (Projective.π W ≫ a)

lemma ambientDuality_naturality_target {P W W' : C} [Projective P]
    (f : W ⟶ W') (g : P ⟶ W) (a : W' ⟶ S.obj P) :
    D.ambientDuality P W (f ≫ a) g = D.ambientDuality P W' a (g ≫ f) := by
  let l := Projective.factorThru g (Projective.π W)
  let r := Projective.factorThru (Projective.π W ≫ f) (Projective.π W')
  have hl : l ≫ Projective.π W = g := Projective.factorThru_comp _ _
  have hr : r ≫ Projective.π W' = Projective.π W ≫ f := Projective.factorThru_comp _ _
  rw [ambientDuality_apply, ambientDuality_apply,
    D.ambientFunctional_eq_of_lift _ _ l hl,
    D.ambientFunctional_eq_of_lift _ _ (l ≫ r) (by simp [Category.assoc, hr, ← hl])]
  rw [← D.naturality_target]
  simp only [← Category.assoc, hr]

/-- The paper's conventional orientation of the extended ambient duality. -/
def ambientHomDuality (P W : C) [Projective P] [FiniteDimensional k (P ⟶ W)] :
    (P ⟶ W) ≃ₗ[k] Module.Dual k (W ⟶ S.obj P) :=
  (Module.evalEquiv k (P ⟶ W)).trans (D.ambientDuality P W).dualMap

end ProjectiveSerreDuality

end PretriangulatedV2
