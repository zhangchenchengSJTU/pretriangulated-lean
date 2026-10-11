import PretriangulatedV2.YonedaHellerTransport
import PretriangulatedV2.CoherentLinear
import PretriangulatedV2.GeneratorCommShift
import PretriangulatedV2.SerreDuality
import PretriangulatedV2.ShiftLinear

/-!
# Original Calabi--Yau duality on the actual coherent projective category

The target integer action is the generated Heller action of the coherent
suspension extension. The original Yoneda generator comparison constructs
coherent commutation with this action. The distinct transported Yoneda action
is never identified by definitional equality with the generated action.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.CoherentCalabiYau

variable {k : Type w} [Field k] (D : Type u) [Category.{v} D]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Linear k D] [IsIdempotentComplete D]
  [∀ X Y : D, FiniteDimensional k (X ⟶ Y)]
  [Functor.Linear k (shiftFunctor D (1 : ℤ))]

abbrev Projectives := HellerClassification.Projectives (C := CoherentFunctors.Mod D)

local instance projectiveGeneratedShift : HasShift (Projectives D) ℤ :=
  HellerClassification.projectiveHasShift (CoherentFunctors.suspension (C := D))

/-- Actual additive Yoneda into ambient projectives is linear for the proved
canonical coherent-functor scalar action. -/
instance yonedaProjectives_linear : Functor.Linear k (YonedaHellerTransport.toProjectives D) where
  map_smul := by
    intro X Y f r
    apply ObjectProperty.hom_ext
    exact (CoherentFunctors.yoneda (C := D)).map_smul r f

instance yonedaEquivalence_linear :
    Functor.Linear k (YonedaHellerTransport.yonedaEquivalence D).functor := by
  change Functor.Linear k (YonedaHellerTransport.toProjectives D)
  infer_instance

/-- Genuine all-integer commutation with the generated Heller action. -/
@[instance_reducible]
def yonedaGeneratedCommShift :
    (YonedaHellerTransport.yonedaEquivalence D).functor.CommShift ℤ :=
  GeneratorCommShift.commutation
    (HellerClassification.projectiveEquivalence (CoherentFunctors.suspension (C := D)))
    (YonedaHellerTransport.toProjectives D)
    (YonedaHellerTransport.yonedaSuspensionIso D).symm

/-- The actual inverse equivalence therefore also commutes with every
integer of the generated action. -/
@[instance_reducible]
def inverseGeneratedCommShift :
    (YonedaHellerTransport.yonedaEquivalence D).inverse.CommShift ℤ := by
  letI := yonedaGeneratedCommShift D
  exact (YonedaHellerTransport.yonedaEquivalence D).commShiftInverse ℤ

/-- Restricting the original linear suspension to coherent projectives is
linear for the actual ambient scalar structure. -/
instance projectiveSuspension_linear : Functor.Linear k
    (HellerClassification.projectiveEquivalence (CoherentFunctors.suspension (C := D))).functor where
  map_smul := by
    intro P Q f r
    apply ObjectProperty.hom_ext
    exact (CoherentFunctors.suspension (C := D)).functor.map_smul r f.hom

omit [HasZeroObject D] [HasBinaryBiproducts D] [Pretriangulated D]
  [IsIdempotentComplete D] [∀ X Y : D, FiniteDimensional k (X ⟶ Y)] in
/-- Every generated target suspension is linear, derived from the original
linear suspension and its actual projective restriction. -/
theorem generatedShift_linear (d : ℤ) : Functor.Linear k (shiftFunctor (Projectives D) d) := by
  have : Functor.Linear k (shiftFunctor (Projectives D) (1 : ℤ)) :=
    Functor.linear_of_iso k
      (HellerClassification.projectiveShiftOneIso (CoherentFunctors.suspension (C := D))).symm
  exact shift_linear_of_one (k := k) d

/-- The inverse Yoneda equivalence gives actual linear Hom equivalences. -/
def inverseHomEquiv (X Y : Projectives D) :
    (X ⟶ Y) ≃ₗ[k]
      ((YonedaHellerTransport.yonedaEquivalence D).inverse.obj X ⟶
        (YonedaHellerTransport.yonedaEquivalence D).inverse.obj Y) where
  toEquiv := (Functor.FullyFaithful.ofFullyFaithful
    (YonedaHellerTransport.yonedaEquivalence D).inverse).homEquiv
  map_add' _f _g := (YonedaHellerTransport.yonedaEquivalence D).inverse.map_add
  map_smul' r f := (YonedaHellerTransport.yonedaEquivalence D).inverse.map_smul r f

/-- Linear transport along an actual original-category codomain iso. -/
def postcomposeIso {X Y Z : D} (e : Y ≅ Z) : (X ⟶ Y) ≃ₗ[k] (X ⟶ Z) :=
  LinearEquiv.ofLinearMap (Linear.rightComp k X e.hom) (Linear.rightComp k X e.inv)
    (by ext; simp) (by ext; simp)

/-- Original CY data and actual inverse shift commutation give the natural
comparison needed by the Serre pairing, for every integer exponent. -/
def inverseSerreComparison (R : SerreDuality k D) (d : ℤ)
    (hCY : R.equivalence.functor ≅ shiftFunctor D d) :
    shiftFunctor (Projectives D) d ⋙ (YonedaHellerTransport.yonedaEquivalence D).inverse ≅
      (YonedaHellerTransport.yonedaEquivalence D).inverse ⋙ R.equivalence.functor := by
  letI := inverseGeneratedCommShift D
  exact (YonedaHellerTransport.yonedaEquivalence D).inverse.commShiftIso d ≪≫
    Functor.isoWhiskerLeft _ hCY.symm

/-- Original Serre/CY data give genuine Serre duality on the actual coherent
projectives, with the literal generated Heller suspension by `d` as functor.
Both Hom-pairing naturality equations are proved through the actual inverse
Yoneda equivalence and its generated-action comparison. -/
def serreDuality (R : SerreDuality k D) (d : ℤ)
    (hCY : R.equivalence.functor ≅ shiftFunctor D d) : SerreDuality k (Projectives D) where
  equivalence := shiftEquiv (Projectives D) d
  functor_additive := by
    change (shiftFunctor (Projectives D) d).Additive
    exact AutoequivalenceShift.shift_additive
      (HellerClassification.projectiveEquivalence (CoherentFunctors.suspension (C := D))) d
  functor_linear := by
    change Functor.Linear k (shiftFunctor (Projectives D) d)
    exact generatedShift_linear D d
  duality X Y :=
    (((inverseHomEquiv D Y ((shiftFunctor (Projectives D) d).obj X)).trans
      (postcomposeIso D ((inverseSerreComparison D R d hCY).app X))).trans
      (R.duality ((YonedaHellerTransport.yonedaEquivalence D).inverse.obj X)
        ((YonedaHellerTransport.yonedaEquivalence D).inverse.obj Y))).trans
      (inverseHomEquiv D X Y).dualMap
  naturality_source := by
    intro X X' Y f g a
    let F := (YonedaHellerTransport.yonedaEquivalence D).inverse
    let e := inverseSerreComparison D R d hCY
    change R.duality (F.obj X) (F.obj Y)
      (F.map (a ≫ (shiftFunctor (Projectives D) d).map f) ≫ e.hom.app X) (F.map g) =
        R.duality (F.obj X') (F.obj Y) (F.map a ≫ e.hom.app X') (F.map (f ≫ g))
    have he : F.map ((shiftFunctor (Projectives D) d).map f) ≫ e.hom.app X =
        e.hom.app X' ≫ R.equivalence.functor.map (F.map f) := e.hom.naturality f
    rw [F.map_comp, Category.assoc, he, ← Category.assoc, F.map_comp]
    exact R.naturality_source (F.map f) (F.map g) (F.map a ≫ e.hom.app X')
  naturality_target := by
    intro X Y Y' f g a
    let F := (YonedaHellerTransport.yonedaEquivalence D).inverse
    let e := inverseSerreComparison D R d hCY
    change R.duality (F.obj X) (F.obj Y) (F.map (f ≫ a) ≫ e.hom.app X) (F.map g) =
      R.duality (F.obj X) (F.obj Y') (F.map a ≫ e.hom.app X) (F.map (g ≫ f))
    rw [F.map_comp, Category.assoc, F.map_comp]
    exact R.naturality_target (F.map f) (F.map g) (F.map a ≫ e.hom.app X)

/-- The resulting CY comparison is the identity on the literal generated
projective suspension, for every integer exponent. -/
def serreIsoShift (R : SerreDuality k D) (d : ℤ)
    (hCY : R.equivalence.functor ≅ shiftFunctor D d) :
    letI := HellerClassification.projectiveHasShift (CoherentFunctors.suspension (C := D))
    (serreDuality D R d hCY).equivalence.functor ≅ shiftFunctor (Projectives D) d :=
  Iso.refl _

end PretriangulatedV2.CoherentCalabiYau
