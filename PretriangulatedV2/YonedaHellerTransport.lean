import PretriangulatedV2.CoherentFunctors
import PretriangulatedV2.HellerClassification
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The actual Yoneda bridge for Heller recovery

The projective objects here belong to the genuine coherent-functor category.
The equivalences and suspension comparison are constructed from additive
Yoneda; no recovery parameter or triangulation is assumed in their fields.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.YonedaHellerTransport

variable (D : Type u) [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Additive Yoneda, with codomain the actual ambient projective full subcategory. -/
def toProjectives : D ⥤ HellerClassification.Projectives (C := CoherentFunctors.Mod D) :=
  (HellerClassification.projectives (C := CoherentFunctors.Mod D)).lift
    CoherentFunctors.yoneda (fun X => by
      change Projective ((CoherentFunctors.yoneda (C := D)).obj X)
      infer_instance)

instance toProjectives_full : (toProjectives D).Full := by
  unfold toProjectives
  infer_instance

instance toProjectives_faithful : (toProjectives D).Faithful := by
  unfold toProjectives
  infer_instance

instance toProjectives_additive : (toProjectives D).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (CoherentFunctors.yoneda (C := D)).map_add

instance toProjectives_essSurj [IsIdempotentComplete D] : (toProjectives D).EssSurj where
  mem_essImage P := by
    obtain ⟨X, ⟨e⟩⟩ := (CoherentFunctors.projective_iff_representable P.obj).mp P.property
    exact ⟨X, ⟨ObjectProperty.isoMk
      (HellerClassification.projectives (C := CoherentFunctors.Mod D)) e.symm⟩⟩

instance toProjectives_isEquivalence [IsIdempotentComplete D] :
    (toProjectives D).IsEquivalence where

/-- Split idempotents make the genuine Yoneda embedding an equivalence onto
all ambient projective coherent functors. -/
def yonedaEquivalence [IsIdempotentComplete D] :
    D ≌ HellerClassification.Projectives (C := CoherentFunctors.Mod D) :=
  (toProjectives D).asEquivalence

instance yonedaEquivalence_additive [IsIdempotentComplete D] :
    (yonedaEquivalence D).functor.Additive := inferInstanceAs (toProjectives D).Additive

/-- The full subcategories defined using both projective and injective, and
using projective alone, are actually equivalent by the Frobenius theorem. -/
def projectiveInjectiveBridge :
    (CoherentFunctors.projectiveInjectives (C := D)).FullSubcategory ≌
      HellerClassification.Projectives (C := CoherentFunctors.Mod D) :=
  (CategoryTheory.Equivalence.refl (C := CoherentFunctors.Mod D)).congrFullSubcategory (by
    ext F
    change Projective F ↔ Projective F ∧ Injective F
    exact ⟨fun h => ⟨h, (CoherentFunctors.projective_iff_injective F).mp h⟩, And.left⟩)

instance suspension_additive : (CoherentFunctors.suspension (C := D)).functor.Additive := by
  dsimp [CoherentFunctors.suspension]
  infer_instance

/-- The concrete suspension extension restricts on projectives to the
original suspension, through an actual natural Yoneda comparison. -/
def yonedaSuspensionIso :
    toProjectives D ⋙
      (HellerClassification.projectiveEquivalence (CoherentFunctors.suspension (C := D))).functor ≅
      shiftFunctor D (1 : ℤ) ⋙ toProjectives D :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk
      (HellerClassification.projectives (C := CoherentFunctors.Mod D))
      ((CoherentFunctors.yonedaSuspensionIso (C := D)).app X))
    (fun f => ObjectProperty.hom_ext _
      ((CoherentFunctors.yonedaSuspensionIso (C := D)).hom.naturality f))

section TransportedShift

variable [IsIdempotentComplete D]

/-- The original coherent integer shift is transported through the genuine
Yoneda equivalence. -/
@[instance_reducible]
def yonedaHasShift : HasShift (HellerClassification.Projectives
    (C := CoherentFunctors.Mod D)) ℤ :=
  AutoequivalenceShift.transportedHasShift (yonedaEquivalence D)

/-- Yoneda commutes with every transported integer shift, with coherence
proved by the library's induced-shift construction. -/
@[instance_reducible]
def yonedaCommShift :
    letI := yonedaHasShift D
    (yonedaEquivalence D).functor.CommShift ℤ :=
  Functor.CommShift.ofInduced (yonedaEquivalence D).functor ℤ
    (AutoequivalenceShift.transportedFunctor (yonedaEquivalence D))
    (AutoequivalenceShift.transportComparison (yonedaEquivalence D))

/-- The transported first shift is the actual restricted coherent suspension. -/
def transportedShiftOneIso :
    letI := yonedaHasShift D
    shiftFunctor (HellerClassification.Projectives (C := CoherentFunctors.Mod D)) (1 : ℤ) ≅
      (HellerClassification.projectiveEquivalence
        (CoherentFunctors.suspension (C := D))).functor := by
  letI := yonedaHasShift D
  exact ((Functor.whiskeringLeft D _ _).obj (toProjectives D)).preimageIso
    (AutoequivalenceShift.transportComparison (yonedaEquivalence D) (1 : ℤ) ≪≫
      (yonedaSuspensionIso D).symm)

end TransportedShift

namespace EquivalenceTransport

open CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {P : Type*} [Category P] [Preadditive P] [HasZeroObject P]
  [HasShift P ℤ] [∀ n : ℤ, (shiftFunctor P n).Additive]
  (e : D ≌ P) [e.functor.Additive] [e.inverse.CommShift ℤ]

/-- Pull back the actual distinguished class along the inverse equivalence. -/
def distinguishedTriangles : Set (Triangle P) :=
  {T | e.inverse.mapTriangle.obj T ∈ distTriang D}

omit [HasBinaryBiproducts D] [HasZeroObject P] [Preadditive P]
  [∀ n : ℤ, (shiftFunctor P n).Additive] [e.functor.Additive] in
theorem isomorphic_distinguished (T₁ : Triangle P)
    (hT₁ : T₁ ∈ distinguishedTriangles D e) (T₂ : Triangle P) (i : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles D e :=
  Pretriangulated.isomorphic_distinguished _ hT₁ _ (e.inverse.mapTriangle.mapIso i)

omit [HasBinaryBiproducts D] [∀ n : ℤ, (shiftFunctor P n).Additive] in
theorem contractible_distinguished (X : P) :
    contractibleTriangle X ∈ distinguishedTriangles D e := by
  let i : e.inverse.mapTriangle.obj (contractibleTriangle X) ≅
      contractibleTriangle (e.inverse.obj X) :=
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((e.inverse.map_isZero (isZero_zero P)).iso (isZero_zero D))
      (by simp) (by simp) (by simp)
  exact Pretriangulated.isomorphic_distinguished _
    (Pretriangulated.contractible_distinguished (e.inverse.obj X)) _ i

omit [HasBinaryBiproducts D] [HasZeroObject P] [Preadditive P]
  [∀ n : ℤ, (shiftFunctor P n).Additive] [e.functor.Additive] in
theorem distinguished_cocone_triangle {X Y : P} (f : X ⟶ Y) :
    ∃ (Z : P) (g : Y ⟶ Z) (h : Z ⟶ (shiftFunctor P (1 : ℤ)).obj X),
      Triangle.mk f g h ∈ distinguishedTriangles D e := by
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle (e.inverse.map f)
  let Z' := e.inverse.objPreimage Z
  let i := e.inverse.objObjPreimageIso Z
  let g' : Y ⟶ Z' := e.inverse.preimage (g ≫ i.inv)
  let h' : Z' ⟶ (shiftFunctor P (1 : ℤ)).obj X :=
    e.inverse.preimage (i.hom ≫ h ≫ (e.inverse.commShiftIso (1 : ℤ)).inv.app X)
  refine ⟨Z', g', h', ?_⟩
  change e.inverse.mapTriangle.obj (Triangle.mk f g' h') ∈ distTriang D
  apply Pretriangulated.isomorphic_distinguished _ hT _
    (Triangle.isoMk (e.inverse.mapTriangle.obj (Triangle.mk f g' h'))
      (Triangle.mk (e.inverse.map f) g h) (Iso.refl _) (Iso.refl _) i ?_ ?_ ?_)
  · simp
  · simp [g']
  · simp [h']

omit [HasBinaryBiproducts D] [HasZeroObject P]
  [∀ n : ℤ, (shiftFunctor P n).Additive] in
theorem rotate_distinguished_triangle (T : Triangle P) :
    T ∈ distinguishedTriangles D e ↔ T.rotate ∈ distinguishedTriangles D e := by
  exact (Pretriangulated.rotate_distinguished_triangle (e.inverse.mapTriangle.obj T)).trans
    (Pretriangulated.distinguished_iff_of_iso ((e.inverse.mapTriangleRotateIso).app T))

omit [HasBinaryBiproducts D] [HasZeroObject P] [Preadditive P]
  [∀ n : ℤ, (shiftFunctor P n).Additive] [e.functor.Additive] in
theorem complete_distinguished_triangle_morphism (T₁ T₂ : Triangle P)
    (hT₁ : T₁ ∈ distinguishedTriangles D e) (hT₂ : T₂ ∈ distinguishedTriangles D e)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (hab : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ (shiftFunctor P (1 : ℤ)).map a = c ≫ T₂.mor₃ := by
  have hs : e.inverse.map T₁.mor₁ ≫ e.inverse.map b =
      e.inverse.map a ≫ e.inverse.map T₂.mor₁ := by
    rw [← e.inverse.map_comp, ← e.inverse.map_comp, hab]
  obtain ⟨c, hc₁, hc₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism
    (e.inverse.mapTriangle.obj T₁) (e.inverse.mapTriangle.obj T₂) hT₁ hT₂
    (e.inverse.map a) (e.inverse.map b) hs
  refine ⟨e.inverse.preimage c, ?_, ?_⟩
  · apply e.inverse.map_injective
    simpa only [Functor.mapTriangle_obj, Triangle.mk_mor₂,
      Functor.map_comp, Functor.map_preimage] using hc₁
  · apply e.inverse.map_injective
    apply (cancel_mono ((e.inverse.commShiftIso (1 : ℤ)).hom.app T₂.obj₁)).mp
    rw [e.inverse.map_comp, e.inverse.map_comp, e.inverse.map_preimage,
      Category.assoc, e.inverse.commShiftIso_hom_naturality, ← Category.assoc]
    simpa only [Functor.mapTriangle_obj, Triangle.mk_mor₃, Category.assoc] using hc₂

/-- An additive equivalence transports an existing pretriangulation by actual
proofs of all its axioms. -/
@[instance_reducible]
def pretriangulated : Pretriangulated P where
  distinguishedTriangles := distinguishedTriangles D e
  isomorphic_distinguished := isomorphic_distinguished D e
  contractible_distinguished := contractible_distinguished D e
  distinguished_cocone_triangle := distinguished_cocone_triangle D e
  rotate_distinguished_triangle := rotate_distinguished_triangle D e
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism D e

end EquivalenceTransport

section OriginalStructure

variable [IsIdempotentComplete D]

local instance : HasShift (HellerClassification.Projectives (C := CoherentFunctors.Mod D)) ℤ :=
  yonedaHasShift D

local instance shifted_additive (n : ℤ) :
    (shiftFunctor (HellerClassification.Projectives (C := CoherentFunctors.Mod D)) n).Additive :=
  AutoequivalenceShift.transportedFunctor_additive (yonedaEquivalence D) n

local instance : ∀ n : ℤ,
    (shiftFunctor (HellerClassification.Projectives (C := CoherentFunctors.Mod D)) n).Additive :=
  shifted_additive D

local instance : (yonedaEquivalence D).functor.CommShift ℤ := yonedaCommShift D

local instance : (yonedaEquivalence D).inverse.CommShift ℤ :=
  (yonedaEquivalence D).commShiftInverse ℤ

local instance : (yonedaEquivalence D).CommShift ℤ :=
  (yonedaEquivalence D).commShift_of_functor ℤ

/-- The original pretriangulation is actually transported to projective
coherent functors through Yoneda, with its distinguished class retained. -/
@[instance_reducible]
def originalPretriangulated :
    Pretriangulated (HellerClassification.Projectives (C := CoherentFunctors.Mod D)) :=
  EquivalenceTransport.pretriangulated D (yonedaEquivalence D)

/-- The inverse Yoneda equivalence is triangulated by the actual pulled-back
class of distinguished triangles. -/
theorem originalInverseTriangulated :
    letI := originalPretriangulated D
    (yonedaEquivalence D).inverse.IsTriangulated := by
  let _ := originalPretriangulated D
  exact ⟨fun _ hT => hT⟩

/-- The actual Yoneda equivalence preserves and reflects distinguished
triangles, including both directions. -/
theorem originalYonedaTriangulated :
    letI := originalPretriangulated D
    (yonedaEquivalence D).IsTriangulated := by
  let _ := originalPretriangulated D
  exact Equivalence.IsTriangulated.mk'' (yonedaEquivalence D) (originalInverseTriangulated D)

/-- Actual octahedra transport across the fully faithful inverse Yoneda
functor. Thus a triangulated original structure stays triangulated. -/
theorem originalIsTriangulated [IsTriangulated D] :
    letI := originalPretriangulated D
    IsTriangulated (HellerClassification.Projectives (C := CoherentFunctors.Mod D)) := by
  let _ := originalPretriangulated D
  let _ := originalInverseTriangulated D
  exact IsTriangulated.of_fully_faithful_triangulated_functor (yonedaEquivalence D).inverse

end OriginalStructure

end PretriangulatedV2.YonedaHellerTransport
