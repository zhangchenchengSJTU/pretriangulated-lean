import PretriangulatedV2.ConeHomotopy

/-! # The mapping-cone lightning flash

This file proves the concrete mapping-cone assertion of Proposition 2.3.
The difference of the two changes of cone factors through the third and
second maps of the actual standard triangle in the homotopy category.
-/

namespace PretriangulatedV2.ConeHomotopy

open CategoryTheory Limits HomologicalComplex CochainComplex.HomComplex
open CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasBinaryBiproducts C]
variable {F G : CochainComplex C ℤ} (f g : F ⟶ G)

omit [HasBinaryBiproducts C] in
lemma identitySquareHomotopy_hom (H : Homotopy f g) (p q : ℤ) :
    (identitySquareHomotopy f g H).hom p q = H.hom p q := by
  have transport (f₁ f₂ g₁ g₂ : F ⟶ G) (hf : f₁ = f₂) (hg : g₁ = g₂)
      (h : Homotopy f₁ g₁) :
      (cast (congrArg₂ (fun a b => Homotopy a b) hf hg) h).hom p q = h.hom p q := by
    cases hf
    cases hg
    rfl
  exact transport f (f ≫ 𝟙 G) g (𝟙 F ≫ g)
    (Category.comp_id f).symm (Category.id_comp g).symm H

@[reassoc]
lemma inl_thetaOfHomotopy_f (H : Homotopy f g) (p q : ℤ)
    (hpq : p + (-1) = q) :
    (CochainComplex.mappingCone.inl f).v p q hpq ≫
      (thetaOfHomotopy f g H).f q =
    (CochainComplex.mappingCone.inl g).v p q hpq +
      H.hom p q ≫ (CochainComplex.mappingCone.inr g).f q := by
  simp [thetaOfHomotopy, CochainComplex.mappingCone.mapOfHomotopy,
    Cochain.comp_zero_cochain_v,
    Cochain.equivHomotopy, Cochain.ofHomotopy, identitySquareHomotopy_hom]

@[reassoc (attr := simp)]
lemma inr_thetaOfHomotopy_f (H : Homotopy f g) (n : ℤ) :
    (CochainComplex.mappingCone.inr f).f n ≫ (thetaOfHomotopy f g H).f n =
      (CochainComplex.mappingCone.inr g).f n := by
  simpa using congrArg (fun k => k.f n) (inr_thetaOfHomotopy f g H)

omit [HasBinaryBiproducts C] in
lemma homotopyDifferenceMap_f (H H' : Homotopy f g) (n : ℤ) :
    (homotopyDifferenceMap f g H H').f n =
      (F.shiftFunctorObjXIso 1 n (n + 1) rfl).hom ≫
        (H'.hom (n + 1) n - H.hom (n + 1) n) := by
  rw [homotopyDifferenceMap_eq]
  simp only [Cocycle.homOf_f, Cocycle.leftShift_coe]
  rw [Cochain.leftShift_v _ 1 0 (by omega) n n (by omega) (n + 1) (by omega)]
  simp [
    homotopyDifference, Cochain.equivHomotopy, Cochain.ofHomotopy]
  rfl

lemma thetaOfHomotopy_comp_symm (H : Homotopy f g) :
    thetaOfHomotopy f g H ≫ thetaOfHomotopy g f H.symm = 𝟙 _ := by
  ext n
  apply CochainComplex.mappingCone.ext_from f (n + 1) n rfl
  · simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    rw [← Category.assoc, inl_thetaOfHomotopy_f, Preadditive.add_comp,
      inl_thetaOfHomotopy_f, Category.assoc, inr_thetaOfHomotopy_f,
      Homotopy.symm_hom, Preadditive.neg_comp]
    simp
  · simp

/-- The actual chain isomorphism induced by a homotopy, with inverse induced
by its symmetric homotopy. -/
noncomputable def thetaIso (H : Homotopy f g) :
    CochainComplex.mappingCone f ≅ CochainComplex.mappingCone g where
  hom := thetaOfHomotopy f g H
  inv := thetaOfHomotopy g f H.symm
  hom_inv_id := thetaOfHomotopy_comp_symm f g H
  inv_hom_id := by
    have hsymm : H.symm.symm = H := by
      ext p q
      simp
    simpa only [hsymm] using thetaOfHomotopy_comp_symm g f H.symm

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise matrix calculation expressed as an equality of actual
cochain maps, with the sign of mathlib's standard triangle. -/
lemma thetaOfHomotopy_comp_symm_sub_id (H H' : Homotopy f g) :
    thetaOfHomotopy f g H' ≫ thetaOfHomotopy g f H.symm - 𝟙 _ =
      (CochainComplex.mappingCone.triangle f).mor₃ ≫
        (-homotopyDifferenceMap f g H H') ≫ CochainComplex.mappingCone.inr f := by
  ext n
  apply CochainComplex.mappingCone.ext_from f (n + 1) n rfl
  · simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply,
      HomologicalComplex.id_f, HomologicalComplex.neg_f_apply, Preadditive.comp_sub]
    rw [← Category.assoc, inl_thetaOfHomotopy_f, Preadditive.add_comp,
      inl_thetaOfHomotopy_f, Category.assoc, inr_thetaOfHomotopy_f,
      Homotopy.symm_hom, Preadditive.neg_comp]
    simp only [Category.assoc, CochainComplex.mappingCone.inl_v_triangle_mor₃_f_assoc,
      homotopyDifferenceMap_f, Preadditive.comp_neg, Preadditive.neg_comp,
      neg_neg, Iso.inv_hom_id_assoc, Preadditive.sub_comp, Category.comp_id]
    abel
  · simp

@[simp]
lemma thetaIso_hom (H : Homotopy f g) :
    (thetaIso f g H).hom = thetaOfHomotopy f g H := rfl

@[simp]
lemma thetaIso_inv (H : Homotopy f g) :
    (thetaIso f g H).inv = thetaOfHomotopy g f H.symm := rfl

/-- The change of cone in the homotopy category. -/
noncomputable def thetaIsoh (H : Homotopy f g) :
    (CochainComplex.mappingCone.triangleh f).obj₃ ≅
      (CochainComplex.mappingCone.triangleh g).obj₃ :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso (thetaIso f g H)

set_option backward.isDefEq.respectTransparency false in
lemma homotopyDifferenceFlash_eq_map (H H' : Homotopy f g) :
    homotopyDifferenceFlash f g H H' =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((CochainComplex.mappingCone.triangle f).mor₃ ≫
          (-homotopyDifferenceMap f g H H') ≫ CochainComplex.mappingCone.inr f) := by
  change
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCone.triangle f).mor₃ ≫
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app F) ≫
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app F ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (-homotopyDifferenceMap f g H H')) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCone.inr f) = _
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The discrepancy of the two induced cone isomorphisms equals the concrete
lightning flash, as an equality of morphisms in the actual homotopy category. -/
lemma thetaIsoh_comp_inv_sub_id (H H' : Homotopy f g) :
    (thetaIsoh f g H').hom ≫ (thetaIsoh f g H).inv - 𝟙 _ =
      homotopyDifferenceFlash f g H H' := by
  dsimp only [CochainComplex.mappingCone.triangleh, Functor.mapTriangle,
    Triangle.mk, CochainComplex.mappingCone.triangle]
  rw [homotopyDifferenceFlash_eq_map]
  have h := congrArg (fun k : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone f =>
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map k)
      (thetaOfHomotopy_comp_symm_sub_id f g H H')
  simp only [Functor.map_sub, Functor.map_comp] at h
  erw [CategoryTheory.Functor.map_id] at h
  simpa only [Functor.map_comp, thetaIsoh, Functor.mapIso_hom, Functor.mapIso_inv,
    thetaIso_hom, thetaIso_inv] using h

/-- Proposition 2.3: two homotopies between the same maps give cone
isomorphisms whose discrepancy is a lightning flash on the standard triangle. -/
theorem isLightningFlash_thetaIsoh_discrepancy (H H' : Homotopy f g) :
    IsLightningFlash (CochainComplex.mappingCone.triangleh f)
      (CochainComplex.mappingCone.triangleh f)
      ((thetaIsoh f g H').hom ≫ (thetaIsoh f g H).inv - 𝟙 _) := by
  rw [thetaIsoh_comp_inv_sub_id]
  exact isLightningFlash_homotopyDifferenceFlash f g H H'

/-- The same equality using the previously defined morphisms of standard
triangles, rather than the middle-object isomorphisms. -/
lemma thetaTriangleh_comp_symm_sub_id (H H' : Homotopy f g) :
    (thetaTriangleh f g H').hom₃ ≫ (thetaTriangleh g f H.symm).hom₃ - 𝟙 _ =
      homotopyDifferenceFlash f g H H' := by
  exact thetaIsoh_comp_inv_sub_id f g H H'

theorem isLightningFlash_thetaTriangleh_discrepancy (H H' : Homotopy f g) :
    IsLightningFlash (CochainComplex.mappingCone.triangleh f)
      (CochainComplex.mappingCone.triangleh f)
      ((thetaTriangleh f g H').hom₃ ≫ (thetaTriangleh g f H.symm).hom₃ - 𝟙 _) := by
  rw [thetaTriangleh_comp_symm_sub_id]
  exact isLightningFlash_homotopyDifferenceFlash f g H H'

end PretriangulatedV2.ConeHomotopy
