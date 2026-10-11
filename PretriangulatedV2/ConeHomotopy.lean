import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import PretriangulatedV2.Lightning

/-!
  The elementary biproduct calculation behind Proposition 2.3 of the source
  paper.  A mapping cone in degree `n` is a biproduct `P ⊞ Q`; a homotopy
  component `h : P ⟶ Q` gives the lower triangular change-of-cone map
  `theta h = 1 + fst ≫ h ≫ inr`.

  Besides the degreewise calculation, the file instantiates mathlib's actual
  mapping-cone map for a homotopy, constructs the closed cochain `H' - H`,
  and records its sign-corrected lightning-flash factor in the homotopy
  category.  The remaining equality between this factor and the difference of
  the two induced cone isomorphisms is deliberately not asserted here.
-/

namespace PretriangulatedV2

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {P Q : C} [HasBinaryBiproduct P Q]

/-- The degreewise change-of-cone matrix associated to `h : P ⟶ Q`.

For a mapping cone, take `P = P•.X (n + 1)` and `Q = Q•.X n`. -/
noncomputable def coneTheta (h : P ⟶ Q) : P ⊞ Q ⟶ P ⊞ Q :=
  𝟙 _ + biprod.fst ≫ h ≫ biprod.inr

/-- The change-of-cone matrix is invertible, with the expected negative
off-diagonal entry. -/
noncomputable def coneThetaIso (h : P ⟶ Q) : P ⊞ Q ≅ P ⊞ Q where
  hom := coneTheta h
  inv := coneTheta (-h)
  hom_inv_id := by
    ext <;> simp [coneTheta]
  inv_hom_id := by
    ext <;> simp [coneTheta]

@[simp]
lemma coneThetaIso_hom (h : P ⟶ Q) : (coneThetaIso h).hom = coneTheta h := rfl

@[simp]
lemma coneThetaIso_inv (h : P ⟶ Q) : (coneThetaIso h).inv = coneTheta (-h) := rfl

/-- The difference of two changes of cone is the lightning-flash matrix.

In Proposition 2.3 this is applied degreewise to two homotopies `H` and `H'`.
The right side factors through the first projection and second inclusion of the
mapping-cone biproduct. -/
lemma coneTheta_inverse_comp_sub_id (h h' : P ⟶ Q) :
    (coneThetaIso h).inv ≫ coneTheta h' - 𝟙 _ =
      biprod.fst ≫ (h' - h) ≫ biprod.inr := by
  ext <;> simp [coneTheta, coneThetaIso]
  all_goals abel

/-- Equivalently, the lightning-flash matrix is the difference between the two
degreewise cone changes after identifying the target cone by the inverse of the
first one. -/
lemma coneTheta_lightning_factorization (h h' : P ⟶ Q) :
    (coneThetaIso h).inv ≫ (coneThetaIso h').hom - 𝟙 _ =
      biprod.fst ≫ (h' - h) ≫ biprod.inr := by
  exact coneTheta_inverse_comp_sub_id h h'

namespace ConeHomotopy

open HomologicalComplex CochainComplex.HomComplex

variable {F G : CochainComplex C ℤ} (f g : F ⟶ G)
variable [HasBinaryBiproducts C]

/-- The input expected by mathlib's mapping-cone map for the identity square
between `f` and `g`. -/
noncomputable def identitySquareHomotopy (H : Homotopy f g) :
    Homotopy (f ≫ 𝟙 G) (𝟙 F ≫ g) := by
  simpa using H

/-- mathlib's `mapOfHomotopy` takes a homotopy filling a square.  For the
identity square between `f` and `g`, this is precisely the chain-level
change-of-cone map used in Proposition 2.3. -/
noncomputable def thetaOfHomotopy (H : Homotopy f g) :
    CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone g :=
  CochainComplex.mappingCone.mapOfHomotopy (φ₁ := f) (φ₂ := g)
    (a := 𝟙 F) (b := 𝟙 G) (identitySquareHomotopy f g H)

/-- The induced map commutes with the second map of the standard triangles. -/
@[reassoc]
lemma inr_thetaOfHomotopy (H : Homotopy f g) :
    CochainComplex.mappingCone.inr f ≫ thetaOfHomotopy f g H =
      CochainComplex.mappingCone.inr g := by
  simpa only [thetaOfHomotopy, Functor.map_id, Category.id_comp, Category.comp_id] using
    CochainComplex.mappingCone.triangleMapOfHomotopy_comm₂ (identitySquareHomotopy f g H)

/-- The induced map commutes with the third map of the standard triangles. -/
@[reassoc]
lemma thetaOfHomotopy_triangle_mor₃ (H : Homotopy f g) :
    thetaOfHomotopy f g H ≫ (CochainComplex.mappingCone.triangle g).mor₃ =
      (CochainComplex.mappingCone.triangle f).mor₃ ≫
        (shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map (𝟙 F) := by
  simpa only [thetaOfHomotopy] using
    CochainComplex.mappingCone.triangleMapOfHomotopy_comm₃ (identitySquareHomotopy f g H)

/-- The induced morphism of standard triangles in the homotopy category. -/
noncomputable def thetaTriangleh (H : Homotopy f g) :
    CochainComplex.mappingCone.triangleh f ⟶ CochainComplex.mappingCone.triangleh g :=
  CochainComplex.mappingCone.trianglehMapOfHomotopy (identitySquareHomotopy f g H)

/-- The closed degree `-1` cochain given by the difference of two homotopies
from `f` to `g`. -/
noncomputable def homotopyDifference (H H' : Homotopy f g) :
    Cocycle F G (-1) :=
  Cocycle.mk ((Cochain.equivHomotopy f g H').1 -
    (Cochain.equivHomotopy f g H).1) 0 (by omega) (by
      have hH := (Cochain.equivHomotopy f g H).2
      have hH' := (Cochain.equivHomotopy f g H').2
      have hdelta : δ (-1) 0 (Cochain.equivHomotopy f g H').1 =
          δ (-1) 0 (Cochain.equivHomotopy f g H).1 := by
        apply add_right_cancel (b := Cochain.ofHom g)
        rw [← hH', ← hH]
      rw [sub_eq_add_neg, δ_add, δ_neg, hdelta]
      simp)

/-- The chain map `F⟦1⟧ ⟶ G` represented by `H' - H`. -/
noncomputable def homotopyDifferenceMap (H H' : Homotopy f g) : F⟦(1 : ℤ)⟧ ⟶ G :=
  (Cocycle.equivHomShift' (K := F) (L := G) 1 (-1) (by omega)).symm
    (homotopyDifference f g H H')

/-- The middle factor of the lightning flash.  The inverse shift-commutation
isomorphism changes the source from the shifted homotopy-category object to
the homotopy-category image of the shifted complex.  The minus sign is forced
by mathlib's convention that the third map of `mappingCone.triangle` uses
`-fst`, whereas the source paper writes the positive projection. -/
noncomputable def homotopyDifferenceWitness (H H' : Homotopy f g) :
    (CochainComplex.mappingCone.triangleh f).obj₁⟦(1 : ℤ)⟧ ⟶
      (CochainComplex.mappingCone.triangleh f).obj₂ :=
  ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app F ≫
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (-(homotopyDifferenceMap f g H H'))

/-- The sign-corrected candidate discrepancy on the standard triangle. -/
noncomputable def homotopyDifferenceFlash (H H' : Homotopy f g) :
    (CochainComplex.mappingCone.triangleh f).obj₃ ⟶
      (CochainComplex.mappingCone.triangleh f).obj₃ :=
  (CochainComplex.mappingCone.triangleh f).mor₃ ≫
    homotopyDifferenceWitness f g H H' ≫
    (CochainComplex.mappingCone.triangleh f).mor₂

/-- The sign-corrected factor is a lightning flash on the standard triangle. -/
lemma isLightningFlash_homotopyDifferenceFlash (H H' : Homotopy f g) :
    IsLightningFlash (CochainComplex.mappingCone.triangleh f)
      (CochainComplex.mappingCone.triangleh f) (homotopyDifferenceFlash f g H H') := by
  refine ⟨homotopyDifferenceWitness f g H H', rfl⟩

omit [HasBinaryBiproducts C] in
lemma homotopyDifferenceMap_eq (H H' : Homotopy f g) :
    homotopyDifferenceMap f g H H' =
      Cocycle.homOf ((homotopyDifference f g H H').leftShift 1 0 (by omega)) := by
  simpa [homotopyDifferenceMap] using
    (Cocycle.equivHomShift'_symm_apply (K := F) (L := G) 1 (-1) (by omega)
      (homotopyDifference f g H H'))

end ConeHomotopy

end PretriangulatedV2
