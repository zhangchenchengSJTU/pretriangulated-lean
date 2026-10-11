import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Square-zero perturbations of identity maps

The elementary algebra in Section 6 of Chen--Ivanov--Liu--Lu--Sosnilo--Zhang,
*Pretriangulated categories failing (TR4)*, arXiv:2608.09777v2.

This file deliberately concerns only a given square-zero natural
endomorphism.  It does not construct the global natural transformation used
for the Gemstone category in the paper.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category

namespace PretriangulatedV2

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An endomorphism whose square is zero gives a unit by adding it to the
identity. -/
def endomorphismIdPlusOfSquareZero {X : C} (alpha : X ⟶ X)
    (hsq : alpha ≫ alpha = 0) : X ≅ X :=
  Iso.mk (𝟙 X + alpha) (𝟙 X - alpha) (by
    simp [sub_eq_add_neg, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.comp_neg, hsq]) (by
    simp [sub_eq_add_neg, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.neg_comp, hsq])

/-- The identity plus a square-zero natural endomorphism is a natural
isomorphism.  Its inverse is the identity minus that endomorphism. -/
def idPlusSquareZero (eta : 𝟭 C ⟶ 𝟭 C)
    (hsq : ∀ X : C, eta.app X ≫ eta.app X = 0) : 𝟭 C ≅ 𝟭 C :=
  NatIso.ofComponents (fun X => endomorphismIdPlusOfSquareZero (eta.app X) (hsq X)) (by
    intro X Y f
    change f ≫ (𝟙 ((𝟭 C).obj Y) + eta.app Y) =
      (𝟙 ((𝟭 C).obj X) + eta.app X) ≫ f
    simp only [Preadditive.comp_add, Preadditive.add_comp]
    rw [show f ≫ eta.app Y = eta.app X ≫ f by simpa using eta.naturality f]
    simp only [Functor.id_obj, Category.comp_id, Category.id_comp])

@[simp]
lemma idPlusSquareZero_hom_app (eta : 𝟭 C ⟶ 𝟭 C)
    (hsq : ∀ X : C, eta.app X ≫ eta.app X = 0) (X : C) :
    (idPlusSquareZero eta hsq).hom.app X = 𝟙 ((𝟭 C).obj X) + eta.app X := rfl

@[simp]
lemma idPlusSquareZero_inv_app (eta : 𝟭 C ⟶ 𝟭 C)
    (hsq : ∀ X : C, eta.app X ≫ eta.app X = 0) (X : C) :
    (idPlusSquareZero eta hsq).inv.app X = 𝟙 ((𝟭 C).obj X) - eta.app X := rfl

/-- An additive endofunctor commuting with `eta` also commutes with the
square-zero perturbation of the identity. -/
lemma idPlusSquareZero_commutes (F : C ⥤ C) [F.Additive]
    (eta : 𝟭 C ⟶ 𝟭 C) (hsq : ∀ X : C, eta.app X ≫ eta.app X = 0)
    (hcomm : ∀ X : C, F.map (eta.app X) = eta.app (F.obj X)) (X : C) :
    F.map ((idPlusSquareZero eta hsq).hom.app X) =
      (idPlusSquareZero eta hsq).hom.app (F.obj X) := by
  simp only [idPlusSquareZero_hom_app, F.map_add, F.map_id]
  rw [hcomm X]
  simp only [Functor.id_obj]

section Linear

variable {k : Type w} [Field k] [Linear k C]

/-- Scaling an endomorphism before composing it with itself scales its square
by the product of the two scalars. -/
lemma smul_comp_smul {X : C} (a b : k) (alpha : X ⟶ X) :
    (a • alpha) ≫ (b • alpha) = (a * b) • (alpha ≫ alpha) := by
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul]

/-- Every scalar multiple of a square-zero endomorphism is square-zero. -/
lemma smul_square_eq_zero {X : C} (a : k) (alpha : X ⟶ X)
    (hsq : alpha ≫ alpha = 0) : (a • alpha) ≫ (a • alpha) = 0 := by
  rw [smul_comp_smul, hsq, smul_zero]

/-- Over a field, multiplication by a nonzero scalar on a hom space is
injective. -/
lemma smul_injective_of_ne_zero {X Y : C} {a : k} (ha : a ≠ 0) :
    Function.Injective fun f : X ⟶ Y => a • f := by
  intro f g h
  simpa only [inv_smul_smul₀ ha] using congrArg (fun q : X ⟶ Y => a⁻¹ • q) h

/-- A nonzero scalar multiple of a nonzero endomorphism remains nonzero. -/
lemma smul_ne_zero_of_ne_zero {X : C} {a : k} (ha : a ≠ 0)
    {alpha : X ⟶ X} (halpha : alpha ≠ 0) : a • alpha ≠ 0 := by
  intro h
  apply halpha
  exact smul_injective_of_ne_zero ha (by simpa using h)

end Linear

end PretriangulatedV2
