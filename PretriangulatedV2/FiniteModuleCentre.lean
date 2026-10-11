import PretriangulatedV2.FiniteModuleCategory
import PretriangulatedV2.StableCategory

/-! Actual scalar endomorphisms on finite modules over a commutative ring,
and their natural descent to the genuine projective stable quotient. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.FiniteModuleCategory

universe u

variable {A : Type u} [CommRing A]

/-- Multiplication by an actual ambient ring element is A-linear. -/
def scalarEnd (a : A) (X : FGModuleCat.{u} A) : End X :=
  FGModuleCat.ofHom (a • (LinearMap.id : X →ₗ[A] X))

@[simp]
theorem scalarEnd_apply (a : A) (X : FGModuleCat.{u} A) (x : X) :
    (scalarEnd a X).hom.hom x = a • x := rfl

/-- Scalar multiplication commutes with every genuine module morphism. -/
theorem scalarEnd_naturality (a : A) {X Y : FGModuleCat.{u} A} (f : X ⟶ Y) :
    scalarEnd a X ≫ f = f ≫ scalarEnd a Y := by
  ext x
  exact f.hom.hom.map_smul a x

variable [IsNoetherianRing A]

abbrev Stable := StableCategory.projectiveStableCategory (FGModuleCat.{u} A)
abbrev Q := StableCategory.projectiveStableQuotient (C := FGModuleCat.{u} A)

/-- The actual central natural transformation on the projective quotient. -/
def stableScalar (a : A) : 𝟭 (Stable (A := A)) ⟶ 𝟭 (Stable (A := A)) where
  app X := Q.map (scalarEnd a X.as)
  naturality := by
    intro X Y f
    obtain ⟨g, hg⟩ := Q.map_surjective f
    rw [← hg]
    change Q.map g ≫ Q.map (scalarEnd a Y.as) = Q.map (scalarEnd a X.as) ≫ Q.map g
    rw [← Q.map_comp, ← Q.map_comp, scalarEnd_naturality]

/-- Its component at a direct sum is an actual central endomorphism. -/
def stableScalarEnd (a : A) (X : Stable (A := A)) : End X := (stableScalar a).app X

theorem stableScalar_central (a : A) (X : Stable (A := A)) (z : End X) :
    stableScalarEnd a X * z = z * stableScalarEnd a X := by
  unfold stableScalarEnd
  simpa only [End.mul_def, Functor.id_map] using (stableScalar a).naturality z

/-- Restriction to a direct summand is exactly its scalar component. -/
theorem stableScalar_restrict (a : A) (X Y : Stable (A := A)) :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (stableScalar a).app (X ⊞ Y) ≫ biprod.fst =
      (stableScalar a).app X := by
  have h := (stableScalar a).naturality (biprod.inl : X ⟶ X ⊞ Y)
  dsimp only [Functor.id_map] at h
  rw [← Category.assoc, h]
  simp

end PretriangulatedV2.FiniteModuleCategory
