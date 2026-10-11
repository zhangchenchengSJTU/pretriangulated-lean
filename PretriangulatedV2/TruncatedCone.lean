import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Truncated cones of maps of triangles

The triangle `truncatedCone m` is the truncated cone `C(a,b,c)` in Section 2
of arXiv:2608.09777v2.  The construction and the zero-composite calculations
below use only the pretriangulated axioms; `HasGoodFillIns` records the extra
property in Theorem 2.1 without asserting its equivalence to (TR4).
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [hZero : HasZeroObject C]
  [HasBinaryBiproducts C] [HasShift C ℤ]
  [hAdditiveShift : ∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
  [hPreservesShiftBiproduct : PreservesBinaryBiproducts (shiftFunctor C (1 : ℤ))]

variable {T T' : Triangle C}

/-- The first matrix in the truncated cone of a morphism of triangles. -/
def truncatedConeMor₁ (m : T ⟶ T') :
    T.obj₂ ⊞ T'.obj₁ ⟶ T.obj₃ ⊞ T'.obj₂ :=
  biprod.fst ≫ (-T.mor₂) ≫ biprod.inl +
    biprod.fst ≫ m.hom₂ ≫ biprod.inr +
    biprod.snd ≫ T'.mor₁ ≫ biprod.inr

/-- The second matrix in the truncated cone of a morphism of triangles. -/
def truncatedConeMor₂ (m : T ⟶ T') :
    T.obj₃ ⊞ T'.obj₂ ⟶ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃ :=
  biprod.fst ≫ (-T.mor₃) ≫ biprod.inl +
    biprod.fst ≫ m.hom₃ ≫ biprod.inr +
    biprod.snd ≫ T'.mor₂ ≫ biprod.inr

/-- The third matrix in the truncated cone, before identifying
`Σ Y ⊞ Σ X'` with `Σ (Y ⊞ X')`. -/
def truncatedConeMor₃Matrix (m : T ⟶ T') :
    T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃ ⟶
      T.obj₂⟦(1 : ℤ)⟧ ⊞ T'.obj₁⟦(1 : ℤ)⟧ :=
  biprod.fst ≫ (-(T.mor₁⟦(1 : ℤ)⟧')) ≫ biprod.inl +
    biprod.fst ≫ (m.hom₁⟦(1 : ℤ)⟧') ≫ biprod.inr +
    biprod.snd ≫ T'.mor₃ ≫ biprod.inr

/-- The third arrow of the truncated cone.  `mapBiprod` is the canonical
isomorphism `Σ (Y ⊞ X') ≅ ΣY ⊞ ΣX'`, so its inverse supplies the required
codomain `Σ (Y ⊞ X')`. -/
def truncatedConeMor₃ (m : T ⟶ T') :
    T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃ ⟶ (T.obj₂ ⊞ T'.obj₁)⟦(1 : ℤ)⟧ :=
  truncatedConeMor₃Matrix m ≫
    ((shiftFunctor C (1 : ℤ)).mapBiprod T.obj₂ T'.obj₁).inv

omit hZero hAdditiveShift hPreservesShiftBiproduct in
lemma truncatedConeMor₁_eq_lift (m : T ⟶ T') :
    truncatedConeMor₁ m =
      biprod.lift (biprod.fst ≫ (-T.mor₂))
        (biprod.fst ≫ m.hom₂ + biprod.snd ≫ T'.mor₁) := by
  ext <;> simp [truncatedConeMor₁]

/-- The truncated cone `C(a,b,c)` of a morphism of triangles `(a,b,c)`. -/
def truncatedCone (m : T ⟶ T') : Triangle C :=
  Triangle.mk (truncatedConeMor₁ m) (truncatedConeMor₂ m) (truncatedConeMor₃ m)

variable [CategoryTheory.Pretriangulated C]

omit hPreservesShiftBiproduct in
/-- The first two maps of a truncated cone compose to zero when its source and
target triangles are distinguished. -/
lemma truncatedConeMor₁_comp_truncatedConeMor₂ (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    truncatedConeMor₁ m ≫ truncatedConeMor₂ m = 0 := by
  ext <;> simp [truncatedConeMor₁, truncatedConeMor₂,
    comp_distTriang_mor_zero₂₃ T hT, comp_distTriang_mor_zero₁₂ T' hT']

/-- Before the canonical biproduct comparison isomorphism, the second and
third truncated-cone matrices already have zero composite. -/
lemma truncatedConeMor₂_comp_truncatedConeMor₃Matrix (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    truncatedConeMor₂ m ≫ truncatedConeMor₃Matrix m = 0 := by
  ext <;> simp [truncatedConeMor₂, truncatedConeMor₃Matrix,
    comp_distTriang_mor_zero₃₁ T hT, comp_distTriang_mor_zero₂₃ T' hT']

/-- The second and third maps of a truncated cone compose to zero. -/
lemma truncatedConeMor₂_comp_truncatedConeMor₃ (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    truncatedConeMor₂ m ≫ truncatedConeMor₃ m = 0 := by
  rw [truncatedConeMor₃, ← Category.assoc,
    truncatedConeMor₂_comp_truncatedConeMor₃Matrix m hT hT', zero_comp]

/-- The last and shifted first maps of a truncated cone compose to zero. -/
lemma truncatedConeMor₃_comp_shift_truncatedConeMor₁ (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    truncatedConeMor₃ m ≫ (truncatedConeMor₁ m)⟦(1 : ℤ)⟧' = 0 := by
  apply (cancel_mono ((shiftFunctor C (1 : ℤ)).mapBiprod T.obj₃ T'.obj₂).hom).mp
  simp only [zero_comp]
  rw [truncatedConeMor₁_eq_lift, truncatedConeMor₃]
  rw [Category.assoc, biprod.map_lift_mapBiprod]
  simp only [Functor.mapBiprod_inv, biprod.desc_eq]
  ext <;> simp [truncatedConeMor₃Matrix, Functor.map_add, Functor.map_neg,
    ← Functor.map_comp,
    comp_distTriang_mor_zero₁₂ T hT, comp_distTriang_mor_zero₃₁ T' hT']

/-- The three consecutive composites in the truncated cone vanish. -/
lemma truncatedCone_comp_mor₁_mor₂ (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    (truncatedCone m).mor₁ ≫ (truncatedCone m).mor₂ = 0 :=
  truncatedConeMor₁_comp_truncatedConeMor₂ m hT hT'

lemma truncatedCone_comp_mor₂_mor₃ (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    (truncatedCone m).mor₂ ≫ (truncatedCone m).mor₃ = 0 :=
  truncatedConeMor₂_comp_truncatedConeMor₃ m hT hT'

lemma truncatedCone_comp_mor₃_shift_mor₁ (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    (truncatedCone m).mor₃ ≫ (truncatedCone m).mor₁⟦(1 : ℤ)⟧' = 0 :=
  truncatedConeMor₃_comp_shift_truncatedConeMor₁ m hT hT'

/-- The good-fill-in property in Theorem 2.1: a triangle morphism between
distinguished triangles can have its third component replaced so that its
truncated cone is distinguished.  This definition deliberately does not claim
the theorem's equivalence with the octahedral axiom. -/
def HasGoodFillIns (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
    [PreservesBinaryBiproducts (shiftFunctor C (1 : ℤ))]
    [CategoryTheory.Pretriangulated C] : Prop :=
  ∀ {T T' : Triangle C} (_hT : T ∈ distTriang C) (_hT' : T' ∈ distTriang C)
    (m : T ⟶ T'), ∃ m' : T ⟶ T', m'.hom₁ = m.hom₁ ∧ m'.hom₂ = m.hom₂ ∧
      truncatedCone m' ∈ distTriang C

end PretriangulatedV2
