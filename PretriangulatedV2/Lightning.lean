import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Lightning flashes

This file formalizes Definition 2.2 of
Chen--Ivanov--Liu--Lu--Sosnilo--Zhang, *Pretriangulated categories failing
(TR4)*, arXiv:2608.09777v2.  The facts below use only the pretriangulated
axioms (TR1--TR3); in particular, none assumes the octahedral axiom.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace PretriangulatedV2

universe v u

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

/-- A lightning flash from `T` to `T'` is a map through the third and second
morphisms of the two triangles, as in Definition 2.2. -/
def IsLightningFlash (T T' : Triangle C) (l : T.obj₃ ⟶ T'.obj₃) : Prop :=
  ∃ phi : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₂, l = T.mor₃ ≫ phi ≫ T'.mor₂

/-- Conjugating a lightning flash by an isomorphism of triangles again gives a
lightning flash. -/
lemma IsLightningFlash.conjugate {T T' : Triangle C} (e : T ≅ T')
    {l : T.obj₃ ⟶ T.obj₃} (hl : IsLightningFlash T T l) :
    IsLightningFlash T' T' (e.inv.hom₃ ≫ l ≫ e.hom.hom₃) := by
  obtain ⟨phi, hl⟩ := hl
  refine ⟨e.inv.hom₁⟦(1 : ℤ)⟧' ≫ phi ≫ e.hom.hom₂, ?_⟩
  have hinv : e.inv.hom₃ ≫ T.mor₃ = T'.mor₃ ≫ e.inv.hom₁⟦(1 : ℤ)⟧' := by
    rw [← cancel_mono (e.hom.hom₁⟦(1 : ℤ)⟧')]
    simp
  calc
    e.inv.hom₃ ≫ l ≫ e.hom.hom₃ =
        e.inv.hom₃ ≫ (T.mor₃ ≫ phi ≫ T.mor₂) ≫ e.hom.hom₃ := by rw [hl]
    _ = (e.inv.hom₃ ≫ T.mor₃) ≫ phi ≫ (T.mor₂ ≫ e.hom.hom₃) := by
      simp only [Category.assoc]
    _ = (T'.mor₃ ≫ e.inv.hom₁⟦(1 : ℤ)⟧') ≫ phi ≫
        (e.hom.hom₂ ≫ T'.mor₂) := by rw [hinv, e.hom.comm₂]
    _ = T'.mor₃ ≫ (e.inv.hom₁⟦(1 : ℤ)⟧' ≫ phi ≫ e.hom.hom₂) ≫ T'.mor₂ := by
      simp only [Category.assoc]

variable [Preadditive C]

lemma isLightningFlash_zero (T T' : Triangle C) :
    IsLightningFlash T T' (0 : T.obj₃ ⟶ T'.obj₃) := by
  refine ⟨0, ?_⟩
  simp

lemma IsLightningFlash.add {T T' : Triangle C} {l l' : T.obj₃ ⟶ T'.obj₃}
    (hl : IsLightningFlash T T' l) (hl' : IsLightningFlash T T' l') :
    IsLightningFlash T T' (l + l') := by
  obtain ⟨phi, rfl⟩ := hl
  obtain ⟨psi, rfl⟩ := hl'
  refine ⟨phi + psi, ?_⟩
  simp only [Preadditive.comp_add, Preadditive.add_comp]

lemma IsLightningFlash.neg {T T' : Triangle C} {l : T.obj₃ ⟶ T'.obj₃}
    (hl : IsLightningFlash T T' l) : IsLightningFlash T T' (-l) := by
  obtain ⟨phi, rfl⟩ := hl
  refine ⟨-phi, ?_⟩
  simp

lemma IsLightningFlash.sub {T T' : Triangle C} {l l' : T.obj₃ ⟶ T'.obj₃}
    (hl : IsLightningFlash T T' l) (hl' : IsLightningFlash T T' l') :
    IsLightningFlash T T' (l - l') := by
  simpa only [sub_eq_add_neg] using hl.add hl'.neg

/-- The lightning flashes from `T` to `T'` form an additive subgroup of the
corresponding hom group. -/
def lightningFlashes (T T' : Triangle C) : AddSubgroup (T.obj₃ ⟶ T'.obj₃) where
  carrier := { l | IsLightningFlash T T' l }
  zero_mem' := isLightningFlash_zero T T'
  add_mem' := IsLightningFlash.add
  neg_mem' := IsLightningFlash.neg

variable [HasZeroObject C] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
  [CategoryTheory.Pretriangulated C]

/-- A lightning flash vanishes after precomposition with the second map of
its distinguished source triangle. -/
lemma IsLightningFlash.precomp_mor₂_eq_zero {T T' : Triangle C}
    (hT : T ∈ distTriang C) {l : T.obj₃ ⟶ T'.obj₃}
    (hl : IsLightningFlash T T' l) : T.mor₂ ≫ l = 0 := by
  obtain ⟨phi, rfl⟩ := hl
  rw [← Category.assoc, ← Category.assoc, comp_distTriang_mor_zero₂₃ T hT]
  simp

/-- A lightning flash vanishes after postcomposition with the third map of
its distinguished target triangle. -/
lemma IsLightningFlash.postcomp_mor₃_eq_zero {T T' : Triangle C}
    (hT' : T' ∈ distTriang C) {l : T.obj₃ ⟶ T'.obj₃}
    (hl : IsLightningFlash T T' l) : l ≫ T'.mor₃ = 0 := by
  obtain ⟨phi, rfl⟩ := hl
  simp only [Category.assoc, comp_distTriang_mor_zero₂₃ T' hT', comp_zero]

/-- Every lightning flash on a distinguished triangle has square zero. -/
lemma IsLightningFlash.square_eq_zero {T : Triangle C} (hT : T ∈ distTriang C)
    {l : T.obj₃ ⟶ T.obj₃} (hl : IsLightningFlash T T l) : l ≫ l = 0 := by
  obtain ⟨phi, hphi⟩ := hl
  calc
    l ≫ l = l ≫ (T.mor₃ ≫ phi ≫ T.mor₂) := by rw [hphi]
    _ = (l ≫ T.mor₃) ≫ phi ≫ T.mor₂ := by simp only [Category.assoc]
    _ = 0 := by
      rw [IsLightningFlash.postcomp_mor₃_eq_zero hT ⟨phi, hphi⟩]
      simp

end PretriangulatedV2
