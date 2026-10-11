import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
Split maps between indecomposable objects in an idempotent-complete additive
category are invertible. This supplies a prerequisite for the supported
central natural transformation used in Section 6 of arXiv:2608.09777v2.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive

namespace PretriangulatedV2

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C] [IsIdempotentComplete C]

/-- A split monomorphism has an actual complementary object. -/
theorem exists_biprod_complement_of_isSplitMono {X Y : C} (f : X ⟶ Y)
    [IsSplitMono f] :
    ∃ (Z : C) (e : Y ≅ X ⊞ Z), e.hom ≫ biprod.fst = retraction f := by
  let r := retraction f
  have hfr : f ≫ r = 𝟙 X := IsSplitMono.id f
  let p : Y ⟶ Y := 𝟙 Y - r ≫ f
  have hrf : (r ≫ f) ≫ (r ≫ f) = r ≫ f := by
    rw [Category.assoc, ← Category.assoc f r f, hfr, Category.id_comp]
  have hp : p ≫ p = p := by
    simp only [p, sub_comp, comp_sub, Category.id_comp, Category.comp_id,
      hrf]
    abel
  obtain ⟨Z, i, q, hiq, hqi⟩ := IsIdempotentComplete.idempotents_split Y p hp
  have : IsSplitMono i := IsSplitMono.mk' ⟨q, hiq⟩
  have : IsSplitEpi q := IsSplitEpi.mk' ⟨i, hiq⟩
  have hfq : f ≫ q = 0 := by
    apply (cancel_mono i).mp
    rw [zero_comp, Category.assoc, hqi]
    dsimp only [p]
    rw [comp_sub, Category.comp_id, ← Category.assoc, hfr, Category.id_comp, sub_self]
  have hir : i ≫ r = 0 := by
    apply (cancel_epi q).mp
    rw [comp_zero, ← Category.assoc, hqi]
    dsimp only [p]
    rw [sub_comp, Category.id_comp, Category.assoc, hfr, Category.comp_id, sub_self]
  let e : Y ≅ X ⊞ Z :=
    { hom := biprod.lift r q
      inv := biprod.desc f i
      hom_inv_id := by
        simp only [biprod.lift_desc, hqi, p]
        abel
      inv_hom_id := by
        ext <;> simp [Category.assoc, hfr, hfq, hir, hiq] }
  exact ⟨Z, e, biprod.lift_fst r q⟩

/-- A section with nonzero source and indecomposable target is an isomorphism. -/
theorem isIso_of_isSplitMono_of_indecomposable {X Y : C}
    (hX : ¬ IsZero X) (hY : Indecomposable Y) (f : X ⟶ Y)
    [IsSplitMono f] : IsIso f := by
  obtain ⟨Z, e, he⟩ := exists_biprod_complement_of_isSplitMono f
  have hZ : IsZero Z := (hY.2 X Z e).resolve_left hX
  have : IsIso (biprod.fst : X ⊞ Z ⟶ X) := by
    exact ⟨⟨biprod.inl,
      by
        have hsnd : (biprod.snd : X ⊞ Z ⟶ Z) = 0 := hZ.eq_zero_of_tgt _
        simpa only [hsnd, zero_comp, add_zero] using
          (biprod.total (X := X) (Y := Z)), by simp⟩⟩
  have : IsIso (retraction f) := by
    rw [← he]
    infer_instance
  exact IsIso.of_mono_retraction f

/-- The dual statement for a retraction onto a nonzero object. -/
theorem isIso_of_isSplitEpi_of_indecomposable {X Y : C}
    (hX : Indecomposable X) (hY : ¬ IsZero Y) (f : X ⟶ Y)
    [IsSplitEpi f] : IsIso f := by
  have : IsIso (section_ f) :=
    isIso_of_isSplitMono_of_indecomposable hY hX (section_ f)
  exact IsIso.of_epi_section f

end PretriangulatedV2
