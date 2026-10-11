import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
The finite direct-sum extension argument of Chen--Ye, Lemma 2.4.
Here we specialize to natural endomorphisms of the identity.  The generating
objects and the existence of finite decompositions remain explicit inputs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- A finite decomposition into generating objects, retaining its actual
isomorphisms.  Zero objects are the empty direct sum. -/
inductive BinaryDecomposition (P : C → Prop) : C → Type (max u v)
  | zero (X : C) (hX : IsZero X) : BinaryDecomposition P X
  | atom (X : C) (hX : P X) : BinaryDecomposition P X
  | iso {X Y : C} (e : X ≅ Y) (d : BinaryDecomposition P Y) : BinaryDecomposition P X
  | sum {X Y : C} (dX : BinaryDecomposition P X) (dY : BinaryDecomposition P Y) :
      BinaryDecomposition P (X ⊞ Y)

namespace BinaryDecomposition

variable {P : C → Prop} (a : ∀ X : C, P X → (X ⟶ X))

/-- Direct-sum and isomorphism transport of the given generator components. -/
def endomorphism {X : C} : BinaryDecomposition P X → (X ⟶ X)
  | .zero _ _ => 0
  | .atom X hX => a X hX
  | .iso e d => e.hom ≫ endomorphism d ≫ e.inv
  | .sum dX dY => biprod.map (endomorphism dX) (endomorphism dY)

/-- The matrix-component argument in Chen--Ye Lemma 2.4. -/
theorem natural
    (ha : ∀ (X Y : C) (hX : P X) (hY : P Y) (f : X ⟶ Y),
      f ≫ a Y hY = a X hX ≫ f) :
    ∀ {X Y : C} (dX : BinaryDecomposition P X) (dY : BinaryDecomposition P Y)
      (f : X ⟶ Y), f ≫ dY.endomorphism a = dX.endomorphism a ≫ f := by
  intro X Y dX
  induction dX generalizing Y with
  | zero X hX =>
      intro dY f
      exact hX.eq_of_src _ _
  | iso e d ih =>
      intro dY f
      apply (cancel_epi e.inv).mp
      simpa only [endomorphism, Category.assoc, Iso.inv_hom_id_assoc] using
        ih dY (e.inv ≫ f)
  | sum dX dZ ihX ihZ =>
      intro dY f
      apply biprod.hom_ext'
      · simpa only [endomorphism, Category.assoc, biprod.inl_map_assoc] using
          ihX dY (biprod.inl ≫ f)
      · simpa only [endomorphism, Category.assoc, biprod.inr_map_assoc] using
          ihZ dY (biprod.inr ≫ f)
  | atom X hX =>
      intro dY f
      induction dY with
      | zero Y hY => exact hY.eq_of_tgt _ _
      | atom Y hY => exact ha X Y hX hY f
      | iso e d ih =>
          apply (cancel_mono e.hom).mp
          simpa only [endomorphism, Category.assoc, Iso.inv_hom_id,
            Category.comp_id] using ih (f ≫ e.hom)
      | sum dY dZ ihY ihZ =>
          apply biprod.hom_ext
          · simpa only [endomorphism, Category.assoc, biprod.map_fst] using
              ihY (f ≫ biprod.fst)
          · simpa only [endomorphism, Category.assoc, biprod.map_snd] using
              ihZ (f ≫ biprod.snd)

end BinaryDecomposition

namespace BinaryDecomposition

variable {P : C → Prop} (a : ∀ X : C, P X → (X ⟶ X))

theorem square_eq_zero
    (ha : ∀ (X : C) (hX : P X), a X hX ≫ a X hX = 0)
    {X : C} (d : BinaryDecomposition P X) :
    d.endomorphism a ≫ d.endomorphism a = 0 := by
  induction d with
  | zero => simp [endomorphism]
  | atom X hX => exact ha X hX
  | iso e d ih =>
      simpa only [endomorphism, Category.assoc, Iso.inv_hom_id_assoc,
        comp_zero, zero_comp] using congrArg (fun f => e.hom ≫ f ≫ e.inv) ih
  | sum dX dY ihX ihY =>
      simp only [endomorphism]
      ext <;> simp [Category.assoc, ihX, ihY]

/-- A natural transformation between additive functors is determined by its
components on a finite direct-sum generating family. -/
theorem natTrans_eq {D : Type*} [Category D] [Preadditive D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (s t : F ⟶ G)
    (hst : ∀ (X : C), P X → s.app X = t.app X)
    {X : C} (d : BinaryDecomposition P X) : s.app X = t.app X := by
  induction d with
  | zero X hX =>
      have hid : (𝟙 X : X ⟶ X) = 0 := hX.eq_of_src _ _
      have hidF : (𝟙 (F.obj X) : F.obj X ⟶ F.obj X) = 0 := by
        simpa only [F.map_id, F.map_zero] using congrArg F.map hid
      calc
        s.app X = 0 := by simpa using congrArg (fun f => f ≫ s.app X) hidF
        _ = t.app X := by simpa using (congrArg (fun f => f ≫ t.app X) hidF).symm
  | atom X hX => exact hst X hX
  | iso e d ih =>
      apply (cancel_mono (G.map e.hom)).mp
      rw [← s.naturality, ← t.naturality, ih]
  | @sum X Y dX dY ihX ihY =>
      have htotal : (F.map (biprod.fst : X ⊞ Y ⟶ X) ≫ F.map biprod.inl) +
          (F.map (biprod.snd : X ⊞ Y ⟶ Y) ≫ F.map biprod.inr) =
          𝟙 (F.obj (X ⊞ Y)) := by
        rw [← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
      have hinl : F.map (biprod.inl : X ⟶ X ⊞ Y) ≫ s.app (X ⊞ Y) =
          F.map biprod.inl ≫ t.app (X ⊞ Y) := by
        rw [s.naturality, t.naturality, ihX]
      have hinr : F.map (biprod.inr : Y ⟶ X ⊞ Y) ≫ s.app (X ⊞ Y) =
          F.map biprod.inr ≫ t.app (X ⊞ Y) := by
        rw [s.naturality, t.naturality, ihY]
      calc
        s.app (X ⊞ Y) =
            ((F.map biprod.fst ≫ F.map biprod.inl) +
              (F.map biprod.snd ≫ F.map biprod.inr)) ≫ s.app (X ⊞ Y) := by
          rw [htotal, Category.id_comp]
        _ = ((F.map biprod.fst ≫ F.map biprod.inl) +
              (F.map biprod.snd ≫ F.map biprod.inr)) ≫ t.app (X ⊞ Y) := by
          simp only [Preadditive.add_comp, Category.assoc, hinl, hinr]
        _ = t.app (X ⊞ Y) := by rw [htotal, Category.id_comp]

end BinaryDecomposition

/-- The actual global extension; naturality is proved by finite sum induction. -/
def extendNaturalEndomorphism {P : C → Prop}
    (hgen : ∀ X : C, Nonempty (BinaryDecomposition P X))
    (a : ∀ X : C, P X → (X ⟶ X))
    (ha : ∀ (X Y : C) (hX : P X) (hY : P Y) (f : X ⟶ Y),
      f ≫ a Y hY = a X hX ≫ f) : 𝟭 C ⟶ 𝟭 C where
  app X := (Classical.choice (hgen X)).endomorphism a
  naturality {_ _} f := BinaryDecomposition.natural a ha _ _ f

theorem extendNaturalEndomorphism_app {P : C → Prop}
    (hgen : ∀ X : C, Nonempty (BinaryDecomposition P X))
    (a : ∀ X : C, P X → (X ⟶ X))
    (ha : ∀ (X Y : C) (hX : P X) (hY : P Y) (f : X ⟶ Y),
      f ≫ a Y hY = a X hX ≫ f) (X : C) (hX : P X) :
    (extendNaturalEndomorphism hgen a ha).app X = a X hX := by
  simpa only [extendNaturalEndomorphism, BinaryDecomposition.endomorphism,
    Category.id_comp, Category.comp_id] using
    (BinaryDecomposition.natural a ha (Classical.choice (hgen X))
      (.atom X hX) (𝟙 X)).symm

theorem extendNaturalEndomorphism_square_eq_zero {P : C → Prop}
    (hgen : ∀ X : C, Nonempty (BinaryDecomposition P X))
    (a : ∀ X : C, P X → (X ⟶ X))
    (ha : ∀ (X Y : C) (hX : P X) (hY : P Y) (f : X ⟶ Y),
      f ≫ a Y hY = a X hX ≫ f)
    (hsq : ∀ (X : C) (hX : P X), a X hX ≫ a X hX = 0) (X : C) :
    (extendNaturalEndomorphism hgen a ha).app X ≫
      (extendNaturalEndomorphism hgen a ha).app X = 0 :=
  BinaryDecomposition.square_eq_zero a hsq (Classical.choice (hgen X))

end PretriangulatedV2
