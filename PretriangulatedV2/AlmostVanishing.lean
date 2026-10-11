import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.EpiMono
import PretriangulatedV2.HomFinite

/-!
# Almost-vanishing morphisms

The elementary consequences of the almost-vanishing definition in Section 5 and Lemma 5.2 of
`Pretriangulated categories failing (TR4)`.

No octahedral axiom is used here: the two factorisation statements use only
the exactness of the Hom-sequences of a distinguished triangle.
-/

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

universe v u

namespace PretriangulatedV2

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A nonzero morphism is almost vanishing if postcomposition with every
non-section, and precomposition with every non-retraction, is zero. -/
structure IsAlmostVanishing {Y Z : C} (u : Y ⟶ Z) : Prop where
  nonzero : u ≠ 0
  postcomp_eq_zero {W : C} (s : Z ⟶ W) : ¬ IsSplitMono s → u ≫ s = 0
  precomp_eq_zero {W : C} (t : W ⟶ Y) : ¬ IsSplitEpi t → t ≫ u = 0

namespace IsAlmostVanishing

variable {Y Z : C} {u : Y ⟶ Z}

section Factorisation

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- Lemma 5.2, first factorisation: an almost-vanishing morphism factors
through every nonzero morphism into its target. -/
theorem factors_through_of_nonzero_to (hu : IsAlmostVanishing u) {X : C} (g : X ⟶ Z)
    (hg : g ≠ 0) : ∃ p : Y ⟶ X, u = p ≫ g := by
  obtain ⟨W, f, h, hT⟩ := distinguished_cocone_triangle₁ g
  let T : Triangle C := Triangle.mk f g h
  have hT' : T ∈ distTriang C := hT
  have hh : ¬ IsSplitMono T.mor₃ := by
    intro hh
    have : IsSplitMono T.mor₃ := hh
    have : Mono T.mor₃ := inferInstance
    apply hg
    exact T.mor₂_eq_zero_of_mono₃ hT' (inferInstance)
  obtain ⟨p, hp⟩ := T.coyoneda_exact₃ hT' u (hu.postcomp_eq_zero T.mor₃ hh)
  exact ⟨p, hp⟩

/-- Lemma 5.2, second factorisation: an almost-vanishing morphism factors
through every nonzero morphism out of its source. -/
theorem factors_through_of_nonzero_from (hu : IsAlmostVanishing u) {X : C} (g : Y ⟶ X)
    (hg : g ≠ 0) : ∃ p : X ⟶ Z, u = g ≫ p := by
  obtain ⟨W, f, h, hT⟩ := distinguished_cocone_triangle₁ g
  let T : Triangle C := Triangle.mk f g h
  have hT' : T ∈ distTriang C := hT
  have hf : ¬ IsSplitEpi T.mor₁ := by
    intro hf
    have : IsSplitEpi T.mor₁ := hf
    have : Epi T.mor₁ := inferInstance
    apply hg
    exact T.mor₂_eq_zero_of_epi₁ hT' (inferInstance)
  obtain ⟨p, hp⟩ := T.yoneda_exact₂ hT' u (hu.precomp_eq_zero T.mor₁ hf)
  exact ⟨p, hp⟩

end Factorisation

/-- Remark 5.4(3) in the form valid without additional finiteness or localness
assumptions: a non-section almost-vanishing endomorphism is square-zero. -/
theorem endomorphism_sq_eq_zero {X : C} {a : X ⟶ X} (ha : IsAlmostVanishing a)
    (hna : ¬ IsSplitMono a) : a ≫ a = 0 :=
  ha.postcomp_eq_zero a hna

/-- Under the finite-dimensional hypothesis used in Section 5, a non-isomorphic
almost-vanishing endomorphism is square-zero. -/
theorem endomorphism_sq_eq_zero_of_not_isIso {k : Type*} [Field k] [Linear k C]
    {X : C} [FiniteDimensional k (X ⟶ X)] {a : X ⟶ X} (ha : IsAlmostVanishing a)
    (hna : ¬ IsIso a) : a ≫ a = 0 :=
  ha.endomorphism_sq_eq_zero (not_isSplitMono_of_not_isIso (k := k) a hna)

/-- If postcomposition of an almost-vanishing endomorphism by an endomorphism
is nonzero, that endomorphism must be a section. -/
theorem isSplitMono_of_postcomp_ne_zero {X : C} {a ε : X ⟶ X}
    (ha : IsAlmostVanishing a) (h : a ≫ ε ≠ 0) : IsSplitMono ε := by
  by_contra hε
  exact h (ha.postcomp_eq_zero ε hε)

/-- The finite-dimensional strengthening of
`isSplitMono_of_postcomp_ne_zero`: the endomorphism is invertible. -/
theorem isIso_of_postcomp_ne_zero {k : Type*} [Field k] [Linear k C]
    {X : C} [FiniteDimensional k (X ⟶ X)] {a ε : X ⟶ X}
    (ha : IsAlmostVanishing a) (h : a ≫ ε ≠ 0) : IsIso ε := by
  let : IsSplitMono ε := ha.isSplitMono_of_postcomp_ne_zero h
  exact isIso_of_isSplitMono_endo (k := k) ε

section Functoriality

variable {D : Type*} [Category D] [Preadditive D]

/-- An additive, fully faithful, essentially surjective functor preserves
almost-vanishing morphisms. -/
theorem map_of_additive_fully_faithful_essSurj (F : C ⥤ D) [Functor.Additive F]
    [Functor.Full F] [Functor.Faithful F] [Functor.EssSurj F] (hu : IsAlmostVanishing u) :
    IsAlmostVanishing (F.map u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hu.nonzero
    apply F.map_injective
    simpa using h
  · intro W s hs
    let W' := F.objPreimage W
    let e : F.obj W' ≅ W := F.objObjPreimageIso W
    let s' : F.obj Z ⟶ F.obj W' := s ≫ e.inv
    let t : Z ⟶ W' := F.preimage s'
    have ht : ¬ IsSplitMono t := by
      intro ht
      have : IsSplitMono t := ht
      have hs' : IsSplitMono s' := by
        simpa only [t, Functor.map_preimage] using
          (inferInstance : IsSplitMono (F.map t))
      have : IsSplitMono s' := hs'
      apply hs
      simpa only [s', Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        (inferInstance : IsSplitMono (s' ≫ e.hom))
    have hzero := congrArg F.map (hu.postcomp_eq_zero t ht)
    have hzero' : F.map u ≫ s ≫ e.inv = 0 := by
      simpa only [Functor.map_comp, t, Functor.map_preimage, Functor.map_zero, s', Category.assoc]
        using hzero
    rw [← cancel_mono e.inv]
    simpa only [Category.assoc, zero_comp] using hzero'
  · intro W t ht
    let W' := F.objPreimage W
    let e : F.obj W' ≅ W := F.objObjPreimageIso W
    let t' : F.obj W' ⟶ F.obj Y := e.hom ≫ t
    let r : W' ⟶ Y := F.preimage t'
    have hr : ¬ IsSplitEpi r := by
      intro hr
      have : IsSplitEpi r := hr
      have ht' : IsSplitEpi t' := by
        simpa only [r, Functor.map_preimage] using
          (inferInstance : IsSplitEpi (F.map r))
      have : IsSplitEpi t' := ht'
      apply ht
      simpa [t', Category.assoc] using
        (inferInstance : IsSplitEpi (e.inv ≫ t'))
    have hzero := congrArg F.map (hu.precomp_eq_zero r hr)
    have hzero' : e.hom ≫ t ≫ F.map u = 0 := by
      simpa only [Functor.map_comp, r, Functor.map_preimage, Functor.map_zero, t', Category.assoc]
        using hzero
    rw [← cancel_epi e.hom]
    simpa only [Category.assoc, comp_zero] using hzero'

/-- Almost-vanishing endomorphisms are invariant under conjugation by an
isomorphism. -/
theorem endomorphism_conjugate {X X' : C} {a : X ⟶ X} (ha : IsAlmostVanishing a)
    (e : X ≅ X') : IsAlmostVanishing (e.inv ≫ a ≫ e.hom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply ha.nonzero
    calc
      a = e.hom ≫ (e.inv ≫ a ≫ e.hom) ≫ e.inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
          Category.comp_id]
      _ = 0 := by rw [h]; simp
  · intro W s hs
    have hs' : ¬ IsSplitMono (e.hom ≫ s) := by
      intro hs'
      have : IsSplitMono (e.hom ≫ s) := hs'
      apply hs
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        (inferInstance : IsSplitMono (e.inv ≫ (e.hom ≫ s)))
    calc
      (e.inv ≫ a ≫ e.hom) ≫ s = e.inv ≫ (a ≫ (e.hom ≫ s)) := by simp only [Category.assoc]
      _ = 0 := by rw [ha.postcomp_eq_zero _ hs']; simp
  · intro W t ht
    have ht' : ¬ IsSplitEpi (t ≫ e.inv) := by
      intro ht'
      have : IsSplitEpi (t ≫ e.inv) := ht'
      apply ht
      simpa [Category.assoc] using
        (inferInstance : IsSplitEpi ((t ≫ e.inv) ≫ e.hom))
    calc
      t ≫ (e.inv ≫ a ≫ e.hom) = (t ≫ e.inv) ≫ a ≫ e.hom := by simp only [Category.assoc]
      _ = 0 ≫ e.hom := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ e.hom) (ha.precomp_eq_zero (t ≫ e.inv) ht')
      _ = 0 := by simp

end Functoriality

section Shifts

variable [HasShift C ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]

/-- Additive shifts preserve almost-vanishing morphisms. -/
theorem map_shift (n : ℤ) (hu : IsAlmostVanishing u) :
    IsAlmostVanishing (u⟦n⟧') := by
  simpa only using hu.map_of_additive_fully_faithful_essSurj (shiftFunctor C n)

/-- The shift-by-one instance of `map_shift`, used for the connecting map in
the gemstone construction. -/
theorem shift_one (hu : IsAlmostVanishing u) : IsAlmostVanishing (u⟦(1 : ℤ)⟧') :=
  hu.map_shift 1

end Shifts

end IsAlmostVanishing

end PretriangulatedV2
