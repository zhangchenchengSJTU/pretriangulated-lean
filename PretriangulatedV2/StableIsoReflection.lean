import PretriangulatedV2.FittingEndomorphisms

/-!
Stable isomorphisms between indecomposable nonprojective objects reflect to
ambient isomorphisms. The proof works with possibly noncommutative End
algebras, using the Fitting alternative in a single-element subalgebra.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]

/-- A stable zero identity exhibits the object as an actual retract of a
projective object. -/
theorem projective_of_stable_identity_eq_zero (X : C)
    (h : 𝟙 ((projectiveStableQuotient (C := C)).obj X) = 0) : Projective X := by
  have hmap : (projectiveStableQuotient (C := C)).map (𝟙 X) = 0 := by
    simpa using h
  obtain ⟨P, hP, i, r, hir⟩ :=
    (functor_map_eq_zero_iff (projectiveObjects : C → Prop) (𝟙 X)).mp hmap
  have : Projective P := hP
  exact (⟨i, r, hir⟩ : Retract X P).projective

variable {k : Type w} [Field k] [Linear k C]

include k in
/-- An endomorphism equal to the identity in the stable quotient of an
indecomposable nonprojective object is invertible in the ambient category. -/
theorem isIso_of_stable_map_eq_identity {X : C}
    [FiniteDimensional k (X ⟶ X)] (hX : Indecomposable X)
    (hnp : ¬ Projective X) (a : X ⟶ X)
    (ha : (projectiveStableQuotient (C := C)).map a = 𝟙 _) : IsIso a := by
  rcases end_nilpotent_or_isUnit (k := k) hX a with hn | hu
  · obtain ⟨N, hN⟩ := hn
    let b : End X := a
    let QE := (projectiveStableQuotient (C := C)).mapEnd X
    have ha' : QE b = 1 := ha
    have hpow : b ^ N = 0 := hN
    have hzero : (𝟙 ((projectiveStableQuotient (C := C)).obj X) : End _) = 0 := by
      have hz : QE (b ^ N) = 0 := by
        rw [hpow]
        exact (projectiveStableQuotient (C := C)).map_zero X X
      rw [map_pow, ha', one_pow] at hz
      exact hz
    exact False.elim (hnp (projective_of_stable_identity_eq_zero X hzero))
  · exact (isUnit_iff_isIso a).mp hu

include k in
/-- The actual quotient reflects isomorphisms between indecomposable
nonprojective objects, without an extra commutativity or localness premise. -/
theorem isIso_of_stable_map_isIso {X Y : C}
    [FiniteDimensional k (X ⟶ X)] [FiniteDimensional k (Y ⟶ Y)]
    (hX : Indecomposable X) (hY : Indecomposable Y)
    (hnpX : ¬ Projective X) (hnpY : ¬ Projective Y) (f : X ⟶ Y)
    [IsIso ((projectiveStableQuotient (C := C)).map f)] : IsIso f := by
  let Q := projectiveStableQuotient (C := C)
  obtain ⟨g, hg⟩ := Q.map_surjective (inv (Q.map f))
  have hfg : Q.map (f ≫ g) = 𝟙 _ := by rw [Q.map_comp, hg]; simp
  have hgf : Q.map (g ≫ f) = 𝟙 _ := by rw [Q.map_comp, hg]; simp
  have : IsIso (f ≫ g) := isIso_of_stable_map_eq_identity (k := k) hX hnpX _ hfg
  have : IsIso (g ≫ f) := isIso_of_stable_map_eq_identity (k := k) hY hnpY _ hgf
  have : Epi f := epi_of_epi g f
  refine { out := ⟨g ≫ inv (f ≫ g), ?_, ?_⟩ }
  · simp [← Category.assoc]
  · apply (cancel_epi f).mp
    simp [← Category.assoc]

include k in
theorem nonempty_iso_of_stable_iso {X Y : C}
    [FiniteDimensional k (X ⟶ X)] [FiniteDimensional k (Y ⟶ Y)]
    (hX : Indecomposable X) (hY : Indecomposable Y)
    (hnpX : ¬ Projective X) (hnpY : ¬ Projective Y)
    (e : (projectiveStableQuotient (C := C)).obj X ≅
      (projectiveStableQuotient (C := C)).obj Y) : Nonempty (X ≅ Y) := by
  let Q := projectiveStableQuotient (C := C)
  let f := Q.preimage e.hom
  have : IsIso (Q.map f) := by
    dsimp [f]
    rw [Q.map_preimage]
    infer_instance
  have : IsIso f := isIso_of_stable_map_isIso (k := k) hX hY hnpX hnpY f
  exact ⟨asIso f⟩

end PretriangulatedV2.StableCategory
