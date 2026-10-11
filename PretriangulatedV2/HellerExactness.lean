import PretriangulatedV2.InjectiveComparison

/-!
The genuine injective-comparison definition of Heller-exact rows from Section 3.
The stable comparison identity is a theorem, obtained from the ambient diagram;
it is not inserted as a field of a cochain-map structure.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open PretriangulatedV2.StableCategory.InjectiveComparison

namespace PretriangulatedV2.StableCategory.HellerExactness

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C] (S : C ≌ C) [S.functor.Additive]

abbrev Parameter := FrobeniusCommutation.StableHellerParameter S

/-- Section 3: a three-step exact injective row ending at `S M` is
δ-exact when an actual comparison diagram represents the Heller parameter.
The four ambient squares and all three short exact rows are retained. -/
def DeltaExact (p : Parameter S) {M : C}
    (E : Extension3 M (S.functor.obj M)) : Prop :=
  ∃ K : E.Comparison, Q.map K.c = p.delta.hom.app (Q.obj M)

/-- The ambient definition is equivalent to the canonical stable comparison,
by the proved independence and existence of actual comparison diagrams. -/
theorem deltaExact_iff_stableComparison (p : Parameter S) {M : C}
    (E : Extension3 M (S.functor.obj M)) :
    DeltaExact S p E ↔ E.stableComparison.hom = p.delta.hom.app (Q.obj M) := by
  constructor
  · rintro ⟨K, hK⟩
    rw [← K.stable_endpoint, hK]
  · intro hE
    exact ⟨E.canonicalComparison, E.canonicalComparison_stable_endpoint.trans hE⟩

/-- δ-exactness of the prescribed projective triangle, written in ambient
objects. The three isomorphisms transport an actual exact injective row to
the triangle's vertices and retain the condition `S(j) ∘ h̄ = h`.
This permits direct use with the underlying objects of mathlib triangles. -/
def DeltaExactTruncation (p : Parameter S) {P₀ P₁ P₂ : C}
    (f : P₀ ⟶ P₁) (g : P₁ ⟶ P₂) (h : P₂ ⟶ S.functor.obj P₀) : Prop :=
  ∃ (M : C) (E : Extension3 M (S.functor.obj M))
    (e₀ : E.I₀ ≅ P₀) (e₁ : E.I₁ ≅ P₁) (e₂ : E.I₂ ≅ P₂),
    E.d₀ ≫ e₁.hom = e₀.hom ≫ f ∧
    E.d₁ ≫ e₂.hom = e₁.hom ≫ g ∧
    E.p₂ ≫ S.functor.map (E.i₀ ≫ e₀.hom) = e₂.hom ≫ h ∧
    DeltaExact S p E

/-- A δ-exact row has the actual boundary triangle of its spliced extension. -/
theorem deltaExactTruncation_of_extension (p : Parameter S) {M : C}
    (E : Extension3 M (S.functor.obj M)) (hE : DeltaExact S p E) :
    DeltaExactTruncation S p E.d₀ E.d₁ (E.p₂ ≫ S.functor.map E.i₀) := by
  refine ⟨M, E, Iso.refl _, Iso.refl _, Iso.refl _, ?_, ?_, ?_, hE⟩
  · simp
  · simp
  · simp

/-- The boundary comparison equation for two genuinely δ-exact rows is
derived from the actual three-step injective comparison theorem. -/
theorem comparison_of_deltaExact (p q : Parameter S) {M N : C}
    {E : Extension3 M (S.functor.obj M)} {E' : Extension3 N (S.functor.obj N)}
    (hE : DeltaExact S p E) (hE' : DeltaExact S q E') (φ : E.Hom E') :
    p.delta.hom.app (Q.obj M) ≫ (cube F).map (Q.map φ.f₀) =
      Q.map φ.f₃ ≫ q.delta.hom.app (Q.obj N) := by
  rw [← (deltaExact_iff_stableComparison S p E).mp hE,
    ← (deltaExact_iff_stableComparison S q E').mp hE']
  exact φ.stableComparison_naturality.symm

/-- The finite injective-extension form of Lemma 4.1.  Its comparison equation
is proved from the ambient diagrams, then the faithful cosyzygy cube cancels.
The endpoint condition is the actual right boundary square, not its stable
comparison consequence. -/
theorem lemma_4_1_of_extension_map (p : Parameter S)
    (u : TriangleCenterUnit F) {M N : C}
    {E : Extension3 M (S.functor.obj M)} {E' : Extension3 N (S.functor.obj N)}
    (hE : DeltaExact S p E) (hE' : DeltaExact S (p.twist u) E')
    (φ : E.Hom E') (f : M ⟶ N) (hφ : φ.f₃ = S.functor.map f) :
    Q.map φ.f₀ = u.iso.hom.app (Q.obj M) ≫ Q.map f := by
  apply p.comparison_eq_unit_comp u
  change p.delta.hom.app (Q.obj M) ≫ (cube F).map (Q.map φ.f₀) =
    Q.map (S.functor.map f) ≫ (p.twist u).delta.hom.app (Q.obj N)
  rw [← hφ]
  exact comparison_of_deltaExact S p (p.twist u) hE hE' φ

end PretriangulatedV2.StableCategory.HellerExactness
