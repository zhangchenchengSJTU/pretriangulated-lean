import PretriangulatedV2.FrobeniusTriangles
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-! Octahedra from genuine ambient cokernel sequences. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory CategoryTheory.Limits
open PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory.FrobeniusTriangles

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- An injective component of a biproduct lift vanishes in the stable quotient. -/
theorem stable_lift_eq {X Y I : C} [Injective I] (f : X ⟶ Y) (i : X ⟶ I) :
    (projectiveStableQuotient (C := C)).map (biprod.lift f i) =
      (projectiveStableQuotient (C := C)).map f ≫
        (projectiveStableQuotient (C := C)).map (biprod.inl : Y ⟶ Y ⊞ I) := by
  have hz : (projectiveStableQuotient (C := C)).map (i ≫ (biprod.inr : I ⟶ Y ⊞ I)) = 0 := by
    rw [functor_map_eq_zero_iff]
    exact ⟨I, (FrobeniusAbelian.projective_iff_injective I).mpr inferInstance, i, biprod.inr, rfl⟩
  rw [biprod.lift_eq, Functor.map_add, hz, add_zero, Functor.map_comp]

/-- The first map of the cokernel sequence of a composable pair. -/
abbrev cokernelCompFirst {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cokernel f ⟶ cokernel (f ≫ g) :=
  cokernel.map f (f ≫ g) (𝟙 X) g (by simp)

/-- The second map of the cokernel sequence of a composable pair. -/
abbrev cokernelCompSecond {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cokernel (f ≫ g) ⟶ cokernel g :=
  cokernel.map (f ≫ g) g f (𝟙 Z) (by simp)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem cokernelComp_condition {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cokernelCompFirst f g ≫ cokernelCompSecond f g = 0 := by
  apply (cancel_epi (cokernel.π f)).1
  simp

/-- The ambient cokernel sequence associated to a composable pair. -/
abbrev cokernelCompSequence {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : ShortComplex C :=
  ShortComplex.mk (cokernelCompFirst f g) (cokernelCompSecond f g)
    (cokernelComp_condition f g)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem cokernelCompSequence_exact {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (cokernelCompSequence f g).Exact := by
  have h := (kernelCokernelCompSequence_exact f g).exact 3
  dsimp [kernelCokernelCompSequence, ComposableArrows.sc, ComposableArrows.sc',
    ComposableArrows.Precomp.map] at h
  exact h

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem cokernelCompFirst_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    Mono (cokernelCompFirst f g) := by
  let S := (kernelCokernelCompSequence_exact f g).sc' 2 3 4
  have hS : S.Exact := (kernelCokernelCompSequence_exact f g).exact 2
  have hz : S.f = 0 := (isZero_kernel_of_mono g).eq_of_src _ _
  exact (S.exact_iff_mono hz).mp hS

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem cokernelCompSequence_shortExact {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono g] : (cokernelCompSequence f g).ShortExact where
  exact := cokernelCompSequence_exact f g
  mono_f := cokernelCompFirst_mono f g
  epi_g := by
    dsimp [cokernelCompSecond, cokernel.map]
    infer_instance

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem cokernelSequence_shortExact {X Y : C} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.cokernelSequence f).ShortExact where
  exact := ShortComplex.cokernelSequence_exact f
  mono_f := by dsimp [ShortComplex.cokernelSequence]; infer_instance
  epi_g := by dsimp [ShortComplex.cokernelSequence]; infer_instance

/-- The first natural short exact diagram in the ambient octahedron. -/
def cokernelCompMap₁ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShortComplex.cokernelSequence f ⟶ ShortComplex.cokernelSequence (f ≫ g) where
  τ₁ := 𝟙 X
  τ₂ := g
  τ₃ := cokernelCompFirst f g
  comm₁₂ := by simp [ShortComplex.cokernelSequence]
  comm₂₃ := by simp [ShortComplex.cokernelSequence]

/-- The second natural short exact diagram in the ambient octahedron. -/
def cokernelCompMap₂ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShortComplex.cokernelSequence (f ≫ g) ⟶ ShortComplex.cokernelSequence g where
  τ₁ := f
  τ₂ := 𝟙 Z
  τ₃ := cokernelCompSecond f g
  comm₁₂ := by simp [ShortComplex.cokernelSequence]
  comm₂₃ := by simp [ShortComplex.cokernelSequence]

/-- This natural short exact diagram computes the connecting map on the
remaining side of the octahedron. -/
def cokernelCompMap₃ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShortComplex.cokernelSequence g ⟶ cokernelCompSequence f g where
  τ₁ := cokernel.π f
  τ₂ := cokernel.π (f ≫ g)
  τ₃ := 𝟙 (cokernel g)
  comm₁₂ := by simp [ShortComplex.cokernelSequence]
  comm₂₃ := by simp [ShortComplex.cokernelSequence]

section WithCompatibleShift

variable [HasShift (projectiveStableCategory C) ℤ]
  (e : Cosyzygy.functor (C := C) ≅ shiftFunctor (projectiveStableCategory C) (1 : ℤ))
  [∀ n : ℤ, (shiftFunctor (projectiveStableCategory C) n).Additive]

open CategoryTheory.Pretriangulated

omit [∀ n : ℤ, (shiftFunctor (projectiveStableCategory C) n).Additive] in
/-- The ambient short exact cokernel triangles are distinguished in the
constructed pretriangulation. -/
theorem cokernelTriangle_distinguished {X Y : C} (f : X ⟶ Y) [Mono f] :
    triangle e (cokernelSequence_shortExact f) ∈ distinguishedTriangles e :=
  ⟨ShortComplex.cokernelSequence f, cokernelSequence_shortExact f, ⟨Iso.refl _⟩⟩

/-- The octahedron for a composable pair of ambient monomorphisms. Its final
side is the genuine short exact cokernel sequence, and all connecting squares
come from natural maps of ambient short exact sequences. -/
theorem monoPair_octahedron {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono f] [Mono g] :
    letI := pretriangulated e
    ∃ (v₁₂ : (projectiveStableQuotient (C := C)).obj Y ⟶
          (projectiveStableQuotient (C := C)).obj (cokernel f))
      (w₁₂ : (projectiveStableQuotient (C := C)).obj (cokernel f) ⟶
          ((projectiveStableQuotient (C := C)).obj X)⟦(1 : ℤ)⟧)
      (h₁₂ : Triangle.mk ((projectiveStableQuotient (C := C)).map f) v₁₂ w₁₂ ∈
        CategoryTheory.Pretriangulated.distinguishedTriangles)
      (v₂₃ : (projectiveStableQuotient (C := C)).obj Z ⟶
          (projectiveStableQuotient (C := C)).obj (cokernel g))
      (w₂₃ : (projectiveStableQuotient (C := C)).obj (cokernel g) ⟶
          ((projectiveStableQuotient (C := C)).obj Y)⟦(1 : ℤ)⟧)
      (h₂₃ : Triangle.mk ((projectiveStableQuotient (C := C)).map g) v₂₃ w₂₃ ∈
        CategoryTheory.Pretriangulated.distinguishedTriangles)
      (v₁₃ : (projectiveStableQuotient (C := C)).obj Z ⟶
          (projectiveStableQuotient (C := C)).obj (cokernel (f ≫ g)))
      (w₁₃ : (projectiveStableQuotient (C := C)).obj (cokernel (f ≫ g)) ⟶
          ((projectiveStableQuotient (C := C)).obj X)⟦(1 : ℤ)⟧)
      (h₁₃ : Triangle.mk
          ((projectiveStableQuotient (C := C)).map f ≫ (projectiveStableQuotient (C := C)).map g)
          v₁₃ w₁₃ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles),
      Nonempty (CategoryTheory.Triangulated.Octahedron rfl h₁₂ h₂₃ h₁₃) := by
  let _ := pretriangulated e
  let v₁₂ := (projectiveStableQuotient (C := C)).map (cokernel.π f)
  let v₂₃ := (projectiveStableQuotient (C := C)).map (cokernel.π g)
  let v₁₃ := (projectiveStableQuotient (C := C)).map (cokernel.π (f ≫ g))
  let w₁₂ := (triangle e (cokernelSequence_shortExact f)).mor₃
  let w₂₃ := (triangle e (cokernelSequence_shortExact g)).mor₃
  let w₁₃ := (triangle e (cokernelSequence_shortExact (f ≫ g))).mor₃
  have h₁₂ : Triangle.mk ((projectiveStableQuotient (C := C)).map f) v₁₂ w₁₂ ∈
      CategoryTheory.Pretriangulated.distinguishedTriangles := cokernelTriangle_distinguished e f
  have h₂₃ : Triangle.mk ((projectiveStableQuotient (C := C)).map g) v₂₃ w₂₃ ∈
      CategoryTheory.Pretriangulated.distinguishedTriangles := cokernelTriangle_distinguished e g
  have h₁₃ : Triangle.mk
      ((projectiveStableQuotient (C := C)).map f ≫ (projectiveStableQuotient (C := C)).map g)
      v₁₃ w₁₃ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles := by
    rw [← Functor.map_comp]
    exact cokernelTriangle_distinguished e (f ≫ g)
  let φ₁ := triangleMap e (cokernelSequence_shortExact f)
    (cokernelSequence_shortExact (f ≫ g)) (cokernelCompMap₁ f g)
  let φ₂ := triangleMap e (cokernelSequence_shortExact (f ≫ g))
    (cokernelSequence_shortExact g) (cokernelCompMap₂ f g)
  let φ₃ := triangleMap e (cokernelSequence_shortExact g)
    (cokernelCompSequence_shortExact f g) (cokernelCompMap₃ f g)
  refine ⟨v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, ⟨{
    m₁ := (projectiveStableQuotient (C := C)).map (cokernelCompFirst f g)
    m₃ := (projectiveStableQuotient (C := C)).map (cokernelCompSecond f g)
    comm₁ := ?_
    comm₂ := ?_
    comm₃ := ?_
    comm₄ := ?_
    mem := ?_ }⟩⟩
  · exact φ₁.comm₂
  · simpa [φ₁, triangleMap, cokernelCompMap₁, w₁₂, w₁₃, triangle, Triangle.mk,
      ShortComplex.cokernelSequence, Functor.map_id] using φ₁.comm₃.symm
  · simpa [φ₂, triangleMap, cokernelCompMap₂, v₁₃, v₂₃, triangle, Triangle.mk,
      ShortComplex.cokernelSequence, Functor.map_id] using φ₂.comm₂
  · exact φ₂.comm₃
  · have hc : w₂₃ ≫ v₁₂⟦1⟧' =
        (triangle e (cokernelCompSequence_shortExact f g)).mor₃ := by
      simpa [φ₃, triangleMap, cokernelCompMap₃, w₂₃, v₁₂, triangle, Triangle.mk,
        ShortComplex.cokernelSequence, Functor.map_id] using φ₃.comm₃
    rw [hc]
    exact ⟨cokernelCompSequence f g, cokernelCompSequence_shortExact f g, ⟨Iso.refl _⟩⟩

/-- The canonical pretriangulation satisfies the full octahedron axiom. A
general stable composable pair is represented by ambient monomorphisms after
adding injective summands; the monomorphism octahedron is then transported by
mathlib's proved `IsTriangulated.mk'` constructor. -/
theorem isTriangulated :
    letI := pretriangulated e
    CategoryTheory.IsTriangulated (projectiveStableCategory C) := by
  let _ := pretriangulated e
  apply CategoryTheory.IsTriangulated.mk'
  rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g
  obtain ⟨f', rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
  obtain ⟨g', rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective g
  let Y' := Y ⊞ Injective.under X
  let Z' := Z ⊞ Injective.under Y'
  let f'' : X ⟶ Y' := biprod.lift f' (Injective.ι X)
  let g'' : Y' ⟶ Z' := biprod.lift (biprod.fst ≫ g') (Injective.ι Y')
  let _ : Mono f'' := by dsimp [f'']; infer_instance
  let _ : Mono g'' := by dsimp [g'']; infer_instance
  let E₂ := stableBiprodInjectiveIso Y (Injective.under X)
  let E₃ := stableBiprodInjectiveIso Z (Injective.under Y')
  obtain ⟨v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, ho⟩ :=
    monoPair_octahedron e f'' g''
  refine ⟨(projectiveStableQuotient (C := C)).obj X,
    (projectiveStableQuotient (C := C)).obj Y',
    (projectiveStableQuotient (C := C)).obj Z',
    (projectiveStableQuotient (C := C)).obj (cokernel f''),
    (projectiveStableQuotient (C := C)).obj (cokernel g''),
    (projectiveStableQuotient (C := C)).obj (cokernel (f'' ≫ g'')),
    (projectiveStableQuotient (C := C)).map f'',
    (projectiveStableQuotient (C := C)).map g'',
    Iso.refl _, E₂.symm, E₃.symm, ?_, ?_,
    v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, ho⟩
  · simp only [Iso.refl_hom, Category.id_comp]
    change (projectiveStableQuotient (C := C)).map f' ≫
        (projectiveStableQuotient (C := C)).map biprod.inl =
      (projectiveStableQuotient (C := C)).map (biprod.lift f' (Injective.ι X))
    exact (stable_lift_eq f' (Injective.ι X)).symm
  · change (projectiveStableQuotient (C := C)).map g' ≫
        (projectiveStableQuotient (C := C)).map biprod.inl =
      (projectiveStableQuotient (C := C)).map biprod.inl ≫
        (projectiveStableQuotient (C := C)).map (biprod.lift (biprod.fst ≫ g') (Injective.ι Y'))
    rw [stable_lift_eq, Functor.map_comp]
    simp [← Functor.map_comp]

end WithCompatibleShift

end PretriangulatedV2.StableCategory.FrobeniusTriangles
