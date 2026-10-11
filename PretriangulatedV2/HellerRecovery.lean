import PretriangulatedV2.HellerClassification
import PretriangulatedV2.ComplexInjectiveExtensions
import PretriangulatedV2.YonedaHellerTransport

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace PretriangulatedV2.HellerRecovery

open HellerClassification

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]
  [HasShift (Projectives (C := C)) ℤ]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))]

omit [HasBinaryBiproducts C] [FrobeniusAbelian C]
  [HasShift (Projectives (C := C)) ℤ]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))] in
/-- Negating a morphism does not change its kernel, expressed through the
actual universal properties rather than an abelian image calculation. -/
def kernelNegIso {X Y : C} (f : X ⟶ Y) : kernel (-f) ≅ kernel f :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.isLimitOfIsLimitOfIff' (kernelIsKernel (-f)) f (fun {_} φ => by
      rw [Preadditive.comp_neg, neg_eq_zero]))
    (limit.isLimit (parallelPair f 0))

omit [HasBinaryBiproducts C] in
/-- Hom-exactness of a distinguished triangle of projective-injectives upgrades
to actual ambient exactness, because an arbitrary target embeds in an injective
(hence projective) object. -/
theorem underlying_exact_of_distinguished
    (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (CategoryTheory.Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C))))) :
    (ShortComplex.mk T.mor₁.hom T.mor₂.hom (by
      exact congrArg (fun f => f.hom) (comp_distTriang_mor_zero₁₂ T hT))).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z q hq
  let I := Injective.under Z
  let j : Z ⟶ I := Injective.ι Z
  let k : kernel T.mor₂.hom ⟶ T.obj₂.obj := kernel.ι T.mor₂.hom
  let r : T.obj₂.obj ⟶ I := Injective.factorThru (q ≫ j) k
  have hr : k ≫ r = q ≫ j := Injective.comp_factorThru _ _
  let I' : Projectives (C := C) :=
    ⟨I, (FrobeniusAbelian.projective_iff_injective I).mpr inferInstance⟩
  let r' : T.obj₂ ⟶ I' := ObjectProperty.homMk r
  have hmor₁ : T.mor₁ ≫ r' = 0 := by
    apply ObjectProperty.hom_ext
    change T.mor₁.hom ≫ r = 0
    rw [← kernel.lift_ι T.mor₂.hom T.mor₁.hom,
      Category.assoc, hr, ← Category.assoc, hq, zero_comp]
    exact congrArg (fun f => f.hom) (comp_distTriang_mor_zero₁₂ T hT)
  obtain ⟨s, hs⟩ := T.yoneda_exact₂ hT r' hmor₁
  apply (cancel_mono j).mp
  rw [← hr]
  have hs' : r = T.mor₂.hom ≫ s.hom := congrArg (fun f => f.hom) hs
  rw [hs', ← Category.assoc, kernel.condition, zero_comp, zero_comp]

section CompatibleShift

variable (S : C ≌ C) [S.functor.Additive]
  (e : shiftFunctor (Projectives (C := C)) (1 : ℤ) ≅
    (projectiveEquivalence S).functor)

/-- The ambient representative of the third map, using compatibility of the
given projective shift with the restricted ambient autoequivalence. -/
abbrev ambientBoundary (T : Triangle (Projectives (C := C))) :
    T.obj₃.obj ⟶ ((projectiveEquivalence S).functor.obj T.obj₁).obj :=
  (T.mor₃ ≫ e.hom.app T.obj₁).hom

omit [HasBinaryBiproducts C] [S.functor.Additive] in
theorem ambient_exact₁₂ (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (CategoryTheory.Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C))))) :
    (ShortComplex.mk T.mor₂.hom (ambientBoundary S e T) (by
      exact congrArg (fun f : T.obj₂ ⟶ (projectiveEquivalence S).functor.obj T.obj₁ =>
        f.hom) (by
        apply ObjectProperty.hom_ext
        change T.mor₂.hom ≫ T.mor₃.hom ≫ (e.hom.app T.obj₁).hom = 0
        have hz : T.mor₂.hom ≫ T.mor₃.hom = 0 := by
          simpa only [ObjectProperty.FullSubcategory.comp_hom,
            ObjectProperty.zero_hom] using
              congrArg (fun f => f.hom) (comp_distTriang_mor_zero₂₃ T hT)
        rw [← Category.assoc, hz, zero_comp]))).Exact := by
  let A : ShortComplex C :=
    ShortComplex.mk T.rotate.mor₁.hom T.rotate.mor₂.hom
      (congrArg (fun f => f.hom)
        (comp_distTriang_mor_zero₁₂ T.rotate (rot_of_distTriang T hT)))
  let B : ShortComplex C :=
    ShortComplex.mk T.mor₂.hom (ambientBoundary S e T) (by
      exact congrArg (fun f : T.obj₂ ⟶ (projectiveEquivalence S).functor.obj T.obj₁ =>
        f.hom) (by
        apply ObjectProperty.hom_ext
        change T.mor₂.hom ≫ T.mor₃.hom ≫ (e.hom.app T.obj₁).hom = 0
        have hz : T.mor₂.hom ≫ T.mor₃.hom = 0 := by
          simpa only [ObjectProperty.FullSubcategory.comp_hom,
            ObjectProperty.zero_hom] using
              congrArg (fun f => f.hom) (comp_distTriang_mor_zero₂₃ T hT)
        rw [← Category.assoc, hz, zero_comp]))
  let ε₃ : T.rotate.obj₃.obj ≅ B.X₃ :=
    (projectives (C := C)).ι.mapIso (e.app T.obj₁)
  let i : A ≅ B := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) ε₃
    (by change 𝟙 _ ≫ T.mor₂.hom = T.mor₂.hom ≫ 𝟙 _; simp)
    (by change 𝟙 _ ≫ (T.mor₃ ≫ e.hom.app T.obj₁).hom =
        T.mor₃.hom ≫ (e.hom.app T.obj₁).hom
        simp)
  exact ShortComplex.exact_of_iso i
    (underlying_exact_of_distinguished T.rotate (rot_of_distTriang T hT))

omit [HasBinaryBiproducts C] [S.functor.Additive] in
theorem ambient_exact₂₃ (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (CategoryTheory.Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C))))) :
    (ShortComplex.mk (ambientBoundary S e T)
      (-((projectiveEquivalence S).functor.map T.mor₁).hom) (by
        exact congrArg (fun f : T.obj₃ ⟶
          (projectiveEquivalence S).functor.obj T.obj₂ => f.hom) (by
          apply ObjectProperty.hom_ext
          change (T.mor₃.hom ≫ (e.hom.app T.obj₁).hom) ≫
            (-((projectiveEquivalence S).functor.map T.mor₁).hom) = 0
          have he :
              ((shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom ≫
                  (e.hom.app T.obj₂).hom =
                (e.hom.app T.obj₁).hom ≫
                  ((projectiveEquivalence S).functor.map T.mor₁).hom := by
            simpa only [ObjectProperty.FullSubcategory.comp_hom] using
              congrArg (fun f => f.hom) (e.hom.naturality T.mor₁)
          have hz : T.mor₃.hom ≫
              ((shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom = 0 := by
            simpa only [ObjectProperty.FullSubcategory.comp_hom,
              ObjectProperty.zero_hom] using
                congrArg (fun f => f.hom) (comp_distTriang_mor_zero₃₁ T hT)
          rw [Preadditive.comp_neg, Category.assoc, ← he,
            ← Category.assoc, hz, zero_comp, neg_zero]))).Exact := by
  let hR := rot_of_distTriang T hT
  let hRR := rot_of_distTriang T.rotate hR
  let A : ShortComplex C :=
    ShortComplex.mk T.rotate.rotate.mor₁.hom T.rotate.rotate.mor₂.hom
      (congrArg (fun f => f.hom)
        (comp_distTriang_mor_zero₁₂ T.rotate.rotate hRR))
  let B : ShortComplex C :=
    ShortComplex.mk (ambientBoundary S e T)
      (-((projectiveEquivalence S).functor.map T.mor₁).hom) (by
        exact congrArg (fun f : T.obj₃ ⟶
          (projectiveEquivalence S).functor.obj T.obj₂ => f.hom) (by
          apply ObjectProperty.hom_ext
          change (T.mor₃.hom ≫ (e.hom.app T.obj₁).hom) ≫
            (-((projectiveEquivalence S).functor.map T.mor₁).hom) = 0
          have he :
              ((shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom ≫
                  (e.hom.app T.obj₂).hom =
                (e.hom.app T.obj₁).hom ≫
                  ((projectiveEquivalence S).functor.map T.mor₁).hom := by
            simpa only [ObjectProperty.FullSubcategory.comp_hom] using
              congrArg (fun f => f.hom) (e.hom.naturality T.mor₁)
          have hz : T.mor₃.hom ≫
              ((shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom = 0 := by
            simpa only [ObjectProperty.FullSubcategory.comp_hom,
              ObjectProperty.zero_hom] using
                congrArg (fun f => f.hom) (comp_distTriang_mor_zero₃₁ T hT)
          rw [Preadditive.comp_neg, Category.assoc, ← he,
            ← Category.assoc, hz, zero_comp, neg_zero]))
  let ε₂ : T.rotate.rotate.obj₂.obj ≅ B.X₂ :=
    (projectives (C := C)).ι.mapIso (e.app T.obj₁)
  let ε₃ : T.rotate.rotate.obj₃.obj ≅ B.X₃ :=
    (projectives (C := C)).ι.mapIso (e.app T.obj₂)
  let i : A ≅ B := ShortComplex.isoMk (Iso.refl _) ε₂ ε₃
    (by change 𝟙 _ ≫ (T.mor₃ ≫ e.hom.app T.obj₁).hom =
        T.mor₃.hom ≫ (e.hom.app T.obj₁).hom
        simp) (by
      change (e.hom.app T.obj₁).hom ≫
          (-((projectiveEquivalence S).functor.map T.mor₁).hom) =
        (-(shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom ≫
          (e.hom.app T.obj₂).hom
      exact congrArg (fun f :
          (shiftFunctor (Projectives (C := C)) (1 : ℤ)).obj T.obj₁ ⟶
            (projectiveEquivalence S).functor.obj T.obj₂ => f.hom) (by
        apply ObjectProperty.hom_ext
        change (e.hom.app T.obj₁).hom ≫
            (-((projectiveEquivalence S).functor.map T.mor₁).hom) =
          (-((shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom) ≫
            (e.hom.app T.obj₂).hom
        have he :
            ((shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom ≫
                (e.hom.app T.obj₂).hom =
              (e.hom.app T.obj₁).hom ≫
                ((projectiveEquivalence S).functor.map T.mor₁).hom := by
          simpa only [ObjectProperty.FullSubcategory.comp_hom] using
            congrArg (fun f => f.hom) (e.hom.naturality T.mor₁)
        rw [Preadditive.comp_neg, Preadditive.neg_comp, ← he]))
  exact ShortComplex.exact_of_iso i
    (underlying_exact_of_distinguished T.rotate.rotate hRR)

/-- Before identifying the last kernel with `S(kernel f)`, a distinguished
triangle gives three literal kernel-to-kernel short exact rows. -/
def triangleExtensionLocal (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (CategoryTheory.Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C))))) :
    StableCategory.InjectiveComparison.Extension3
      (kernel T.mor₁.hom)
      (kernel (-((projectiveEquivalence S).functor.map T.mor₁).hom)) := by
  let h₀₁ : T.mor₁.hom ≫ T.mor₂.hom = 0 :=
    congrArg (fun f => f.hom) (comp_distTriang_mor_zero₁₂ T hT)
  let h₁₂ : T.mor₂.hom ≫ ambientBoundary S e T = 0 := by
    exact congrArg (fun f : T.obj₂ ⟶ (projectiveEquivalence S).functor.obj T.obj₁ =>
      f.hom) (by
      apply ObjectProperty.hom_ext
      change T.mor₂.hom ≫ T.mor₃.hom ≫ (e.hom.app T.obj₁).hom = 0
      have hz : T.mor₂.hom ≫ T.mor₃.hom = 0 := by
        simpa only [ObjectProperty.FullSubcategory.comp_hom,
          ObjectProperty.zero_hom] using
            congrArg (fun f => f.hom) (comp_distTriang_mor_zero₂₃ T hT)
      rw [← Category.assoc, hz, zero_comp])
  let h₂₃ : ambientBoundary S e T ≫
      (-((projectiveEquivalence S).functor.map T.mor₁).hom) = 0 := by
    exact congrArg (fun f : T.obj₃ ⟶
      (projectiveEquivalence S).functor.obj T.obj₂ => f.hom) (by
      apply ObjectProperty.hom_ext
      change (T.mor₃.hom ≫ (e.hom.app T.obj₁).hom) ≫
        (-((projectiveEquivalence S).functor.map T.mor₁).hom) = 0
      have he :
          ((shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom ≫
              (e.hom.app T.obj₂).hom =
            (e.hom.app T.obj₁).hom ≫
              ((projectiveEquivalence S).functor.map T.mor₁).hom := by
        simpa only [ObjectProperty.FullSubcategory.comp_hom] using
          congrArg (fun f => f.hom) (e.hom.naturality T.mor₁)
      have hz : T.mor₃.hom ≫
          ((shiftFunctor (Projectives (C := C)) (1 : ℤ)).map T.mor₁).hom = 0 := by
        simpa only [ObjectProperty.FullSubcategory.comp_hom,
          ObjectProperty.zero_hom] using
            congrArg (fun f => f.hom) (comp_distTriang_mor_zero₃₁ T hT)
      rw [Preadditive.comp_neg, Category.assoc, ← he,
        ← Category.assoc, hz, zero_comp, neg_zero])
  exact {
    Z₁ := kernel T.mor₂.hom
    Z₂ := kernel (ambientBoundary S e T)
    I₀ := T.obj₁.obj
    I₁ := T.obj₂.obj
    I₂ := T.obj₃.obj
    i₀ := kernel.ι T.mor₁.hom
    p₀ := kernel.lift T.mor₂.hom T.mor₁.hom h₀₁
    i₁ := kernel.ι T.mor₂.hom
    p₁ := kernel.lift (ambientBoundary S e T) T.mor₂.hom h₁₂
    i₂ := kernel.ι (ambientBoundary S e T)
    p₂ := kernel.lift (-((projectiveEquivalence S).functor.map T.mor₁).hom)
      (ambientBoundary S e T) h₂₃
    zero₀ := (StableCategory.InjectiveComparison.cyclesSequence
      T.mor₁.hom T.mor₂.hom h₀₁).zero
    zero₁ := (StableCategory.InjectiveComparison.cyclesSequence
      T.mor₂.hom (ambientBoundary S e T) h₁₂).zero
    zero₂ := (StableCategory.InjectiveComparison.cyclesSequence
      (ambientBoundary S e T)
      (-((projectiveEquivalence S).functor.map T.mor₁).hom) h₂₃).zero
    exact₀ := StableCategory.InjectiveComparison.cyclesSequence_shortExact
      T.mor₁.hom T.mor₂.hom h₀₁
      (underlying_exact_of_distinguished T hT)
    exact₁ := StableCategory.InjectiveComparison.cyclesSequence_shortExact
      T.mor₂.hom (ambientBoundary S e T) h₁₂
      (ambient_exact₁₂ S e T hT)
    exact₂ := StableCategory.InjectiveComparison.cyclesSequence_shortExact
      (ambientBoundary S e T)
      (-((projectiveEquivalence S).functor.map T.mor₁).hom) h₂₃
      (ambient_exact₂₃ S e T hT)
    injective₀ := inferInstance
    injective₁ := inferInstance
    injective₂ := inferInstance }

/-- The right kernel in `triangleExtensionLocal` is the ambient shift of its
left kernel: first remove the rotation sign, then use preservation of kernels
by the ambient equivalence. -/
def triangleEndpointIso (T : Triangle (Projectives (C := C))) :
    kernel (-((projectiveEquivalence S).functor.map T.mor₁).hom) ≅
      S.functor.obj (kernel T.mor₁.hom) := by
  let k : kernel (-S.functor.map T.mor₁.hom) ≅
      S.functor.obj (kernel T.mor₁.hom) :=
    kernelNegIso (S.functor.map T.mor₁.hom) ≪≫
      (PreservesKernel.iso S.functor T.mor₁.hom).symm
  rw [projectiveEquivalence_map_hom]
  exact k

/-- A distinguished triangle of projective-injectives therefore yields an
actual three-step injective extension from `ker(f)` to `S(ker(f))`. -/
def triangleExtension (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (CategoryTheory.Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C))))) :
    StableCategory.InjectiveComparison.Extension3
      (kernel T.mor₁.hom) (S.functor.obj (kernel T.mor₁.hom)) :=
  StableCategory.ComplexInjectiveExtensions.transportEndpoint
    (triangleExtensionLocal S e T hT) (triangleEndpointIso S T)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))] [S.functor.Additive] [Abelian C] in
/-- The third ambient boundary square follows from the actual triangle
morphism and naturality of the first-shift comparison. -/
theorem ambientBoundary_naturality {T T' : Triangle (Projectives (C := C))}
    (φ : T ⟶ T') :
    ambientBoundary S e T ≫ ((projectiveEquivalence S).functor.map φ.hom₁).hom =
      φ.hom₃.hom ≫ ambientBoundary S e T' := by
  have ht := congrArg (fun t => t ≫ e.hom.app T'.obj₁) φ.comm₃
  rw [Category.assoc, e.hom.naturality] at ht
  simpa only [ambientBoundary, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc] using congrArg (fun t => t.hom) ht

omit [HasBinaryBiproducts C] [FrobeniusAbelian C]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))] [S.functor.Additive] in
/-- The signed fourth square is a genuine mapped first triangle square. -/
theorem signed_first_square {T T' : Triangle (Projectives (C := C))}
    (φ : T ⟶ T') :
    (-((projectiveEquivalence S).functor.map T.mor₁).hom) ≫
        ((projectiveEquivalence S).functor.map φ.hom₂).hom =
      ((projectiveEquivalence S).functor.map φ.hom₁).hom ≫
        (-((projectiveEquivalence S).functor.map T'.mor₁).hom) := by
  have ht := congrArg (fun t => t.hom) ((projectiveEquivalence S).functor.congr_map φ.comm₁)
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at ht
  rw [Preadditive.neg_comp, Preadditive.comp_neg, ht]

/-- Actual triangle morphisms induce actual morphisms of all three kernel
rows before transport of the final endpoint. -/
def triangleExtensionLocalMap {T T' : Triangle (Projectives (C := C))}
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (hT' : T' ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (φ : T ⟶ T') : (triangleExtensionLocal S e T hT).Hom
      (triangleExtensionLocal S e T' hT') where
  f₀ := kernel.map T.mor₁.hom T'.mor₁.hom φ.hom₁.hom φ.hom₂.hom
    (congrArg (fun t => t.hom) φ.comm₁)
  f₁ := kernel.map T.mor₂.hom T'.mor₂.hom φ.hom₂.hom φ.hom₃.hom
    (congrArg (fun t => t.hom) φ.comm₂)
  f₂ := kernel.map (ambientBoundary S e T) (ambientBoundary S e T') φ.hom₃.hom
    ((projectiveEquivalence S).functor.map φ.hom₁).hom (ambientBoundary_naturality S e φ)
  f₃ := kernel.map (-((projectiveEquivalence S).functor.map T.mor₁).hom)
    (-((projectiveEquivalence S).functor.map T'.mor₁).hom)
    ((projectiveEquivalence S).functor.map φ.hom₁).hom
    ((projectiveEquivalence S).functor.map φ.hom₂).hom (signed_first_square S φ)
  a₀ := φ.hom₁.hom
  a₁ := φ.hom₂.hom
  a₂ := φ.hom₃.hom
  comm_i₀ := by simp [triangleExtensionLocal]
  comm_p₀ := by
    apply (cancel_mono (kernel.ι T'.mor₂.hom)).mp
    simp only [triangleExtensionLocal, Category.assoc, kernel.map, kernel.lift_ι, kernel.lift_ι_assoc]
    exact congrArg (fun t => t.hom) φ.comm₁
  comm_i₁ := by simp [triangleExtensionLocal]
  comm_p₁ := by
    apply (cancel_mono (kernel.ι (ambientBoundary S e T'))).mp
    simp only [triangleExtensionLocal, Category.assoc, kernel.map, kernel.lift_ι, kernel.lift_ι_assoc]
    exact congrArg (fun t => t.hom) φ.comm₂
  comm_i₂ := by simp [triangleExtensionLocal]
  comm_p₂ := by
    apply (cancel_mono (kernel.ι (-((projectiveEquivalence S).functor.map T'.mor₁).hom))).mp
    simp only [triangleExtensionLocal, Category.assoc, kernel.map, kernel.lift_ι, kernel.lift_ι_assoc]
    exact ambientBoundary_naturality S e φ


omit [HasBinaryBiproducts C] [FrobeniusAbelian C]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))]
  [HasShift (Projectives (C := C)) ℤ] in
@[reassoc (attr := simp)]
theorem kernelNegIso_hom_ι {X Y : C} (f : X ⟶ Y) :
    (kernelNegIso f).hom ≫ kernel.ι f = kernel.ι (-f) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

omit [HasBinaryBiproducts C] [FrobeniusAbelian C]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))] in
@[reassoc]
theorem triangleEndpointIso_hom_ι (T : Triangle (Projectives (C := C))) :
    (triangleEndpointIso S T).hom ≫ S.functor.map (kernel.ι T.mor₁.hom) =
      kernel.ι (-((projectiveEquivalence S).functor.map T.mor₁).hom) := by
  simp [triangleEndpointIso, projectiveEquivalence_map_hom]

/-- Genuine triangle morphisms induce genuine three-row extension maps. -/
def triangleExtensionMap {T T' : Triangle (Projectives (C := C))}
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (hT' : T' ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (φ : T ⟶ T') : (triangleExtension S e T hT).Hom (triangleExtension S e T' hT') :=
  StableCategory.ComplexInjectiveExtensions.transportEndpointMap
    (triangleExtensionLocalMap S e hT hT' φ)
    (triangleEndpointIso S T) (triangleEndpointIso S T')

omit [HasBinaryBiproducts C] in
/-- The final extension map is exactly the ambient shift of its initial
kernel map; both endpoint transports are justified by kernel uniqueness. -/
theorem triangleExtensionMap_f₃ {T T' : Triangle (Projectives (C := C))}
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (hT' : T' ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (φ : T ⟶ T') :
    (triangleExtensionMap S e hT hT' φ).f₃ =
      S.functor.map (triangleExtensionMap S e hT hT' φ).f₀ := by
  apply (cancel_mono (S.functor.map (kernel.ι T'.mor₁.hom))).mp
  dsimp [triangleExtensionMap, StableCategory.ComplexInjectiveExtensions.transportEndpointMap,
    triangleExtensionLocalMap]
  rw [Category.assoc, Category.assoc, triangleEndpointIso_hom_ι]
  simp only [projectiveEquivalence_map_hom, kernel.map, kernel.lift_ι]
  have hk := triangleEndpointIso_hom_ι S T
  simp only [projectiveEquivalence_map_hom] at hk
  rw [← hk]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Functor.map_comp, kernel.lift_ι]


/-- The two chosen injectives whose composite differential presents `M` as a
kernel. -/
abbrev chosenP₀ (M : C) : Projectives (C := C) :=
  ⟨Injective.under M,
    (FrobeniusAbelian.projective_iff_injective (Injective.under M)).mpr inferInstance⟩

abbrev chosenP₁ (M : C) : Projectives (C := C) :=
  ⟨Injective.under (StableCategory.Cosyzygy.obj M),
    (FrobeniusAbelian.projective_iff_injective
      (Injective.under (StableCategory.Cosyzygy.obj M))).mpr inferInstance⟩

def chosenDifferential (M : C) : chosenP₀ M ⟶ chosenP₁ M :=
  ObjectProperty.homMk (cokernel.π (Injective.ι M) ≫
    Injective.ι (StableCategory.Cosyzygy.obj M))

/-- A fixed TR1 completion of the chosen two-injective differential. -/
noncomputable def chosenTriangle (M : C) : Triangle (Projectives (C := C)) :=
  let H := CategoryTheory.Pretriangulated.distinguished_cocone_triangle
    (chosenDifferential M)
  Triangle.mk (chosenDifferential M) H.choose_spec.choose
    H.choose_spec.choose_spec.choose

omit [HasBinaryBiproducts C] in
theorem chosenTriangle_distinguished (M : C) :
    chosenTriangle M ∈ (CategoryTheory.Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C)))) := by
  dsimp [chosenTriangle]
  exact (CategoryTheory.Pretriangulated.distinguished_cocone_triangle
    (chosenDifferential M)).choose_spec.choose_spec.choose_spec

omit [S.functor.Additive] in
/-- `M` is the literal kernel of the chosen composite differential, up to the
canonical unique kernel isomorphism. -/
def chosenKernelIso (M : C) :
    M ≅ kernel (chosenDifferential M).hom := by
  let d := (chosenDifferential M).hom
  let hc : IsLimit (KernelFork.ofι (Injective.ι M)
      (show Injective.ι M ≫ d = 0 by simp [d, chosenDifferential])) :=
    KernelFork.isLimitOfIsLimitOfIff'
      (StableCategory.InjectiveComparison.chosenSequence_shortExact M).fIsKernel d
      (fun {_} φ => by
        constructor
        · intro h
          dsimp [d, chosenDifferential]
          rw [← Category.assoc, h, zero_comp]
        · intro h
          change φ ≫ cokernel.π (Injective.ι M) ≫
            Injective.ι (StableCategory.Cosyzygy.obj M) = 0 at h
          apply (cancel_mono (Injective.ι (StableCategory.Cosyzygy.obj M))).mp
          simpa only [Category.assoc, zero_comp] using h)
  exact IsLimit.conePointUniqueUpToIso hc (limit.isLimit (parallelPair d 0))

/-- The candidate recovered Heller isomorphism at one ambient object.  The
middle factor is the stable comparison of the chosen distinguished
completion; the outer factors replace its literal kernel by `M`. -/
def recoveredDeltaComponent (M : C) :
    (StableCategory.stableFunctor S.functor).obj
        ((StableCategory.projectiveStableQuotient (C := C)).obj M) ≅
      (cube (StableCategory.Cosyzygy.functor (C := C))).obj
        ((StableCategory.projectiveStableQuotient (C := C)).obj M) := by
  let T := chosenTriangle M
  let E := triangleExtension S e T (chosenTriangle_distinguished M)
  let a := (StableCategory.projectiveStableQuotient (C := C)).mapIso
    (chosenKernelIso M)
  exact (StableCategory.stableFunctor S.functor).mapIso a ≪≫
    E.stableComparison ≪≫
    (cube (StableCategory.Cosyzygy.functor (C := C))).mapIso a.symm


omit [HasBinaryBiproducts C] in
/-- The initial map of the transported extension is the induced kernel map. -/
@[simp] theorem triangleExtensionMap_f₀ {T T' : Triangle (Projectives (C := C))}
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (hT' : T' ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (φ : T ⟶ T') :
    (triangleExtensionMap S e hT hT' φ).f₀ =
      kernel.map T.mor₁.hom T'.mor₁.hom φ.hom₁.hom φ.hom₂.hom
        (congrArg (fun t => t.hom) φ.comm₁) := rfl

/-- Stable comparison of original distinguished triangles is natural for
actual triangle morphisms, with exactly the ambient shift at the endpoint. -/
theorem triangleExtension_stableComparison_naturality
    {T T' : Triangle (Projectives (C := C))}
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (hT' : T' ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (φ : T ⟶ T') :
    (StableCategory.stableFunctor S.functor).map
        ((StableCategory.projectiveStableQuotient (C := C)).map (triangleExtensionMap S e hT hT' φ).f₀) ≫
      (triangleExtension S e T' hT').stableComparison.hom =
    (triangleExtension S e T hT).stableComparison.hom ≫
      (cube StableCategory.Cosyzygy.functor).map
        ((StableCategory.projectiveStableQuotient (C := C)).map (triangleExtensionMap S e hT hT' φ).f₀) := by
  simpa only [triangleExtensionMap_f₃, StableCategory.stableFunctor_map] using
    (triangleExtensionMap S e hT hT' φ).stableComparison_naturality




section
variable {T T' : Triangle (Projectives (C := C))}
  (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
  (hT' : T' ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
  (u : kernel T.mor₁.hom ⟶ kernel T'.mor₁.hom)


/-- Extend the prescribed kernel map across the first injective terms. -/
def presentationA₀ : T.obj₁.obj ⟶ T'.obj₁.obj :=
  Injective.factorThru (u ≫ kernel.ι T'.mor₁.hom) (kernel.ι T.mor₁.hom)

omit [HasBinaryBiproducts C]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))] in
lemma presentation_i₀_a₀ :
    kernel.ι T.mor₁.hom ≫ presentationA₀ u =
      u ≫ kernel.ι T'.mor₁.hom :=
  Injective.comp_factorThru _ _

/-- The induced map on the first quotient/cycle. -/
def presentationZ₁ : kernel T.mor₂.hom ⟶ kernel T'.mor₂.hom :=
  StableCategory.FrobeniusTriangles.desc
    (StableCategory.InjectiveComparison.cyclesSequence_shortExact
      T.mor₁.hom T.mor₂.hom
        (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T hT))
        (underlying_exact_of_distinguished T hT))
    (presentationA₀ u ≫
      kernel.lift T'.mor₂.hom T'.mor₁.hom
        (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T' hT'))) (by
      change kernel.ι T.mor₁.hom ≫ presentationA₀ u ≫
        kernel.lift T'.mor₂.hom T'.mor₁.hom
          (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T' hT')) = 0
      rw [← Category.assoc, presentation_i₀_a₀ u]
      have hz := (StableCategory.InjectiveComparison.cyclesSequence
        T'.mor₁.hom T'.mor₂.hom
          (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T' hT'))).zero
      change kernel.ι T'.mor₁.hom ≫
        kernel.lift T'.mor₂.hom T'.mor₁.hom
          (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T' hT')) = 0 at hz
      rw [Category.assoc, hz, comp_zero])

omit [HasBinaryBiproducts C] in
lemma presentation_p₀_z₁ :
    kernel.lift T.mor₂.hom T.mor₁.hom
        (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T hT)) ≫
      presentationZ₁ hT hT' u =
    presentationA₀ u ≫
      kernel.lift T'.mor₂.hom T'.mor₁.hom
        (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T' hT')) :=
  StableCategory.FrobeniusTriangles.g_desc
    (StableCategory.InjectiveComparison.cyclesSequence_shortExact
      T.mor₁.hom T.mor₂.hom
        (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T hT))
        (underlying_exact_of_distinguished T hT)) _ _

/-- Extend the cycle map across the second injective terms. -/
def presentationA₁ : T.obj₂.obj ⟶ T'.obj₂.obj :=
  Injective.factorThru
    (presentationZ₁ hT hT' u ≫ kernel.ι T'.mor₂.hom)
    (kernel.ι T.mor₂.hom)

omit [HasBinaryBiproducts C] in
lemma presentation_i₁_a₁ :
    kernel.ι T.mor₂.hom ≫ presentationA₁ hT hT' u =
      presentationZ₁ hT hT' u ≫ kernel.ι T'.mor₂.hom :=
  Injective.comp_factorThru _ _

omit [HasBinaryBiproducts C] in
lemma presentation_square :
    T.mor₁.hom ≫ presentationA₁ hT hT' u =
      presentationA₀ u ≫ T'.mor₁.hom := by
  rw [← kernel.lift_ι T.mor₂.hom T.mor₁.hom
    (congrArg (fun t => t.hom) (comp_distTriang_mor_zero₁₂ T hT))]
  rw [Category.assoc, presentation_i₁_a₁]
  rw [← Category.assoc, presentation_p₀_z₁]
  rw [Category.assoc, kernel.lift_ι]

/-- Every ambient map of the initial kernels extends to a triangle morphism. -/
def triangleHomOfKernelMap : T ⟶ T' :=
  completeDistinguishedTriangleMorphism T T' hT hT'
    (ObjectProperty.homMk (presentationA₀ u))
    (ObjectProperty.homMk (presentationA₁ hT hT' u)) (by
      apply ObjectProperty.hom_ext
      exact presentation_square hT hT' u)

omit [HasBinaryBiproducts C] in
lemma triangleHomOfKernelMap_kernel :
    kernel.map T.mor₁.hom T'.mor₁.hom
      (triangleHomOfKernelMap hT hT' u).hom₁.hom
      (triangleHomOfKernelMap hT hT' u).hom₂.hom
      (congrArg (fun t => t.hom)
        (triangleHomOfKernelMap hT hT' u).comm₁) = u := by
  apply (cancel_mono (kernel.ι T'.mor₁.hom)).1
  rw [kernel.lift_ι]
  exact presentation_i₀_a₀ u

end

section ExtensionPresentation

open StableCategory.InjectiveComparison

variable {M : C} (E : Extension3 M (S.functor.obj M))
  (T : Triangle (Projectives (C := C)))
  (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
  (a₀ : E.I₀ ≅ T.obj₁.obj) (a₁ : E.I₁ ≅ T.obj₂.obj) (a₂ : E.I₂ ≅ T.obj₃.obj)
  (h₀ : E.d₀ ≫ a₁.hom = a₀.hom ≫ T.mor₁.hom)
  (h₁ : E.d₁ ≫ a₂.hom = a₁.hom ≫ T.mor₂.hom)
  (h₂ : E.p₂ ≫ S.functor.map (E.i₀ ≫ a₀.hom) = a₂.hom ≫ ambientBoundary S e T)

/-- An exact extension presenting a triangle has its initial object as the
actual kernel of the first differential. -/
def extensionKernelIso : M ≅ kernel T.mor₁.hom :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.isLimitOfIsLimitOfIff
      (StableCategory.ComplexInjectiveExtensions.initialKernel E) T.mor₁.hom a₀
      (fun {_} f => by rw [← cancel_mono a₁.hom, Category.assoc, h₀, zero_comp]))
    (limit.isLimit (parallelPair T.mor₁.hom 0))

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))] in
@[reassoc (attr := simp)]
theorem extensionKernelIso_hom_ι :
    (extensionKernelIso S E T a₀ a₁ h₀).hom ≫ kernel.ι T.mor₁.hom = E.i₀ ≫ a₀.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

omit [HasBinaryBiproducts C] in
@[simp] theorem triangleExtension_d₀ : (triangleExtension S e T hT).d₀ = T.mor₁.hom := by
  simp [triangleExtension, StableCategory.ComplexInjectiveExtensions.transportEndpoint,
    triangleExtensionLocal, Extension3.d₀]

omit [HasBinaryBiproducts C] in
@[simp] theorem triangleExtension_d₁ : (triangleExtension S e T hT).d₁ = T.mor₂.hom := by
  simp [triangleExtension, StableCategory.ComplexInjectiveExtensions.transportEndpoint,
    triangleExtensionLocal, Extension3.d₁]

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem triangleExtension_p₂_map_i₀ :
    (triangleExtension S e T hT).p₂ ≫
      S.functor.map (triangleExtension S e T hT).i₀ = ambientBoundary S e T := by
  dsimp [triangleExtension, StableCategory.ComplexInjectiveExtensions.transportEndpoint]
  rw [Category.assoc]
  change (triangleExtensionLocal S e T hT).p₂ ≫
    (triangleEndpointIso S T).hom ≫ S.functor.map (kernel.ι T.mor₁.hom) = _
  rw [triangleEndpointIso_hom_ι]
  simp [triangleExtensionLocal]

/-- An arbitrary exact extension presenting an original distinguished triangle
maps to its canonical kernel extension, with shift-compatible endpoints. -/
def extensionToTriangle : E.Hom (triangleExtension S e T hT) :=
  Extension3.Hom.ofSplicedMap (extensionKernelIso S E T a₀ a₁ h₀).hom a₀.hom a₁.hom a₂.hom
    (S.functor.map (extensionKernelIso S E T a₀ a₁ h₀).hom)
    (by simp [triangleExtension, StableCategory.ComplexInjectiveExtensions.transportEndpoint,
      triangleExtensionLocal])
    (by simpa only [triangleExtension_d₀] using h₀)
    (by simpa only [triangleExtension_d₁] using h₁)
    (by
      apply (cancel_mono (S.functor.map (kernel.ι T.mor₁.hom))).mp
      rw [Category.assoc, ← S.functor.map_comp, extensionKernelIso_hom_ι,
        h₂]
      rw [Category.assoc]
      exact (triangleExtension_p₂_map_i₀ S e T hT).symm ▸ rfl)

include a₂ h₁ h₂ in
/-- Canonical comparison is preserved by the actual presentation map. -/
theorem extensionToTriangle_stableComparison :
    (StableCategory.stableFunctor S.functor).map
        (Q.map (extensionKernelIso S E T a₀ a₁ h₀).hom) ≫
      (triangleExtension S e T hT).stableComparison.hom =
    E.stableComparison.hom ≫
      (cube StableCategory.Cosyzygy.functor).map
        (Q.map (extensionKernelIso S E T a₀ a₁ h₀).hom) := by
  simpa only [extensionToTriangle, Extension3.Hom.ofSplicedMap, StableCategory.stableFunctor_map] using
    (extensionToTriangle S e E T hT a₀ a₁ a₂ h₀ h₁ h₂).stableComparison_naturality

end ExtensionPresentation


/-- Stable comparisons extracted from distinguished triangles are natural for
an arbitrary ambient map between their initial kernels. -/
theorem triangleComparison_naturality_of_kernelMap
    {T T' : Triangle (Projectives (C := C))}
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (hT' : T' ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (u : kernel T.mor₁.hom ⟶ kernel T'.mor₁.hom) :
    (StableCategory.stableFunctor S.functor).map
        ((StableCategory.projectiveStableQuotient (C := C)).map u) ≫
      (triangleExtension S e T' hT').stableComparison.hom =
    (triangleExtension S e T hT).stableComparison.hom ≫
      (cube StableCategory.Cosyzygy.functor).map
        ((StableCategory.projectiveStableQuotient (C := C)).map u) := by
  have h := triangleExtension_stableComparison_naturality S e hT hT'
    (triangleHomOfKernelMap hT hT' u)
  rw [triangleExtensionMap_f₀, triangleHomOfKernelMap_kernel] at h
  exact h


/-- Naturality after replacing each literal presentation kernel by its
canonically isomorphic ambient object. -/
theorem recoveredDeltaComponent_naturality {M N : C} (f : M ⟶ N) :
    (StableCategory.stableFunctor S.functor).map
        ((StableCategory.projectiveStableQuotient (C := C)).map f) ≫
      (recoveredDeltaComponent S e N).hom =
    (recoveredDeltaComponent S e M).hom ≫
      (cube StableCategory.Cosyzygy.functor).map
        ((StableCategory.projectiveStableQuotient (C := C)).map f) := by
  let TM := chosenTriangle M
  let TN := chosenTriangle N
  let hM := chosenTriangle_distinguished M
  let hN := chosenTriangle_distinguished N
  let EM := triangleExtension S e TM hM
  let EN := triangleExtension S e TN hN
  let iM := chosenKernelIso M
  let iN := chosenKernelIso N
  let aM := (StableCategory.projectiveStableQuotient (C := C)).mapIso iM
  let aN := (StableCategory.projectiveStableQuotient (C := C)).mapIso iN
  let k : kernel TM.mor₁.hom ⟶ kernel TN.mor₁.hom :=
    iM.inv ≫ f ≫ iN.hom
  have hk := triangleComparison_naturality_of_kernelMap S e hM hN k
  have hleft :
      (StableCategory.projectiveStableQuotient (C := C)).map f ≫ aN.hom =
        aM.hom ≫ (StableCategory.projectiveStableQuotient (C := C)).map k := by
    dsimp [aM, aN, k, iM, iN]
    simp only [← Functor.map_comp]
    congr 1
    simp
  have hright :
      (StableCategory.projectiveStableQuotient (C := C)).map k ≫ aN.inv =
        aM.inv ≫ (StableCategory.projectiveStableQuotient (C := C)).map f := by
    dsimp [aM, aN, k, iM, iN]
    simp only [← Functor.map_comp]
    congr 1
    simp
  change
    (StableCategory.stableFunctor S.functor).map
          ((StableCategory.projectiveStableQuotient (C := C)).map f) ≫
        ((StableCategory.stableFunctor S.functor).mapIso aN ≪≫
          EN.stableComparison ≪≫
          (cube StableCategory.Cosyzygy.functor).mapIso aN.symm).hom =
      ((StableCategory.stableFunctor S.functor).mapIso aM ≪≫
          EM.stableComparison ≪≫
          (cube StableCategory.Cosyzygy.functor).mapIso aM.symm).hom ≫
        (cube StableCategory.Cosyzygy.functor).map
          ((StableCategory.projectiveStableQuotient (C := C)).map f)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.map_comp, hleft, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc
      ((StableCategory.stableFunctor S.functor).map
        ((StableCategory.projectiveStableQuotient (C := C)).map k))
      EN.stableComparison.hom
      ((cube StableCategory.Cosyzygy.functor).map aN.inv), hk]
  simp only [Category.assoc]
  rw [← Functor.map_comp, hright, Functor.map_comp]


/-- The recovered objectwise comparisons assemble to an actual natural
isomorphism on the projective stable quotient. -/
def recoveredDelta :
    StableCategory.stableFunctor S.functor ≅
      cube (StableCategory.Cosyzygy.functor (C := C)) :=
  NatIso.ofComponents (fun X => recoveredDeltaComponent S e X.as) (by
    rintro ⟨M⟩ ⟨N⟩ f
    obtain ⟨f, rfl⟩ :=
      (StableCategory.projectiveStableQuotient (C := C)).map_surjective f
    exact recoveredDeltaComponent_naturality S e f)


/-- Four iterates differ only by functor composition parentheses. -/
def cosyzygyFourthIso :
    StableCategory.Cosyzygy.functor ⋙ cube (StableCategory.Cosyzygy.functor (C := C)) ≅
      cube StableCategory.Cosyzygy.functor ⋙ StableCategory.Cosyzygy.functor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp)

/-- The signed Heller obstruction is a natural transformation before imposing
any anticommutation axiom. -/
def recoveredObstruction :
    StableCategory.stableFunctor S.functor ⋙ StableCategory.Cosyzygy.functor ⟶
      cube StableCategory.Cosyzygy.functor ⋙ StableCategory.Cosyzygy.functor :=
  Functor.whiskerRight (recoveredDelta S e).hom StableCategory.Cosyzygy.functor +
    (StableCategory.FrobeniusCommutation.sigma S).hom ≫
      Functor.whiskerLeft StableCategory.Cosyzygy.functor (recoveredDelta S e).hom ≫
        (cosyzygyFourthIso (C := C)).hom


theorem triangleComparison_eq_recovered
    (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C))))) :
    (triangleExtension S e T hT).stableComparison.hom =
      (recoveredDeltaComponent S e (kernel T.mor₁.hom)).hom := by
  let K := kernel T.mor₁.hom
  let TK := chosenTriangle K
  let hK := chosenTriangle_distinguished K
  let EK := triangleExtension S e TK hK
  let i := chosenKernelIso K
  let a := (StableCategory.projectiveStableQuotient (C := C)).mapIso i
  have h := triangleComparison_naturality_of_kernelMap S e hT hK i.hom
  change
    (StableCategory.stableFunctor S.functor).map a.hom ≫
        EK.stableComparison.hom =
      (triangleExtension S e T hT).stableComparison.hom ≫
        (cube StableCategory.Cosyzygy.functor).map a.hom at h
  change
    (triangleExtension S e T hT).stableComparison.hom =
      ((StableCategory.stableFunctor S.functor).mapIso a ≪≫
        EK.stableComparison ≪≫
        (cube StableCategory.Cosyzygy.functor).mapIso a.symm).hom
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, h]
  rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  have hid : (cube StableCategory.Cosyzygy.functor).map
      (𝟙 ((StableCategory.projectiveStableQuotient (C := C)).obj
        (kernel T.mor₁.hom))) = 𝟙 _ :=
    (cube StableCategory.Cosyzygy.functor).map_id _
  rw [hid, Category.comp_id]


/-- Every actual injective extension presenting an original distinguished
triangle has exactly the recovered stable comparison. -/
theorem extensionComparison_eq_recovered {M : C}
    (E : StableCategory.InjectiveComparison.Extension3 M (S.functor.obj M))
    (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C)))))
    (a₀ : E.I₀ ≅ T.obj₁.obj) (a₁ : E.I₁ ≅ T.obj₂.obj) (a₂ : E.I₂ ≅ T.obj₃.obj)
    (h₀ : E.d₀ ≫ a₁.hom = a₀.hom ≫ T.mor₁.hom)
    (h₁ : E.d₁ ≫ a₂.hom = a₁.hom ≫ T.mor₂.hom)
    (h₂ : E.p₂ ≫ S.functor.map (E.i₀ ≫ a₀.hom) = a₂.hom ≫ ambientBoundary S e T) :
    E.stableComparison.hom = (recoveredDelta S e).hom.app
      ((StableCategory.projectiveStableQuotient (C := C)).obj M) := by
  let k := extensionKernelIso S E T a₀ a₁ h₀
  have : IsIso ((cube StableCategory.Cosyzygy.functor).map
      ((StableCategory.projectiveStableQuotient (C := C)).map k.hom)) :=
    inferInstanceAs (IsIso (((cube StableCategory.Cosyzygy.functor).mapIso
      ((StableCategory.projectiveStableQuotient (C := C)).mapIso k)).hom))
  apply (cancel_mono ((cube StableCategory.Cosyzygy.functor).map
      ((StableCategory.projectiveStableQuotient (C := C)).map k.hom))).mp
  have hc := extensionToTriangle_stableComparison S e E T hT a₀ a₁ a₂ h₀ h₁ h₂
  rw [triangleComparison_eq_recovered S e T hT] at hc
  exact hc.symm.trans ((recoveredDelta S e).hom.naturality
    ((StableCategory.projectiveStableQuotient (C := C)).map k.hom))


/-- The actual cyclic rotation of an original triangle presents the actual
signed cyclic rotation of its three-row extension. -/
theorem rotatedExtensionComparison_eq_recovered
    (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C))))) :
    (Rotation.rotate S (triangleExtension S e T hT)).stableComparison.hom =
      (recoveredDelta S e).hom.app
        ((StableCategory.projectiveStableQuotient (C := C)).obj
          (triangleExtension S e T hT).Z₁) := by
  let E := triangleExtension S e T hT
  let a₂ : S.functor.obj T.obj₁.obj ≅ T.obj₁⟦(1 : ℤ)⟧.obj :=
    ((projectives (C := C)).ι.mapIso (e.app T.obj₁)).symm
  apply extensionComparison_eq_recovered S e (Rotation.rotate S E) T.rotate
    (rot_of_distTriang T hT) (Iso.refl _) (Iso.refl _) a₂
  · simpa only [E, Triangle.rotate, Triangle.mk, Iso.refl_hom, Category.comp_id, Category.id_comp,
      Rotation.rotate_d₀] using triangleExtension_d₁ S e T hT
  · have ht : (T.mor₃ ≫ e.hom.app T.obj₁) ≫ e.inv.app T.obj₁ = T.mor₃ := by simp
    have hc := congrArg (fun f => f ≫ a₂.hom) (triangleExtension_p₂_map_i₀ S e T hT)
    simpa only [Rotation.rotate_d₁, E, a₂, ambientBoundary,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.ι,
      inducedFunctor, Functor.mapIso, Iso.app_inv, Iso.symm_hom, Iso.refl_hom,
      Category.id_comp, Triangle.rotate, Triangle.mk] using
      hc.trans (congrArg (fun t => t.hom) ht)
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [Rotation.rotate_last_differential]
    rw [show E.d₀ = T.mor₁.hom from triangleExtension_d₀ S e T hT]
    have ht := congrArg (fun t => e.inv.app T.obj₁ ≫ t) (e.hom.naturality T.mor₁)
    simp only [← Category.assoc, e.inv_hom_id_app, Category.id_comp] at ht
    have hn := congrArg (fun t => -(t.hom)) ht.symm
    simpa only [a₂, ambientBoundary, ObjectProperty.FullSubcategory.comp_hom,
      projectiveEquivalence_map_hom, projectiveEquivalence, Equivalence.congrFullSubcategory,
      ObjectProperty.lift, ObjectProperty.homMk, ObjectProperty.ι, inducedFunctor,
      Functor.comp_obj, Functor.comp_map, Functor.mapIso, Iso.symm_hom,
      Triangle.rotate, Triangle.mk, Iso.app_inv, Iso.refl_hom, projective_neg_hom,
      Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using hn


open StableCategory StableCategory.InjectiveComparison
open StableCategory.FrobeniusTriangles StableCategory.FrobeniusCommutation

omit [HasShift (Projectives (C := C)) ℤ]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))] in
/-- Rotation plus naturality forces the Heller anticommutation sign. -/
lemma antiComm_of_rotation
    (δ : stableFunctor S.functor ≅ cube (Cosyzygy.functor (C := C)))
    {M : C} (E : Extension3 M (S.functor.obj M))
    (hE : E.stableComparison.hom =
      δ.hom.app ((projectiveStableQuotient (C := C)).obj M))
    (hR : (Rotation.rotate S E).stableComparison.hom =
      δ.hom.app ((projectiveStableQuotient (C := C)).obj E.Z₁)) :
    (show Cosyzygy.functor.obj
          ((stableFunctor S.functor).obj
            ((projectiveStableQuotient (C := C)).obj M)) ⟶
        Cosyzygy.functor.obj
          ((cube Cosyzygy.functor).obj
            ((projectiveStableQuotient (C := C)).obj M)) from
      Cosyzygy.functor.map
        (δ.hom.app ((projectiveStableQuotient (C := C)).obj M))) +
    (show Cosyzygy.functor.obj
          ((stableFunctor S.functor).obj
            ((projectiveStableQuotient (C := C)).obj M)) ⟶
        Cosyzygy.functor.obj
          ((cube Cosyzygy.functor).obj
            ((projectiveStableQuotient (C := C)).obj M)) from
      (sigmaComponent S M).hom ≫
        δ.hom.app (Cosyzygy.functor.obj
          ((projectiveStableQuotient (C := C)).obj M))) = 0 := by
  let c₀ := (connectingIso E.exact₀).hom
  let cr := (connectingIso (Rotation.rotate S E).exact₂).hom
  have hc₀ : c₀ = Q.map (connecting E.exact₀) :=
    connectingIso_hom E.exact₀
  have hcr : cr = Q.map (connecting (Rotation.rotate S E).exact₂) :=
    connectingIso_hom (Rotation.rotate S E).exact₂
  have : IsIso cr := by
    dsimp [cr]
    infer_instance
  apply (cancel_epi cr).1
  rw [Preadditive.comp_add, comp_zero]
  have hrot := Rotation.rotate_stableComparison_comp_connecting₀ S E
  have hnat := δ.hom.naturality c₀
  have hsigned := Rotation.signedMap_connecting_comp_sigma S E.exact₀
  rw [← hcr, ← hc₀] at hrot hsigned
  change cr ≫ (sigmaComponent S M).hom =
    -(stableFunctor S.functor).map c₀ at hsigned
  rw [← Category.assoc, hsigned, Preadditive.neg_comp]
  rw [hE, hR] at hrot
  rw [← hrot]
  rw [← hnat]
  simp


/-- The signed obstruction vanishes at every literal triangle kernel. -/
theorem recoveredObstruction_kernel_zero
    (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C))))) :
    (recoveredObstruction S e).app (Q.obj (kernel T.mor₁.hom)) = 0 := by
  have hc := antiComm_of_rotation S (recoveredDelta S e)
    (triangleExtension S e T hT)
    (triangleComparison_eq_recovered S e T hT)
    (rotatedExtensionComparison_eq_recovered S e T hT)
  simpa [recoveredObstruction, cosyzygyFourthIso] using hc

/-- Every ambient object is canonically isomorphic to its chosen triangle
kernel, so naturality transports vanishing of the obstruction to all objects. -/
theorem recoveredObstruction_zero (X : projectiveStableCategory C) :
    (recoveredObstruction S e).app X = 0 := by
  rcases X with ⟨M⟩
  let a := Q.mapIso (chosenKernelIso M)
  let G := cube (Cosyzygy.functor (C := C)) ⋙ Cosyzygy.functor
  have : IsIso (G.map a.hom) := inferInstanceAs (IsIso (G.mapIso a).hom)
  apply (cancel_mono (G.map a.hom)).mp
  rw [zero_comp]
  have hn := (recoveredObstruction S e).naturality a.hom
  have hz := recoveredObstruction_kernel_zero S e (chosenTriangle M)
    (chosenTriangle_distinguished M)
  change (recoveredObstruction S e).app
    (Q.obj (kernel (chosenDifferential M).hom)) = 0 at hz
  rw [hz, comp_zero] at hn
  exact hn.symm

/-- The original pretriangulation gives a genuine Heller parameter: its
natural isomorphism and anticommutation are both proved from TR1--TR3. -/
def recoveredParameter : StableHellerParameter S where
  delta := recoveredDelta S e
  commutes X := by
    simpa [recoveredObstruction, cosyzygyFourthIso] using recoveredObstruction_zero S e X


/-- Every original distinguished triangle is a distinguished triangle for the
recovered Heller parameter, using its actual three-row kernel extension. -/
theorem original_distinguished_deltaExact
    (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (Pretriangulated.distinguishedTriangles : Set (Triangle (Projectives (C := C))))) :
    T ∈ HellerClassification.distinguishedTriangles S (recoveredParameter S e) e := by
  let E := triangleExtension S e T hT
  refine ⟨kernel T.mor₁.hom, E, Iso.refl _, Iso.refl _, Iso.refl _, ?_, ?_, ?_, ?_⟩
  · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      triangleExtension_d₀ S e T hT
  · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      triangleExtension_d₁ S e T hT
  · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      triangleExtension_p₂_map_i₀ S e T hT
  · apply (StableCategory.HellerExactness.deltaExact_iff_stableComparison S
      (recoveredParameter S e) E).mpr
    exact triangleComparison_eq_recovered S e T hT

end CompatibleShift


section CoherentBaseline

variable (D : Type u) [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsIdempotentComplete D]

local instance coherentProjectiveShift :
    HasShift (Projectives (C := CoherentFunctors.Mod D)) ℤ :=
  YonedaHellerTransport.yonedaHasShift D

local instance coherentProjectiveShiftAdditive (n : ℤ) :
    (shiftFunctor (Projectives (C := CoherentFunctors.Mod D)) n).Additive :=
  YonedaHellerTransport.shifted_additive D n

local instance coherentOriginalPretriangulated :
    Pretriangulated (Projectives (C := CoherentFunctors.Mod D)) :=
  YonedaHellerTransport.originalPretriangulated D

/-- The baseline Heller parameter of the paper's actual coherent-functor
Frobenius category, recovered from the original structure through Yoneda. -/
def coherentBaselineParameter :
    StableCategory.FrobeniusCommutation.StableHellerParameter
      (CoherentFunctors.suspension (C := D)) :=
  recoveredParameter (CoherentFunctors.suspension (C := D))
    (YonedaHellerTransport.transportedShiftOneIso D)

/-- Original projective coherent-functor triangles have actual δ-exact rows
for the constructed baseline parameter. -/
theorem coherent_original_distinguished_deltaExact
    (T : Triangle (Projectives (C := CoherentFunctors.Mod D)))
    (hT : T ∈ (Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := CoherentFunctors.Mod D))))) :
    T ∈ HellerClassification.distinguishedTriangles
      (CoherentFunctors.suspension (C := D)) (coherentBaselineParameter D)
      (YonedaHellerTransport.transportedShiftOneIso D) :=
  original_distinguished_deltaExact _ _ T hT

end CoherentBaseline

end PretriangulatedV2.HellerRecovery
