import PretriangulatedV2.ProjectiveSerreDuality
import PretriangulatedV2.SerreFunctorConstruction
import PretriangulatedV2.StableLinear
import PretriangulatedV2.FrobeniusCommutation
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Serre pairings on the actual projective stable quotient

The raw pairing uses a projective cover of the first object and the kernel of
its image under the ambient Serre extension. Both projective ideals are proved
to lie in its radicals before the pairing is descended to the actual quotient.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Preadditive PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory.StableSerreDuality

section LinearDescent

variable {k : Type*} [Field k] {V W Z : Type*}
  [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
  [Module k V] [Module k W] [Module k Z]

/-- Descending a linear map through an actual surjective linear map. -/
def descendLinear (q : V →ₗ[k] W) (hq : Function.Surjective q)
    (f : V →ₗ[k] Z) (hf : LinearMap.ker q ≤ LinearMap.ker f) : W →ₗ[k] Z :=
  ((LinearMap.ker q).liftQ f hf).comp
    (q.quotKerEquivOfSurjective hq).symm.toLinearMap

@[simp]
lemma descendLinear_apply (q : V →ₗ[k] W) (hq : Function.Surjective q)
    (f : V →ₗ[k] Z) (hf : LinearMap.ker q ≤ LinearMap.ker f) (v : V) :
    descendLinear q hq f hf (q v) = f v := by
  change (LinearMap.ker q).liftQ f hf ((q.quotKerEquivOfSurjective hq).symm (q v)) = f v
  rw [← q.quotKerEquivOfSurjective_apply_mk hq, LinearEquiv.symm_apply_apply]
  rfl

end LinearDescent

variable {k : Type w} [Field k]
  {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [Linear k C] [FrobeniusAbelian C]
  (S : C ≌ C) [S.functor.Additive] [Functor.Linear k S.functor]
  (D : ProjectiveSerreDuality k C S.functor)

/-- A concrete representative of the prospective stable Serre image `Ω S X`. -/
abbrev syzygyObj (X : C) : C := kernel (S.functor.map (Projective.π X))

/-- A projective cover of that kernel obtained by applying the ambient
equivalence to the kernel cover of `X`. -/
def syzygyCover (X : C) :
    S.functor.obj (Projective.over (kernel (Projective.π X))) ⟶ syzygyObj S X :=
  S.functor.map (Projective.π (kernel (Projective.π X))) ≫
    (PreservesKernel.iso S.functor (Projective.π X)).hom

instance syzygyCover_epi (X : C) : Epi (syzygyCover S X) := by
  dsimp [syzygyCover]
  infer_instance

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
lemma syzygyCover_ι (X : C) :
    syzygyCover S X ≫ kernel.ι (S.functor.map (Projective.π X)) =
      S.functor.map (ProjectiveSerreDuality.coverDifferential X) := by
  simp [syzygyCover, PreservesKernel.iso_hom,
    ProjectiveSerreDuality.coverDifferential, Functor.map_comp]

/-- The ambient bilinear pairing before passing to either stable quotient. -/
def rawPairMap (X Y : C) :
    (Y ⟶ syzygyObj S X) →ₗ[k] Module.Dual k (X ⟶ Y) :=
  (CategoryTheory.Linear.leftComp k Y (Projective.π X)).dualMap.comp
    ((D.ambientDuality (Projective.over X) Y).toLinearMap.comp
      (CategoryTheory.Linear.rightComp k Y (kernel.ι (S.functor.map (Projective.π X)))))

omit [HasBinaryBiproducts C] [Functor.Linear k S.functor] in
@[simp]
lemma rawPairMap_apply {X Y : C} (b : Y ⟶ syzygyObj S X) (f : X ⟶ Y) :
    rawPairMap S D X Y b f =
      D.ambientDuality (Projective.over X) Y
        (b ≫ kernel.ι (S.functor.map (Projective.π X))) (Projective.π X ≫ f) := rfl

omit [HasBinaryBiproducts C] [Functor.Linear k S.functor] in
/-- Maps from `X` through projectives are annihilated by the raw pairing. -/
theorem rawPairMap_factorsThrough_left {X Y : C} (b : Y ⟶ syzygyObj S X)
    (f : X ⟶ Y) (hf : FactorsThrough (projectiveObjects : C → Prop) f) :
    rawPairMap S D X Y b f = 0 := by
  obtain ⟨P, hP, a, c, hac⟩ := hf
  have : Injective P := (FrobeniusAbelian.projective_iff_injective P).mp hP
  have : Projective (Injective.under X) :=
    (FrobeniusAbelian.projective_iff_injective _).mpr inferInstance
  let a' := Injective.factorThru a (Injective.ι X)
  have ha' : Injective.ι X ≫ a' = a := Injective.comp_factorThru _ _
  let r := Projective.π X ≫ Injective.ι X
  have hz : (b ≫ kernel.ι (S.functor.map (Projective.π X))) ≫ S.functor.map r = 0 := by
    calc
      _ = b ≫ (kernel.ι (S.functor.map (Projective.π X)) ≫
          S.functor.map (Projective.π X)) ≫ S.functor.map (Injective.ι X) := by
        simp [r, Functor.map_comp, Category.assoc]
      _ = 0 := by rw [kernel.condition]; simp
  rw [rawPairMap_apply, ← hac, ← ha']
  simp only [Category.assoc]
  rw [← Category.assoc (Projective.π X) (Injective.ι X)]
  change D.ambientDuality (Projective.over X) Y
    (b ≫ kernel.ι (S.functor.map (Projective.π X))) (r ≫ (a' ≫ c)) = 0
  rw [← D.ambientDuality_naturality_source, hz, map_zero]
  rfl

omit [HasBinaryBiproducts C] [Functor.Linear k S.functor] in
/-- Maps into the kernel through projectives are annihilated by the raw pairing. -/
theorem rawPairMap_factorsThrough_right {X Y : C} (b : Y ⟶ syzygyObj S X)
    (f : X ⟶ Y) (hb : FactorsThrough (projectiveObjects : C → Prop) b) :
    rawPairMap S D X Y b f = 0 := by
  obtain ⟨P, hP, a, c, hac⟩ := hb
  have : Projective P := hP
  let c' := Projective.factorThru c (syzygyCover S X)
  have hc' : c' ≫ syzygyCover S X = c := Projective.factorThru_comp _ _
  have hcι : c ≫ kernel.ι (S.functor.map (Projective.π X)) =
      c' ≫ S.functor.map (ProjectiveSerreDuality.coverDifferential X) := by
    rw [← hc', Category.assoc, syzygyCover_ι]
  rw [rawPairMap_apply, ← hac, Category.assoc, hcι, ← Category.assoc,
    D.ambientDuality_naturality_source]
  simp [← Category.assoc]

/-- A raw kernel morphism defines a linear functional on actual stable Hom. -/
def stableFunctional {X Y : C} (b : Y ⟶ syzygyObj S X) :
    Module.Dual k ((projectiveStableQuotient (C := C)).obj X ⟶
      (projectiveStableQuotient (C := C)).obj Y) :=
  descendLinear ((projectiveStableQuotient (C := C)).mapLinearMap k)
    (projectiveStableQuotient (C := C)).map_surjective (rawPairMap S D X Y b) (by
      intro f hf
      apply rawPairMap_factorsThrough_left S D b f
      exact (functor_map_eq_zero_iff (projectiveObjects : C → Prop) f).mp hf)

omit [Functor.Linear k S.functor] in
@[simp]
lemma stableFunctional_map {X Y : C} (b : Y ⟶ syzygyObj S X) (f : X ⟶ Y) :
    stableFunctional S D b ((projectiveStableQuotient (C := C)).map f) =
      rawPairMap S D X Y b f :=
  descendLinear_apply _ _ _ _ f

/-- The first descent remains linear in the kernel morphism. -/
def stableFunctionalMap (X Y : C) :
    (Y ⟶ syzygyObj S X) →ₗ[k]
      Module.Dual k ((projectiveStableQuotient (C := C)).obj X ⟶
        (projectiveStableQuotient (C := C)).obj Y) where
  toFun := stableFunctional S D
  map_add' a b := by
    ext f
    obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
    simp only [LinearMap.add_apply, stableFunctional_map, map_add]
  map_smul' r a := by
    ext f
    obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
    simp [LinearMap.smul_apply, stableFunctional_map]

/-- The bilinear pairing descended through both actual projective ideals. -/
def stablePairMap (X Y : C) :
    ((projectiveStableQuotient (C := C)).obj Y ⟶
        (projectiveStableQuotient (C := C)).obj (syzygyObj S X)) →ₗ[k]
      Module.Dual k ((projectiveStableQuotient (C := C)).obj X ⟶
        (projectiveStableQuotient (C := C)).obj Y) :=
  descendLinear ((projectiveStableQuotient (C := C)).mapLinearMap k)
    (projectiveStableQuotient (C := C)).map_surjective (stableFunctionalMap S D X Y) (by
      intro b hb
      ext f
      obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
      change stableFunctional S D b ((projectiveStableQuotient (C := C)).map f) = 0
      rw [stableFunctional_map]
      exact rawPairMap_factorsThrough_right S D b f
        ((functor_map_eq_zero_iff (projectiveObjects : C → Prop) b).mp hb))

omit [Functor.Linear k S.functor] in
@[simp]
lemma stablePairMap_map {X Y : C} (b : Y ⟶ syzygyObj S X) (f : X ⟶ Y) :
    stablePairMap S D X Y ((projectiveStableQuotient (C := C)).map b)
      ((projectiveStableQuotient (C := C)).map f) = rawPairMap S D X Y b f := by
  have h : stablePairMap S D X Y ((projectiveStableQuotient (C := C)).map b) =
      stableFunctional S D b := descendLinear_apply _ _ _ _ b
  rw [h]
  exact stableFunctional_map S D b f

omit [HasBinaryBiproducts C] [Functor.Linear k S.functor] in
/-- Nondegeneracy on the Serre side: the full raw radical is exactly the
ideal of maps through projectives. -/
theorem factorsThrough_of_rawPairMap_eq_zero {X Y : C} (b : Y ⟶ syzygyObj S X)
    (hb : rawPairMap S D X Y b = 0) :
    FactorsThrough (projectiveObjects : C → Prop) b := by
  let L := CategoryTheory.Linear.leftComp k Y (ProjectiveSerreDuality.coverDifferential X)
  let ν := D.ambientDuality (Projective.over X) Y
    (b ≫ kernel.ι (S.functor.map (Projective.π X)))
  have hν : ν ∈ (LinearMap.ker L).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro l hl
    have hd : ProjectiveSerreDuality.coverDifferential X ≫ l = 0 := hl
    have hk : kernel.ι (Projective.π X) ≫ l = 0 := by
      apply (cancel_epi (Projective.π (kernel (Projective.π X)))).mp
      simpa only [ProjectiveSerreDuality.coverDifferential, Category.assoc, comp_zero] using hd
    let f := Abelian.epiDesc (Projective.π X) l hk
    have hf : Projective.π X ≫ f = l := Abelian.comp_epiDesc _ _ _
    rw [← hf]
    change rawPairMap S D X Y b f = 0
    simpa using congrArg (fun ℓ : Module.Dual k (X ⟶ Y) ↦ ℓ f) hb
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker L] at hν
  obtain ⟨μ, hμ⟩ := hν
  let c := (D.ambientDuality (Projective.over (kernel (Projective.π X))) Y).symm μ
  have hc : D.ambientDuality (Projective.over (kernel (Projective.π X))) Y c = μ :=
    (D.ambientDuality _ _).apply_symm_apply μ
  have ha : c ≫ S.functor.map (ProjectiveSerreDuality.coverDifferential X) =
      b ≫ kernel.ι (S.functor.map (Projective.π X)) := by
    apply (D.ambientDuality (Projective.over X) Y).injective
    ext g
    rw [D.ambientDuality_naturality_source, hc]
    exact congrArg (fun ℓ : Module.Dual k (Projective.over X ⟶ Y) ↦ ℓ g) hμ
  refine ⟨S.functor.obj (Projective.over (kernel (Projective.π X))), inferInstance,
    c, syzygyCover S X, ?_⟩
  apply (cancel_mono (kernel.ι (S.functor.map (Projective.π X)))).mp
  rw [Category.assoc, syzygyCover_ι]
  exact ha

omit [Functor.Linear k S.functor] in
/-- The descended pairing is injective on the actual stable Serre Hom. -/
theorem stablePairMap_injective (X Y : C) :
    Function.Injective (stablePairMap S D X Y) := by
  intro a b hab
  apply sub_eq_zero.mp
  obtain ⟨c, hc⟩ := (projectiveStableQuotient (C := C)).map_surjective (a - b)
  rw [← hc, functor_map_eq_zero_iff]
  apply factorsThrough_of_rawPairMap_eq_zero S D c
  ext f
  rw [← stablePairMap_map, hc, map_sub, hab, sub_self]
  rfl

omit [Functor.Linear k S.functor] in
/-- Every stable linear functional arises from a genuine kernel morphism;
linear dual extension and the projective-injective embedding prove this. -/
theorem stablePairMap_surjective (X Y : C) :
    Function.Surjective (stablePairMap S D X Y) := by
  intro ℓ
  let μ := ℓ.comp ((projectiveStableQuotient (C := C)).mapLinearMap k)
  let j := CategoryTheory.Linear.leftComp k Y (Projective.π X)
  have hj : Function.Injective j := by
    intro f g h
    exact (cancel_epi (Projective.π X)).mp h
  obtain ⟨ν, hν⟩ := LinearMap.dualMap_surjective_of_injective hj μ
  let a := (D.ambientDuality (Projective.over X) Y).symm ν
  have ha : D.ambientDuality (Projective.over X) Y a = ν :=
    (D.ambientDuality _ _).apply_symm_apply ν
  have : Projective (Injective.under X) :=
    (FrobeniusAbelian.projective_iff_injective _).mpr inferInstance
  let r := Projective.π X ≫ Injective.ι X
  have hr : a ≫ S.functor.map r = 0 := by
    apply (D.ambientDuality (Injective.under X) Y).injective
    ext g
    rw [D.ambientDuality_naturality_source, ha]
    have h := congrArg (fun φ : Module.Dual k (X ⟶ Y) ↦ φ (Injective.ι X ≫ g)) hν
    change ν (Projective.π X ≫ (Injective.ι X ≫ g)) = μ (Injective.ι X ≫ g) at h
    rw [← Category.assoc] at h
    simp only [map_zero, LinearMap.zero_apply]
    change ν (r ≫ g) = 0
    rw [h]
    change ℓ ((projectiveStableQuotient (C := C)).map (Injective.ι X ≫ g)) = 0
    have hz : (projectiveStableQuotient (C := C)).map (Injective.ι X ≫ g) = 0 := by
      rw [functor_map_eq_zero_iff]
      exact ⟨Injective.under X, inferInstance, Injective.ι X, g, rfl⟩
    simp [hz]
  have hπ : a ≫ S.functor.map (Projective.π X) = 0 := by
    apply (cancel_mono (S.functor.map (Injective.ι X))).mp
    simpa only [r, Functor.map_comp, Category.assoc, zero_comp] using hr
  let b := kernel.lift (S.functor.map (Projective.π X)) a hπ
  have hb : b ≫ kernel.ι (S.functor.map (Projective.π X)) = a := kernel.lift_ι _ _ _
  refine ⟨(projectiveStableQuotient (C := C)).map b, ?_⟩
  ext f
  obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
  rw [stablePairMap_map, rawPairMap_apply, hb, ha]
  exact congrArg (fun φ : Module.Dual k (X ⟶ Y) ↦ φ f) hν

/-- A genuine linear Serre duality on the actual stable Hom spaces, at the
concrete projective-kernel representative of `Ω S X`. -/
def stableDuality (X Y : C) :
    ((projectiveStableQuotient (C := C)).obj Y ⟶
        (projectiveStableQuotient (C := C)).obj (syzygyObj S X)) ≃ₗ[k]
      Module.Dual k ((projectiveStableQuotient (C := C)).obj X ⟶
        (projectiveStableQuotient (C := C)).obj Y) :=
  LinearEquiv.ofBijective (stablePairMap S D X Y)
    ⟨stablePairMap_injective S D X Y, stablePairMap_surjective S D X Y⟩

omit [Functor.Linear k S.functor] in
@[simp]
lemma stableDuality_apply {X Y : C} (b : Y ⟶ syzygyObj S X) (f : X ⟶ Y) :
    stableDuality S D X Y ((projectiveStableQuotient (C := C)).map b)
      ((projectiveStableQuotient (C := C)).map f) = rawPairMap S D X Y b f :=
  stablePairMap_map S D b f

omit [Functor.Linear k S.functor] in
/-- Naturality in the second object holds on actual stable morphisms. -/
lemma stableDuality_naturality_target (X Y Y' : C)
    (f : (projectiveStableQuotient (C := C)).obj Y ⟶
      (projectiveStableQuotient (C := C)).obj Y')
    (g : (projectiveStableQuotient (C := C)).obj X ⟶
      (projectiveStableQuotient (C := C)).obj Y)
    (a : (projectiveStableQuotient (C := C)).obj Y' ⟶
      (projectiveStableQuotient (C := C)).obj (syzygyObj S X)) :
    stableDuality S D X Y (f ≫ a) g = stableDuality S D X Y' a (g ≫ f) := by
  obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
  obtain ⟨g, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective g
  obtain ⟨a, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective a
  rw [← Functor.map_comp, ← Functor.map_comp, stableDuality_apply, stableDuality_apply,
    rawPairMap_apply, rawPairMap_apply]
  simpa only [Category.assoc] using D.ambientDuality_naturality_target f (Projective.π X ≫ g)
    (a ≫ kernel.ι (S.functor.map (Projective.π X)))

/-- The concrete kernels genuinely represent stable dual Hom. -/
def rightPairing : SerreFunctorConstruction.RightPairing k (projectiveStableCategory C) where
  obj X := (projectiveStableQuotient (C := C)).obj (syzygyObj S X.as)
  duality X Y := stableDuality S D X.as Y.as
  naturality_target := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Y'⟩ f g a
    exact stableDuality_naturality_target S D X Y Y' f g a

/-- The chosen lift between the projective covers. -/
def projectiveLift {X Y : C} (f : X ⟶ Y) : Projective.over X ⟶ Projective.over Y :=
  Projective.factorThru (Projective.π X ≫ f) (Projective.π Y)

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
lemma projectiveLift_π {X Y : C} (f : X ⟶ Y) :
    projectiveLift f ≫ Projective.π Y = Projective.π X ≫ f := Projective.factorThru_comp _ _

/-- The map on concrete projective-kernel representatives. -/
def syzygyMap {X Y : C} (f : X ⟶ Y) : syzygyObj S X ⟶ syzygyObj S Y :=
  kernel.map (S.functor.map (Projective.π X)) (S.functor.map (Projective.π Y))
    (S.functor.map (projectiveLift f)) (S.functor.map f) (by
      simp only [← S.functor.map_comp, projectiveLift_π])

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
lemma syzygyMap_ι {X Y : C} (f : X ⟶ Y) :
    syzygyMap S f ≫ kernel.ι (S.functor.map (Projective.π Y)) =
      kernel.ι (S.functor.map (Projective.π X)) ≫ S.functor.map (projectiveLift f) :=
  by simp [syzygyMap, kernel.map]

omit [HasBinaryBiproducts C] [Functor.Linear k S.functor] in
/-- Source naturality of the raw pairing for actual projective-kernel maps. -/
lemma rawPairMap_naturality_source {X X' Y : C} (f : X' ⟶ X) (g : X ⟶ Y)
    (a : Y ⟶ syzygyObj S X') :
    rawPairMap S D X Y (a ≫ syzygyMap S f) g = rawPairMap S D X' Y a (f ≫ g) := by
  rw [rawPairMap_apply, Category.assoc, syzygyMap_ι, ← Category.assoc,
    D.ambientDuality_naturality_source, rawPairMap_apply]
  simp [← Category.assoc]

/-- Canonical identification of an epimorphism's target with its coimage. -/
def epiCokernelIso {A B : C} (f : A ⟶ B) [Epi f] : cokernel (kernel.ι f) ≅ B :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι f))
    (Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι f) (kernel.condition f)) (kernelIsKernel f))

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[reassoc (attr := simp)]
lemma π_epiCokernelIso_hom {A B : C} (f : A ⟶ B) [Epi f] :
    cokernel.π (kernel.ι f) ≫ (epiCokernelIso f).hom = f := by
  exact (cokernelIsCokernel (kernel.ι f)).comp_coconePointUniqueUpToIso_hom
    (Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι f) (kernel.condition f)) (kernelIsKernel f))
    WalkingParallelPair.one

/-- The cosyzygy of the concrete kernel is the Serre-extension image of `X`.
This is constructed using the genuine ambient projective presentation. -/
def cosyzygySyzygyIso (X : C) :
    (Cosyzygy.functor (C := C)).obj
        ((projectiveStableQuotient (C := C)).obj (syzygyObj S X)) ≅
      (projectiveStableQuotient (C := C)).obj (S.functor.obj X) := by
  have : Injective (S.functor.obj (Projective.over X)) :=
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  let f := S.functor.map (Projective.π X)
  exact Cosyzygy.stableCokernelIso (Injective.ι (syzygyObj S X))
    (kernel.ι f) ≪≫ (projectiveStableQuotient (C := C)).mapIso (epiCokernelIso f)

omit [Functor.Linear k S.functor] in
/-- Essential surjectivity of the representing kernels follows from the
already proved cosyzygy equivalence and the ambient equivalence. -/
theorem rightPairing_obj_essSurj :
    ∀ Y : projectiveStableCategory C, ∃ X : projectiveStableCategory C,
      Nonempty ((rightPairing S D).obj X ≅ Y) := by
  rintro ⟨Y⟩
  let X := S.inverse.obj (Cosyzygy.obj Y)
  let e : (Cosyzygy.functor (C := C)).obj
        ((projectiveStableQuotient (C := C)).obj (syzygyObj S X)) ≅
      (Cosyzygy.functor (C := C)).obj ((projectiveStableQuotient (C := C)).obj Y) :=
    cosyzygySyzygyIso S X ≪≫
      (projectiveStableQuotient (C := C)).mapIso (S.counitIso.app (Cosyzygy.obj Y))
  exact ⟨(projectiveStableQuotient (C := C)).obj X,
    ⟨(Cosyzygy.functor (C := C)).preimageIso e⟩⟩

section HomFinite

variable [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Genuine Serre duality on the actual projective stable category, obtained
from the original projective-projective Serre pairing. -/
def serreDuality : SerreDuality k (projectiveStableCategory C) :=
  (rightPairing S D).serreDuality (rightPairing_obj_essSurj S D)

omit [Functor.Linear k S.functor] in
@[simp]
lemma serreDuality_obj (X : C) :
    (serreDuality S D).equivalence.functor.obj ((projectiveStableQuotient (C := C)).obj X) =
      (projectiveStableQuotient (C := C)).obj (syzygyObj S X) := rfl

omit [Functor.Linear k S.functor] in
/-- The functor forced by Serre representation has the actual kernel map. -/
lemma serreDuality_map {X Y : C} (f : X ⟶ Y) :
    (serreDuality S D).equivalence.functor.map ((projectiveStableQuotient (C := C)).map f) =
      (projectiveStableQuotient (C := C)).map (syzygyMap S f) := by
  apply (stableDuality S D Y (syzygyObj S X)).injective
  ext g
  obtain ⟨g, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective g
  change (rightPairing S D).duality _ _
    ((rightPairing S D).mapHom ((projectiveStableQuotient (C := C)).map f))
      ((projectiveStableQuotient (C := C)).map g) = _
  rw [SerreFunctorConstruction.RightPairing.mapHom_pair]
  change stableDuality S D X (syzygyObj S X) (𝟙 _)
      ((projectiveStableQuotient (C := C)).map f ≫
        (projectiveStableQuotient (C := C)).map g) = _
  rw [← (projectiveStableQuotient (C := C)).map_id (syzygyObj S X),
    ← Functor.map_comp, stableDuality_apply, stableDuality_apply]
  simpa only [Category.id_comp] using
    (rawPairMap_naturality_source S D f g (𝟙 (syzygyObj S X))).symm

lemma cosyzygySyzygyIso_hom (X : C) :
    letI : Injective (S.functor.obj (Projective.over X)) :=
      (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
    (cosyzygySyzygyIso S X).hom =
      (projectiveStableQuotient (C := C)).map
        (Cosyzygy.comparison (Injective.ι (syzygyObj S X))
          (kernel.ι (S.functor.map (Projective.π X)))) ≫
        (projectiveStableQuotient (C := C)).map
          (epiCokernelIso (S.functor.map (Projective.π X))).hom := rfl

/-- The concrete cosyzygy/kernel comparison is natural for the maps forced
by the Serre pairing. -/
lemma cosyzygySyzygyIso_naturality {X Y : C} (f : X ⟶ Y) :
    (projectiveStableQuotient (C := C)).map (Cosyzygy.map (syzygyMap S f)) ≫
        (cosyzygySyzygyIso S Y).hom =
      (cosyzygySyzygyIso S X).hom ≫
        (projectiveStableQuotient (C := C)).map (S.functor.map f) := by
  have : Injective (S.functor.obj (Projective.over X)) :=
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  have : Injective (S.functor.obj (Projective.over Y)) :=
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  let jX := kernel.ι (S.functor.map (Projective.π X))
  let jY := kernel.ι (S.functor.map (Projective.π Y))
  have hb : jX ≫ S.functor.map (projectiveLift f) = syzygyMap S f ≫ jY :=
    (syzygyMap_ι S f).symm
  have hc := Cosyzygy.comparison_naturality
    (Injective.ι (syzygyObj S X)) (Injective.ι (syzygyObj S Y)) jX jY
    (syzygyMap S f) (Cosyzygy.extension (syzygyMap S f)) (S.functor.map (projectiveLift f))
    (Cosyzygy.ι_extension _) hb
  have he : cokernel.map jX jY (syzygyMap S f) (S.functor.map (projectiveLift f)) hb ≫
        (epiCokernelIso (S.functor.map (Projective.π Y))).hom =
      (epiCokernelIso (S.functor.map (Projective.π X))).hom ≫ S.functor.map f := by
    apply (cancel_epi (cokernel.π jX)).mp
    simp only [Category.assoc, cokernel.π_desc_assoc]
    change S.functor.map (projectiveLift f) ≫
        (cokernel.π jY ≫ (epiCokernelIso (S.functor.map (Projective.π Y))).hom) =
      cokernel.π jX ≫ (epiCokernelIso (S.functor.map (Projective.π X))).hom ≫ S.functor.map f
    rw [π_epiCokernelIso_hom, ← Category.assoc, π_epiCokernelIso_hom]
    simp only [← S.functor.map_comp, projectiveLift_π]
  have h := hc =≫ (projectiveStableQuotient (C := C)).map
    (epiCokernelIso (S.functor.map (Projective.π Y))).hom
  simp only [Category.assoc] at h
  rw [← (projectiveStableQuotient (C := C)).map_comp
      (cokernel.map jX jY (syzygyMap S f) (S.functor.map (projectiveLift f)) hb)
      (epiCokernelIso (S.functor.map (Projective.π Y))).hom,
    he, Functor.map_comp] at h
  simpa only [cosyzygySyzygyIso_hom, Cosyzygy.map, Category.assoc] using h

/-- The naturally constructed stable Serre functor becomes the ambient
Serre extension after one cosyzygy. -/
def serreCompCosyzygyIso :
    (serreDuality S D).equivalence.functor ⋙ Cosyzygy.functor ≅ stableFunctor S.functor :=
  NatIso.ofComponents (fun X ↦ cosyzygySyzygyIso S X.as) (by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
    simp only [Functor.comp_map, serreDuality_map, Cosyzygy.functor_map, stableFunctor_map]
    exact cosyzygySyzygyIso_naturality S f)

/-- The genuine natural identification of stable Serre duality with `Ω S`. -/
def serreIsoOmega :
    (serreDuality S D).equivalence.functor ≅
      stableFunctor S.functor ⋙ (Cosyzygy.equivalence (C := C)).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Cosyzygy.equivalence (C := C)).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (serreCompCosyzygyIso S D) _

end HomFinite

end PretriangulatedV2.StableCategory.StableSerreDuality
