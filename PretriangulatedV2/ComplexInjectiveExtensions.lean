import PretriangulatedV2.HellerExactness
import PretriangulatedV2.PeriodicComplexes
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
The actual three-step injective extension extracted from an acyclic cochain
complex. Its objects are mathlib's actual cycles, with their kernel universal
properties; no abstract comparison equation is supplied as input.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PretriangulatedV2.StableCategory.InjectiveComparison

namespace PretriangulatedV2.StableCategory.ComplexInjectiveExtensions

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- The exact row of actual consecutive cocycles. -/
def cycleSequence (P : CochainComplex C ℤ) (n : ℤ) : ShortComplex C :=
  ShortComplex.mk (P.iCycles n) (P.toCycles n (n + 1)) (by
    apply (cancel_mono (P.iCycles (n + 1))).mp
    simp)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem cycleSequence_shortExact (P : CochainComplex C ℤ) (n : ℤ)
    (hP : P.ExactAt (n + 1)) : (cycleSequence P n).ShortExact := by
  have hex : (P.sc' n (n + 1) (n + 2)).Exact :=
    (P.exactAt_iff' n (n + 1) (n + 2) (by
      apply (ComplexShape.up ℤ).prev_eq'
      change n + 1 = n + 1
      rfl) (by
      apply (ComplexShape.up ℤ).next_eq'
      change (n + 1) + 1 = n + 2
      omega)).mp hP
  let e := P.cyclesIsoSc' n (n + 1) (n + 2) (by
    apply (ComplexShape.up ℤ).prev_eq'
    change n + 1 = n + 1
    rfl) (by
    apply (ComplexShape.up ℤ).next_eq'
    change (n + 1) + 1 = n + 2
    omega)
  have : Epi (P.sc' n (n + 1) (n + 2)).toCycles := hex.epi_toCycles
  have hep : Epi (P.toCycles n (n + 1) ≫ e.hom) := by
    rw [HomologicalComplex.toCycles_cyclesIsoSc'_hom]
    infer_instance
  have : Epi ((P.toCycles n (n + 1) ≫ e.hom) ≫ e.inv) := inferInstance
  have : Epi (P.toCycles n (n + 1)) := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ShortComplex.exact_of_f_is_kernel
    apply KernelFork.isLimitOfIsLimitOfIff'
      (P.cyclesIsKernel n (n + 1) (by
        apply (ComplexShape.up ℤ).next_eq'
        change n + 1 = n + 1
        rfl))
    intro W f
    change f ≫ P.d n (n + 1) = 0 ↔ f ≫ P.toCycles n (n + 1) = 0
    rw [← cancel_mono (P.iCycles (n + 1)), Category.assoc, toCycles_i, zero_comp]
  · dsimp [cycleSequence]; infer_instance
  · dsimp [cycleSequence]; infer_instance

/-- The actual truncation `0 → Z⁰P → P⁰ → P¹ → P² → Z³P → 0`,
split into its three actual short exact rows. -/
def extensionLocal (P : CochainComplex C ℤ)
    (h₁ : P.ExactAt 1) (h₂ : P.ExactAt 2) (h₃ : P.ExactAt 3)
    (hproj : ∀ n : ℤ, Projective (P.X n)) : Extension3 (P.cycles 0) (P.cycles 3) where
  Z₁ := P.cycles 1
  Z₂ := P.cycles 2
  I₀ := P.X 0
  I₁ := P.X 1
  I₂ := P.X 2
  i₀ := P.iCycles 0
  p₀ := P.toCycles 0 1
  i₁ := P.iCycles 1
  p₁ := P.toCycles 1 2
  i₂ := P.iCycles 2
  p₂ := P.toCycles 2 3
  zero₀ := (cycleSequence P 0).zero
  zero₁ := (cycleSequence P 1).zero
  zero₂ := (cycleSequence P 2).zero
  exact₀ := cycleSequence_shortExact P 0 h₁
  exact₁ := cycleSequence_shortExact P 1 h₂
  exact₂ := cycleSequence_shortExact P 2 h₃
  injective₀ := (FrobeniusAbelian.projective_iff_injective _).mp (hproj 0)
  injective₁ := (FrobeniusAbelian.projective_iff_injective _).mp (hproj 1)
  injective₂ := (FrobeniusAbelian.projective_iff_injective _).mp (hproj 2)

/-- The extension associated to an actual acyclic complex. -/
def extension (P : CochainComplex C ℤ) (hP : P.Acyclic)
    (hproj : ∀ n : ℤ, Projective (P.X n)) : Extension3 (P.cycles 0) (P.cycles 3) :=
  extensionLocal P (hP 1) (hP 2) (hP 3) hproj

omit [HasBinaryBiproducts C] in
@[simp]
theorem extension_d₀ (P : CochainComplex C ℤ) (hP : P.Acyclic)
    (hproj : ∀ n : ℤ, Projective (P.X n)) :
    (extension P hP hproj).d₀ = P.d 0 1 := by
  exact P.toCycles_i 0 1

omit [HasBinaryBiproducts C] in
@[simp]
theorem extension_d₁ (P : CochainComplex C ℤ) (hP : P.Acyclic)
    (hproj : ∀ n : ℤ, Projective (P.X n)) :
    (extension P hP hproj).d₁ = P.d 1 2 := by
  exact P.toCycles_i 1 2

/-- Every actual cochain map induces the needed actual morphism of exact rows. -/
def extensionMapLocal {P R : CochainComplex C ℤ}
    (hP₁ : P.ExactAt 1) (hP₂ : P.ExactAt 2) (hP₃ : P.ExactAt 3)
    (hR₁ : R.ExactAt 1) (hR₂ : R.ExactAt 2) (hR₃ : R.ExactAt 3)
    (hprojP : ∀ n : ℤ, Projective (P.X n))
    (hprojR : ∀ n : ℤ, Projective (R.X n)) (f : P ⟶ R) :
    (extensionLocal P hP₁ hP₂ hP₃ hprojP).Hom (extensionLocal R hR₁ hR₂ hR₃ hprojR) where
  f₀ := cyclesMap f 0
  f₁ := cyclesMap f 1
  f₂ := cyclesMap f 2
  f₃ := cyclesMap f 3
  a₀ := f.f 0
  a₁ := f.f 1
  a₂ := f.f 2
  comm_i₀ := (cyclesMap_i f 0).symm
  comm_p₀ := by
    apply (cancel_mono (R.iCycles 1)).mp
    simp only [extensionLocal, Category.assoc, cyclesMap_i, toCycles_i_assoc, toCycles_i]
    exact (f.comm 0 1).symm
  comm_i₁ := (cyclesMap_i f 1).symm
  comm_p₁ := by
    apply (cancel_mono (R.iCycles 2)).mp
    simp only [extensionLocal, Category.assoc, cyclesMap_i, toCycles_i_assoc, toCycles_i]
    exact (f.comm 1 2).symm
  comm_i₂ := (cyclesMap_i f 2).symm
  comm_p₂ := by
    apply (cancel_mono (R.iCycles 3)).mp
    simp only [extensionLocal, Category.assoc, cyclesMap_i, toCycles_i_assoc, toCycles_i]
    exact (f.comm 2 3).symm

def extensionMap {P R : CochainComplex C ℤ} (hP : P.Acyclic) (hR : R.Acyclic)
    (hprojP : ∀ n : ℤ, Projective (P.X n))
    (hprojR : ∀ n : ℤ, Projective (R.X n)) (f : P ⟶ R) :
    (extension P hP hprojP).Hom (extension R hR hprojR) :=
  extensionMapLocal (hP 1) (hP 2) (hP 3) (hR 1) (hR 2) (hR 3) hprojP hprojR f

/-- Transport of the genuine last short exact row along an endpoint isomorphism. -/
def transportEndpoint {M N N' : C} (E : Extension3 M N) (e : N ≅ N') :
    Extension3 M N' where
  Z₁ := E.Z₁
  Z₂ := E.Z₂
  I₀ := E.I₀
  I₁ := E.I₁
  I₂ := E.I₂
  i₀ := E.i₀
  p₀ := E.p₀
  i₁ := E.i₁
  p₁ := E.p₁
  i₂ := E.i₂
  p₂ := E.p₂ ≫ e.hom
  zero₀ := E.zero₀
  zero₁ := E.zero₁
  zero₂ := by rw [← Category.assoc, E.zero₂, zero_comp]
  exact₀ := E.exact₀
  exact₁ := E.exact₁
  exact₂ := ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := E.row₂)
      (S₂ := ShortComplex.mk E.i₂ (E.p₂ ≫ e.hom) (by
        rw [← Category.assoc, E.zero₂, zero_comp]))
      (Iso.refl _) (Iso.refl _) e (by simp) (by simp)) E.exact₂
  injective₀ := E.injective₀
  injective₁ := E.injective₁
  injective₂ := E.injective₂

/-- Endpoint transport of the actual three-row cochain comparison. -/
def transportEndpointMap {M N M' N' K K' : C}
    {E : Extension3 M N} {E' : Extension3 M' N'} (φ : E.Hom E')
    (e : N ≅ K) (e' : N' ≅ K') :
    (transportEndpoint E e).Hom (transportEndpoint E' e') where
  f₀ := φ.f₀
  f₁ := φ.f₁
  f₂ := φ.f₂
  f₃ := e.inv ≫ φ.f₃ ≫ e'.hom
  a₀ := φ.a₀
  a₁ := φ.a₁
  a₂ := φ.a₂
  comm_i₀ := φ.comm_i₀
  comm_p₀ := φ.comm_p₀
  comm_i₁ := φ.comm_i₁
  comm_p₁ := φ.comm_p₁
  comm_i₂ := φ.comm_i₂
  comm_p₂ := by
    change (E.p₂ ≫ e.hom) ≫ (e.inv ≫ φ.f₃ ≫ e'.hom) =
      φ.a₂ ≫ E'.p₂ ≫ e'.hom
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc E.p₂ φ.f₃, φ.comm_p₂, Category.assoc]

section Periodic

open PeriodicComplexes

variable (S : C ≌ C) [S.functor.Additive]

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
/-- Exactness survives splicing an epimorphism on the left and a monomorphism
on the right of an actual short exact sequence. -/
theorem splice_exact {T : ShortComplex C} (hT : T.ShortExact)
    {A B : C} (a : A ⟶ T.X₁) (b : T.X₃ ⟶ B) [Epi a] [Mono b] :
    (ShortComplex.mk (a ≫ T.f) (T.g ≫ b) (by
      simp only [Category.assoc, ← Category.assoc T.f T.g b, T.zero, zero_comp,
        comp_zero])).Exact := by
  let U : ShortComplex C := ShortComplex.mk T.f (T.g ≫ b) (by simp [← Category.assoc])
  let V : ShortComplex C := ShortComplex.mk (a ≫ T.f) (T.g ≫ b) (by
    simp only [Category.assoc, ← Category.assoc T.f T.g b, T.zero, zero_comp, comp_zero])
  let φ : T ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := b
      comm₁₂ := by simp [U]
      comm₂₃ := by simp [U] }
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  have hU : U.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hT.exact
  let ψ : V ⟶ U :=
    { τ₁ := a
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [V, U]
      comm₂₃ := by simp [V, U] }
  have : Epi ψ.τ₁ := by dsimp [ψ]; infer_instance
  have : IsIso ψ.τ₂ := by dsimp [ψ]; infer_instance
  have : Mono ψ.τ₃ := by dsimp [ψ]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hU

/-- The first injection of the spliced row is its actual initial kernel. -/
def initialKernel {M N : C} (E : Extension3 M N) :
    IsLimit (KernelFork.ofι E.i₀ (show E.i₀ ≫ E.d₀ = 0 from by
      simp only [Extension3.d₀, ← Category.assoc, E.zero₀, zero_comp])) :=
  KernelFork.isLimitOfIsLimitOfIff' E.exact₀.fIsKernel E.d₀ (fun {_} f => by
    rw [← cancel_mono E.i₁, Category.assoc, zero_comp])

/-- The arbitrary initial witness object of a δ-exact truncation is actually
isomorphic to its zeroth cycles. -/
def initialCycleIso (P : SComplex S) {M : C}
    (E : Extension3 M (S.functor.obj M)) (e₀ : E.I₀ ≅ P.complex.X 0)
    (e₁ : E.I₁ ≅ P.complex.X 1)
    (h₀ : E.d₀ ≫ e₁.hom = e₀.hom ≫ P.complex.d 0 1) : M ≅ P.complex.cycles 0 :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.isLimitOfIsLimitOfIff (initialKernel E) (P.complex.d 0 1) e₀ (fun {_} f => by
      rw [← cancel_mono e₁.hom, Category.assoc, h₀, zero_comp]))
    (P.complex.cyclesIsKernel 0 1 (by simp))

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive] in
theorem initialCycleIso_hom_iCycles (P : SComplex S) {M : C}
    (E : Extension3 M (S.functor.obj M)) (e₀ : E.I₀ ≅ P.complex.X 0)
    (e₁ : E.I₁ ≅ P.complex.X 1)
    (h₀ : E.d₀ ≫ e₁.hom = e₀.hom ≫ P.complex.d 0 1) :
    (initialCycleIso S P E e₀ e₁ h₀).hom ≫ P.complex.iCycles 0 = E.i₀ ≫ e₀.hom := by
  dsimp only [initialCycleIso]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The actual periodic-complex truncation, whose endpoint is `S Z⁰(P)` via
the proved kernel isomorphism supplied by the actual periodicity. -/
def periodicExtension (P : SComplex S)
    (h₁ : P.complex.ExactAt 1) (h₂ : P.complex.ExactAt 2) (h₃ : P.complex.ExactAt 3) :
    Extension3 (P.complex.cycles 0) (S.functor.obj (P.complex.cycles 0)) :=
  transportEndpoint (extensionLocal P.complex h₁ h₂ h₃ P.projective)
    P.periodicityCycleIso.symm

/-- δ-exactness with its genuine three local short exact rows. These are the
exactness conditions of the truncation, not an assumed stable comparison. -/
def DeltaExactPeriodic (p : HellerExactness.Parameter S) (P : SComplex S) : Prop :=
  ∃ (h₁ : P.complex.ExactAt 1) (h₂ : P.complex.ExactAt 2)
    (h₃ : P.complex.ExactAt 3), HellerExactness.DeltaExact S p (periodicExtension S P h₁ h₂ h₃)

omit [HasBinaryBiproducts C] in
/-- The periodicity-induced right endpoint of the actual reindexed cochain
map is `S` applied to its original zeroth-cycle map. -/
theorem periodic_endpoint (P R : SComplex S)
    (hP₁ : P.complex.ExactAt 1) (hP₂ : P.complex.ExactAt 2) (hP₃ : P.complex.ExactAt 3)
    (hR₁ : R.complex.ExactAt 1) (hR₂ : R.complex.ExactAt 2) (hR₃ : R.complex.ExactAt 3)
    (f : P.complex ⟶ R.complex) :
    (transportEndpointMap
      (extensionMapLocal hP₁ hP₂ hP₃ hR₁ hR₂ hR₃ P.projective R.projective
        (P.twistMap R f)) P.periodicityCycleIso.symm R.periodicityCycleIso.symm).f₃ =
      S.functor.map (cyclesMap f 0) := by
  apply (cancel_mono R.periodicityCycleIso.hom).mp
  change (P.periodicityCycleIso.hom ≫ cyclesMap (P.twistMap R f) 3 ≫
    R.periodicityCycleIso.inv) ≫ R.periodicityCycleIso.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (P.periodicityCycleIso_naturality R f).symm

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem periodicityCycleIso_inv_iCycles (P : SComplex S) :
    P.periodicityCycleIso.inv ≫ S.functor.map (P.complex.iCycles 0) =
      P.complex.iCycles 3 ≫ (P.period 3).inv := by
  apply (cancel_mono (P.period 3).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← P.periodicityCycleIso_hom_iCycles, Iso.inv_hom_id_assoc]

omit [HasBinaryBiproducts C] in
theorem periodicExtension_boundary (P : SComplex S)
    (h₁ : P.complex.ExactAt 1) (h₂ : P.complex.ExactAt 2) (h₃ : P.complex.ExactAt 3) :
    (periodicExtension S P h₁ h₂ h₃).p₂ ≫
      S.functor.map (periodicExtension S P h₁ h₂ h₃).i₀ =
        P.complex.d 2 3 ≫ (P.period 3).inv := by
  change (P.complex.toCycles 2 3 ≫ P.periodicityCycleIso.inv) ≫
    S.functor.map (P.complex.iCycles 0) = _
  rw [Category.assoc, periodicityCycleIso_inv_iCycles S P,
    toCycles_i_assoc]

theorem deltaExactTruncation_of_periodic (p : HellerExactness.Parameter S)
    (P : SComplex S) (hP : DeltaExactPeriodic S p P) :
    HellerExactness.DeltaExactTruncation S p (P.complex.d 0 1)
      (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv) := by
  obtain ⟨h₁, h₂, h₃, hE⟩ := hP
  have h := HellerExactness.deltaExactTruncation_of_extension S p
    (periodicExtension S P h₁ h₂ h₃) hE
  rw [periodicExtension_boundary] at h
  simpa only [periodicExtension, transportEndpoint, extensionLocal, Extension3.d₀,
    Extension3.d₁, toCycles_i] using h

/-- The cochain-map part of Lemma 4.1 for actual periodic complexes and
actual δ-exact truncation rows. Every comparison and boundary square used
in the proof is derived from the complex differential and exactness. -/
theorem lemma_4_1 (p : HellerExactness.Parameter S) (u : TriangleCenterUnit F)
    (P R : SComplex S) (hP : DeltaExactPeriodic S p P)
    (hR : DeltaExactPeriodic S (p.twist u) R) (f : P.complex ⟶ R.complex) :
    Q.map (cyclesMap (P.twistMap R f) 0) =
      u.iso.hom.app (Q.obj (P.complex.cycles 0)) ≫ Q.map (cyclesMap f 0) := by
  obtain ⟨hP₁, hP₂, hP₃, hPE⟩ := hP
  obtain ⟨hR₁, hR₂, hR₃, hRE⟩ := hR
  let φ := transportEndpointMap
    (extensionMapLocal hP₁ hP₂ hP₃ hR₁ hR₂ hR₃ P.projective R.projective
      (P.twistMap R f)) P.periodicityCycleIso.symm R.periodicityCycleIso.symm
  exact HellerExactness.lemma_4_1_of_extension_map S p u hPE hRE φ
    (cyclesMap f 0) (periodic_endpoint S P R hP₁ hP₂ hP₃ hR₁ hR₂ hR₃ f)

end Periodic

end PretriangulatedV2.StableCategory.ComplexInjectiveExtensions
