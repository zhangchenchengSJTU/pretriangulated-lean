import PretriangulatedV2.HellerExactness
import PretriangulatedV2.AutoequivalenceShift
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Components of the positive Heller classification

The constructions in this module use three genuine short exact rows in the
ambient Frobenius abelian category. In particular, a stable endpoint equality
is strictified by subtracting an explicit projective factorization. None of
TR1, TR2, TR3, or the classification theorem is postulated as a structure field.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open PretriangulatedV2.IdealQuotient
open scoped ZeroObject

namespace PretriangulatedV2.HellerClassification

open StableCategory StableCategory.InjectiveComparison

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- The genuine full subcategory of ambient projective objects. -/
def projectives : ObjectProperty C := Projective

abbrev Projectives := (projectives (C := C)).FullSubcategory

instance projectives_closedUnderIsomorphisms :
    (projectives (C := C)).IsClosedUnderIsomorphisms where
  of_iso e h := Projective.of_iso e h

instance projectives_containsZero : (projectives (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by change Projective (0 : C); infer_instance⟩

instance projective_underlying (X : Projectives (C := C)) : Projective X.obj := X.property

instance injective_underlying (X : Projectives (C := C)) : Injective X.obj :=
  (FrobeniusAbelian.projective_iff_injective _).mp X.property

/-- An actual additive ambient equivalence restricts to the projective full
subcategory, using the proved preservation of projective objects. -/
def projectiveEquivalence (S : C ≌ C) : Projectives (C := C) ≌ Projectives (C := C) :=
  S.congrFullSubcategory (by
    ext X
    change Projective (S.functor.obj X) ↔ Projective X
    exact ⟨fun h => Projective.of_iso (S.unitIso.app X).symm
      (S.inverse.projective_obj_of_projective h), S.functor.projective_obj_of_projective⟩)

instance projectiveEquivalence_additive (S : C ≌ C) [S.functor.Additive] :
    (projectiveEquivalence S).functor.Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact S.functor.map_add

omit [Abelian C] [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[simp]
theorem projectiveEquivalence_map_hom (S : C ≌ C)
    {X Y : Projectives (C := C)} (f : X ⟶ Y) :
    ((projectiveEquivalence S).functor.map f).hom = S.functor.map f.hom := rfl

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[simp]
theorem projective_neg_hom {X Y : Projectives (C := C)} (f : X ⟶ Y) :
    (-f).hom = -f.hom := rfl

namespace Realization

open FrobeniusTriangles

omit [FrobeniusAbelian C] in
lemma middle_projective_of_boundary_stable_zero {S : ShortComplex C}
    (hS : S.ShortExact)
    (hf : Q.map S.f = 0) (hg : Q.map S.g = 0) : Projective S.X₂ := by
  let _ := hS.epi_g
  rw [functor_map_eq_zero_iff] at hf hg
  obtain ⟨P, hP, a, b, hab⟩ := hf
  obtain ⟨R, hR, c, d, hcd⟩ := hg
  let _ : Projective P := hP
  let _ : Projective R := hR
  let l : R ⟶ S.X₂ := Projective.factorThru d S.g
  have hl : l ≫ S.g = d := Projective.factorThru_comp _ _
  let z : S.X₂ ⟶ S.X₂ := 𝟙 S.X₂ - c ≫ l
  have hz : z ≫ S.g = 0 := by
    dsimp [z]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hl, hcd, sub_self]
  let k : S.X₂ ⟶ S.X₁ := (KernelFork.IsLimit.lift' hS.fIsKernel z hz).val
  have hk : k ≫ S.f = z := (KernelFork.IsLimit.lift' hS.fIsKernel z hz).property
  let r : Retract S.X₂ (R ⊞ P) :=
    { i := biprod.lift c (k ≫ a)
      r := biprod.desc l b
      retract := by
        rw [biprod.lift_desc, Category.assoc, hab, hk]
        dsimp [z]
        abel }
  exact r.projective

lemma connecting_comp_cosyzygy_map_stable_zero {S : ShortComplex C}
    (hS : S.ShortExact) :
    Q.map (connecting hS) ≫
        (Cosyzygy.functor (C := C)).map (Q.map S.f) = 0 := by
  change Q.map (connecting hS) ≫ Q.map (Cosyzygy.map S.f) = 0
  rw [← Q.map_comp, functor_map_eq_zero_iff]
  let d : S.X₂ ⟶ Injective.under S.X₂ :=
    extension hS ≫ Cosyzygy.extension S.f - Injective.ι S.X₂
  have hd : S.f ≫ d = 0 := by
    dsimp [d]
    rw [Preadditive.comp_sub, ← Category.assoc, f_extension]
    simp
  let r : S.X₃ ⟶ Injective.under S.X₂ := desc hS d hd
  have hr : S.g ≫ r = d := g_desc hS d hd
  refine ⟨Injective.under S.X₂,
    (FrobeniusAbelian.projective_iff_injective _).mpr inferInstance,
    r, cokernel.π (Injective.ι S.X₂), ?_⟩
  let _ := hS.epi_g
  apply (cancel_epi S.g).1
  rw [← Category.assoc, hr]
  dsimp [d]
  rw [Preadditive.sub_comp]
  simp

lemma boundary_stable_zero_of_connecting_isIso {S : ShortComplex C}
    (hS : S.ShortExact) [IsIso (Q.map (connecting hS))] :
    Q.map S.f = 0 ∧ Q.map S.g = 0 := by
  constructor
  · apply (Cosyzygy.functor (C := C)).map_injective
    apply (cancel_epi (Q.map (connecting hS))).1
    simpa using connecting_comp_cosyzygy_map_stable_zero hS
  · apply (cancel_mono (Q.map (connecting hS))).1
    rw [zero_comp, ← Q.map_comp, g_connecting, functor_map_eq_zero_iff]
    exact ⟨Injective.under S.X₁,
      (FrobeniusAbelian.projective_iff_injective _).mpr inferInstance,
      extension hS, cokernel.π (Injective.ι S.X₁), rfl⟩

lemma middle_projective_of_connecting_isIso {S : ShortComplex C}
    (hS : S.ShortExact) [IsIso (Q.map (connecting hS))] : Projective S.X₂ := by
  obtain ⟨hf, hg⟩ := boundary_stable_zero_of_connecting_isIso hS
  exact middle_projective_of_boundary_stable_zero hS hf hg

variable {A N : C}

abbrev realizationMiddle (a : N ⟶ Cosyzygy.obj A) : C :=
  pullback (cokernel.π (Injective.ι A)) a

def realizationIncl (a : N ⟶ Cosyzygy.obj A) : A ⟶ realizationMiddle a :=
  pullback.lift (Injective.ι A) 0 (by simp)

abbrev realizationProj (a : N ⟶ Cosyzygy.obj A) : realizationMiddle a ⟶ N :=
  pullback.snd (cokernel.π (Injective.ι A)) a

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
lemma realizationIncl_fst (a : N ⟶ Cosyzygy.obj A) :
    realizationIncl a ≫ pullback.fst (cokernel.π (Injective.ι A)) a = Injective.ι A := by
  simp [realizationIncl]

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
lemma realizationIncl_proj (a : N ⟶ Cosyzygy.obj A) :
    realizationIncl a ≫ realizationProj a = 0 := by
  simp [realizationIncl]

instance realizationIncl_mono (a : N ⟶ Cosyzygy.obj A) : Mono (realizationIncl a) :=
  mono_of_mono_fac (realizationIncl_fst a)

def realizationInclIsKernel (a : N ⟶ Cosyzygy.obj A) :
    IsLimit (KernelFork.ofι (realizationIncl a) (realizationIncl_proj a)) := by
  let hj := Abelian.monoIsKernelOfCokernel
    (CokernelCofork.ofπ (cokernel.π (Injective.ι A))
      (cokernel.condition (Injective.ι A)))
    (cokernelIsCokernel (Injective.ι A))
  apply KernelFork.IsLimit.ofι'
  intro W k hk
  have hkfst : (k ≫ pullback.fst (cokernel.π (Injective.ι A)) a) ≫
      cokernel.π (Injective.ι A) = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hk, zero_comp]
  let l : W ⟶ A :=
    (KernelFork.IsLimit.lift' hj
      (k ≫ pullback.fst (cokernel.π (Injective.ι A)) a) hkfst).val
  refine ⟨l, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, realizationIncl_fst]
    exact (KernelFork.IsLimit.lift' hj
      (k ≫ pullback.fst (cokernel.π (Injective.ι A)) a) hkfst).property
  · simp [realizationIncl, hk]

def realizationSequence (a : N ⟶ Cosyzygy.obj A) : ShortComplex C :=
  ShortComplex.mk (realizationIncl a) (realizationProj a) (realizationIncl_proj a)

omit [HasBinaryBiproducts C] in
lemma realizationSequence_shortExact (a : N ⟶ Cosyzygy.obj A) :
    (realizationSequence a).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (realizationInclIsKernel a)
  mono_f := by
    change Mono (realizationIncl a)
    infer_instance
  epi_g := by
    change Epi (realizationProj a)
    infer_instance

lemma realization_connecting_stable_eq (a : N ⟶ Cosyzygy.obj A) :
    Q.map (connecting (realizationSequence_shortExact a)) = Q.map a := by
  let hS := realizationSequence_shortExact a
  let t : realizationMiddle a ⟶ Injective.under A :=
    pullback.fst (cokernel.π (Injective.ι A)) a
  have ht : (realizationSequence a).f ≫ t = Injective.ι A := by
    exact realizationIncl_fst a
  change Q.map (connecting hS) = Q.map a
  calc
    _ = Q.map (connectingUsing hS (Injective.ι A) t ht) :=
      connectingUsing_stable_eq hS (Injective.ι A)
        (extension hS) t (f_extension hS) ht
    _ = Q.map a := by
      congr 1
      let _ := hS.epi_g
      apply (cancel_epi (realizationSequence a).g).1
      rw [g_connectingUsing]
      exact pullback.condition

lemma realizationMiddle_projective (a : N ⟶ Cosyzygy.obj A)
    [IsIso (Q.map a)] : Projective (realizationMiddle a) := by
  let hS := realizationSequence_shortExact a
  have : IsIso (Q.map (connecting hS)) := by
    rw [realization_connecting_stable_eq a]
    infer_instance
  exact middle_projective_of_connecting_isIso hS

lemma realizationMiddle_injective (a : N ⟶ Cosyzygy.obj A)
    [IsIso (Q.map a)] : Injective (realizationMiddle a) :=
  (FrobeniusAbelian.projective_iff_injective _).mp (realizationMiddle_projective a)


instance realizationSequence_injective (a : N ⟶ Cosyzygy.obj A)
    [IsIso (Q.map a)] : Injective (realizationSequence a).X₂ :=
  realizationMiddle_injective a

end Realization

namespace Extension3

variable {M N M' N' : C} {E : InjectiveComparison.Extension3 M N}
  {E' : InjectiveComparison.Extension3 M' N'}

/-- Change the endpoint of an actual three-step extension morphism to any
ambient map with the same stable class, keeping its first two middle maps.
Projectivity lifts the endpoint error through the target epimorphism. -/
def strictifyEndpoint (φ : E.Hom E') (g : N ⟶ N')
    (hg : Q.map φ.f₃ = Q.map g) : E.Hom E' := by
  have hz : Q.map (φ.f₃ - g) = 0 := by rw [Functor.map_sub, hg, sub_self]
  rw [functor_map_eq_zero_iff] at hz
  let P := hz.choose
  have hP : Projective P := hz.choose_spec.1
  let a := hz.choose_spec.2.choose
  let b := hz.choose_spec.2.choose_spec.choose
  have hab : a ≫ b = φ.f₃ - g := hz.choose_spec.2.choose_spec.choose_spec
  let : Projective P := hP
  let b' := Projective.factorThru b E'.p₂
  have hb' : b' ≫ E'.p₂ = b := Projective.factorThru_comp _ _
  exact {
    φ with
    f₃ := g
    a₂ := φ.a₂ - E.p₂ ≫ a ≫ b'
    comm_i₂ := by
      rw [Preadditive.comp_sub, φ.comm_i₂]
      simp [← Category.assoc, E.zero₂]
    comm_p₂ := by
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hb', hab]
      rw [← φ.comm_p₂, Preadditive.comp_sub, sub_sub_cancel] }

omit [FrobeniusAbelian C] in
@[simp]
theorem strictifyEndpoint_f₃ (φ : E.Hom E') (g : N ⟶ N')
    (hg : Q.map φ.f₃ = Q.map g) : (strictifyEndpoint φ g hg).f₃ = g := rfl

omit [FrobeniusAbelian C] in
@[simp]
theorem strictifyEndpoint_a₀ (φ : E.Hom E') (g : N ⟶ N')
    (hg : Q.map φ.f₃ = Q.map g) : (strictifyEndpoint φ g hg).a₀ = φ.a₀ := rfl

omit [FrobeniusAbelian C] in
@[simp]
theorem strictifyEndpoint_a₁ (φ : E.Hom E') (g : N ⟶ N')
    (hg : Q.map φ.f₃ = Q.map g) : (strictifyEndpoint φ g hg).a₁ = φ.a₁ := rfl

/-- A commutative square on the first two injective middle objects extends to
a morphism of all three short exact rows. All endpoint maps are constructed
by the ambient kernel and cokernel universal properties. -/
def completeTwoTermSquare (E : InjectiveComparison.Extension3 M N)
    (E' : InjectiveComparison.Extension3 M' N')
    (a₀ : E.I₀ ⟶ E'.I₀) (a₁ : E.I₁ ⟶ E'.I₁)
    (ha : E.d₀ ≫ a₁ = a₀ ≫ E'.d₀) : E.Hom E' := by
  have h₀ : (E.i₀ ≫ a₀) ≫ E'.p₀ = 0 := by
    apply (cancel_mono E'.i₁).1
    have h : E.i₀ ≫ a₀ ≫ E'.d₀ = 0 := by
      rw [← ha]
      simp [InjectiveComparison.Extension3.d₀, ← Category.assoc, E.zero₀]
    simpa [InjectiveComparison.Extension3.d₀, Category.assoc] using h
  let f₀ := E'.exact₀.exact.lift (E.i₀ ≫ a₀) h₀
  have hf₀ : f₀ ≫ E'.i₀ = E.i₀ ≫ a₀ := E'.exact₀.exact.lift_f _ _
  let f₁ := FrobeniusTriangles.desc E.exact₀ (a₀ ≫ E'.p₀) (by simpa [Category.assoc] using h₀)
  have hp₀ : E.p₀ ≫ f₁ = a₀ ≫ E'.p₀ := FrobeniusTriangles.g_desc E.exact₀ _ _
  have hi₁ : E.i₁ ≫ a₁ = f₁ ≫ E'.i₁ := by
    apply (cancel_epi E.p₀).1
    rw [← Category.assoc, ← Category.assoc, hp₀]
    simpa [InjectiveComparison.Extension3.d₀, Category.assoc] using ha
  have h₁ : E.i₁ ≫ (a₁ ≫ E'.p₁) = 0 := by
    rw [← Category.assoc, hi₁, Category.assoc, E'.zero₁, comp_zero]
  let f₂ := FrobeniusTriangles.desc E.exact₁ (a₁ ≫ E'.p₁) h₁
  have hp₁ : E.p₁ ≫ f₂ = a₁ ≫ E'.p₁ := FrobeniusTriangles.g_desc E.exact₁ _ _
  let a₂ := Injective.factorThru (f₂ ≫ E'.i₂) E.i₂
  have hi₂ : E.i₂ ≫ a₂ = f₂ ≫ E'.i₂ := Injective.comp_factorThru _ _
  have h₂ : E.i₂ ≫ (a₂ ≫ E'.p₂) = 0 := by
    rw [← Category.assoc, hi₂, Category.assoc, E'.zero₂, comp_zero]
  let f₃ := FrobeniusTriangles.desc E.exact₂ (a₂ ≫ E'.p₂) h₂
  exact {
    f₀ := f₀
    f₁ := f₁
    f₂ := f₂
    f₃ := f₃
    a₀ := a₀
    a₁ := a₁
    a₂ := a₂
    comm_i₀ := hf₀.symm
    comm_p₀ := hp₀
    comm_i₁ := hi₁
    comm_p₁ := hp₁
    comm_i₂ := hi₂
    comm_p₂ := FrobeniusTriangles.g_desc E.exact₂ _ _ }

end Extension3

namespace InitialRows

variable {P₀ P₁ : C} (f : P₀ ⟶ P₁)

/-- The actual kernel-to-coimage short exact row attached to a morphism. -/
abbrev row₀ : ShortComplex C := ShortComplex.cokernelSequence (kernel.ι f)

/-- The actual coimage-to-cokernel short exact row attached to a morphism. -/
abbrev row₁ : ShortComplex C :=
  ShortComplex.cokernelSequence (Abelian.factorThruCoimage f)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem row₀_shortExact : (row₀ f).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by dsimp [row₀, ShortComplex.cokernelSequence]; infer_instance
  epi_g := by dsimp [row₀, ShortComplex.cokernelSequence]; infer_instance

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem row₁_shortExact : (row₁ f).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by dsimp [row₁, ShortComplex.cokernelSequence]; infer_instance
  epi_g := by dsimp [row₁, ShortComplex.cokernelSequence]; infer_instance

instance row₀_middle_injective [Injective P₀] : Injective (row₀ f).X₂ := by
  change Injective P₀
  infer_instance

instance row₁_middle_injective [Injective P₁] : Injective (row₁ f).X₂ := by
  change Injective P₁
  infer_instance

/-- Two injective steps give the canonical second cosyzygy comparison. -/
def stableComparison [Injective P₀] [Injective P₁] :
    Q.obj (row₁ f).X₃ ≅ F.obj (F.obj (Q.obj (kernel f))) :=
  connectingIso (row₁_shortExact f) ≪≫ F.mapIso (connectingIso (row₀_shortExact f))

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[simp]
theorem differential : (row₀ f).g ≫ (row₁ f).f = f := Abelian.coimage.fac f

end InitialRows

section Parameter

variable (S : C ≌ C) [S.functor.Additive]
  (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)

/-- The canonical comparison formulation of parameter exactness. This
predicate is on genuine three-row injective extensions; equivalence with the
paper's comparison-diagram definition is supplied by `HellerExactness`. -/
def CanonicalExact {M : C} (E : InjectiveComparison.Extension3 M (S.functor.obj M)) : Prop :=
  E.stableComparison.hom = p.delta.hom.app (Q.obj M)

/-- The stable last-row boundary prescribed by the parameter for the two
actual initial rows of a fixed injective-object morphism. -/
def prescribedBoundary {P₀ P₁ : C} [Injective P₀] [Injective P₁] (f : P₀ ⟶ P₁) :
    Q.obj (S.functor.obj (kernel f)) ≅ F.obj (Q.obj (InitialRows.row₁ f).X₃) :=
  p.delta.app (Q.obj (kernel f)) ≪≫ (F.mapIso (InitialRows.stableComparison f)).symm

/-- An ambient representative of the prescribed stable boundary. -/
def boundaryRepresentative {P₀ P₁ : C} [Injective P₀] [Injective P₁]
    (f : P₀ ⟶ P₁) : S.functor.obj (kernel f) ⟶ Cosyzygy.obj (InitialRows.row₁ f).X₃ :=
  Q.preimage (prescribedBoundary S p f).hom

@[simp]
theorem map_boundaryRepresentative {P₀ P₁ : C} [Injective P₀] [Injective P₁]
    (f : P₀ ⟶ P₁) : Q.map (boundaryRepresentative S p f) =
      (prescribedBoundary S p f).hom := Q.map_preimage _

instance boundaryRepresentative_stable_isIso {P₀ P₁ : C} [Injective P₀] [Injective P₁]
    (f : P₀ ⟶ P₁) : IsIso (Q.map (boundaryRepresentative S p f)) := by
  rw [map_boundaryRepresentative]
  infer_instance

/-- Complete any prescribed morphism between injective objects to a genuine
three-step extension. The last middle object is constructed by a pullback and
is proved injective from the invertible stable boundary. -/
def completeMorphism {P₀ P₁ : C} [Injective P₀] [Injective P₁]
    (f : P₀ ⟶ P₁) : InjectiveComparison.Extension3 (kernel f) (S.functor.obj (kernel f)) where
  Z₁ := (InitialRows.row₀ f).X₃
  Z₂ := (InitialRows.row₁ f).X₃
  I₀ := P₀
  I₁ := P₁
  I₂ := Realization.realizationMiddle (boundaryRepresentative S p f)
  i₀ := kernel.ι f
  p₀ := (InitialRows.row₀ f).g
  i₁ := (InitialRows.row₁ f).f
  p₁ := (InitialRows.row₁ f).g
  i₂ := Realization.realizationIncl (boundaryRepresentative S p f)
  p₂ := Realization.realizationProj (boundaryRepresentative S p f)
  zero₀ := (InitialRows.row₀ f).zero
  zero₁ := (InitialRows.row₁ f).zero
  zero₂ := Realization.realizationIncl_proj _
  exact₀ := InitialRows.row₀_shortExact f
  exact₁ := InitialRows.row₁_shortExact f
  exact₂ := Realization.realizationSequence_shortExact _
  injective₀ := inferInstance
  injective₁ := inferInstance
  injective₂ := Realization.realizationMiddle_injective _

@[simp]
theorem completeMorphism_d₀ {P₀ P₁ : C} [Injective P₀] [Injective P₁]
    (f : P₀ ⟶ P₁) : (completeMorphism S p f).d₀ = f := Abelian.coimage.fac f

/-- The constructed completion has exactly the parameter's stable endpoint.
This proves the fixed-first-morphism existence component of TR1. -/
theorem completeMorphism_canonicalExact {P₀ P₁ : C} [Injective P₀] [Injective P₁]
    (f : P₀ ⟶ P₁) : CanonicalExact S p (completeMorphism S p f) := by
  change (connectingIso (Realization.realizationSequence_shortExact
      (boundaryRepresentative S p f))).hom ≫
    F.map (connectingIso (InitialRows.row₁_shortExact f)).hom ≫
    F.map (F.map (connectingIso (InitialRows.row₀_shortExact f)).hom) =
      p.delta.hom.app (Q.obj (kernel f))
  rw [connectingIso_hom, Realization.realization_connecting_stable_eq,
    map_boundaryRepresentative]
  rw [← F.map_comp]
  change (p.delta.app (Q.obj (kernel f)) ≪≫
    (F.mapIso (InitialRows.stableComparison f)).symm).hom ≫
    (F.mapIso (InitialRows.stableComparison f)).hom = _
  simp

/-- The fixed-first-morphism completion satisfies the actual comparison
-diagram definition of δ-exactness. -/
theorem completeMorphism_deltaExact {P₀ P₁ : C} [Injective P₀] [Injective P₁]
    (f : P₀ ⟶ P₁) :
    HellerExactness.DeltaExact S p (completeMorphism S p f) :=
  (HellerExactness.deltaExact_iff_stableComparison S p _).mpr
    (completeMorphism_canonicalExact S p f)

/-- TR1 existence in the paper's ambient δ-exact truncation formulation. -/
theorem exists_deltaExact_completion {P₀ P₁ : C} [Injective P₀] [Injective P₁]
    (f : P₀ ⟶ P₁) : ∃ (P₂ : C) (g : P₁ ⟶ P₂) (h : P₂ ⟶ S.functor.obj P₀),
      Injective P₂ ∧ HellerExactness.DeltaExactTruncation S p f g h := by
  let E := completeMorphism S p f
  refine ⟨E.I₂, E.d₁, E.p₂ ≫ S.functor.map E.i₀, E.injective₂, ?_⟩
  have hd := HellerExactness.deltaExactTruncation_of_extension S p E
    (completeMorphism_deltaExact S p f)
  simpa only [E, completeMorphism_d₀] using hd

/-- The contractible triangle is the truncation of three explicit split
short exact rows. -/
def contractibleExtension (P : C) [Injective P] :
    InjectiveComparison.Extension3 (0 : C) (S.functor.obj (0 : C)) where
  Z₁ := P
  Z₂ := 0
  I₀ := P
  I₁ := P
  I₂ := 0
  i₀ := 0
  p₀ := 𝟙 P
  i₁ := 𝟙 P
  p₁ := 0
  i₂ := 0
  p₂ := 0
  zero₀ := by simp
  zero₁ := by simp
  zero₂ := by simp
  exact₀ := {
    exact := (ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C) inferInstance).exact
    mono_f := (isZero_zero C).mono _
    epi_g := inferInstance }
  exact₁ := {
    exact := (ShortComplex.Splitting.ofIsIsoOfIsZero _ inferInstance (isZero_zero C)).exact
    mono_f := inferInstance
    epi_g := (isZero_zero C).epi _ }
  exact₂ := {
    exact := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
    mono_f := (isZero_zero C).mono _
    epi_g := (S.functor.map_isZero (isZero_zero C)).epi _ }
  injective₀ := inferInstance
  injective₁ := inferInstance
  injective₂ := inferInstance

/-- The parameter condition on a contractible row follows from its zero
left endpoint, using the additive stable functors. -/
theorem contractibleExtension_canonicalExact (P : C) [Injective P] :
    CanonicalExact S p (contractibleExtension S P) := by
  apply (F.map_isZero (F.map_isZero (F.map_isZero
    (Q.map_isZero (isZero_zero C))))).eq_of_tgt

/-- TR1 contractibility in the actual ambient truncation predicate. -/
theorem contractible_deltaExact (P : C) [Injective P] :
    HellerExactness.DeltaExactTruncation S p (𝟙 P) (0 : P ⟶ (0 : C))
      (0 : (0 : C) ⟶ S.functor.obj P) := by
  have hE := HellerExactness.deltaExactTruncation_of_extension S p
    (contractibleExtension S P)
    ((HellerExactness.deltaExact_iff_stableComparison S p _).mpr
      (contractibleExtension_canonicalExact S p P))
  simpa [contractibleExtension, InjectiveComparison.Extension3.d₀,
    InjectiveComparison.Extension3.d₁] using hE

/-- A morphism between canonically parameter-exact extensions has the
prescribed endpoint after passage to the actual stable quotient. -/
theorem stable_endpoint_eq {M M' : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M))
    (E' : InjectiveComparison.Extension3 M' (S.functor.obj M'))
    (hE : CanonicalExact S p E) (hE' : CanonicalExact S p E') (φ : E.Hom E') :
    Q.map φ.f₃ = Q.map (S.functor.map φ.f₀) := by
  apply (cancel_mono E'.stableComparison.hom).1
  rw [φ.stableComparison_naturality, hE, hE']
  exact (p.delta.hom.naturality (Q.map φ.f₀)).symm

/-- Naturality of the Heller parameter plus projective lifting makes the
endpoint of the actual row morphism strictly equal to `S(f₀)`. -/
def strictifyParameterEndpoint {M M' : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M))
    (E' : InjectiveComparison.Extension3 M' (S.functor.obj M'))
    (hE : CanonicalExact S p E) (hE' : CanonicalExact S p E') (φ : E.Hom E') : E.Hom E' :=
  Extension3.strictifyEndpoint φ (S.functor.map φ.f₀) (stable_endpoint_eq S p E E' hE hE' φ)

/-- The ambient TR3 filling equation for the triangles determined by genuine
parameter-exact three-step extensions. It preserves both prescribed first
components of the square. -/
theorem exists_completed_square {M M' : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M))
    (E' : InjectiveComparison.Extension3 M' (S.functor.obj M'))
    (hE : CanonicalExact S p E) (hE' : CanonicalExact S p E')
    (a₀ : E.I₀ ⟶ E'.I₀) (a₁ : E.I₁ ⟶ E'.I₁)
    (ha : E.d₀ ≫ a₁ = a₀ ≫ E'.d₀) :
    ∃ a₂ : E.I₂ ⟶ E'.I₂,
      E.d₁ ≫ a₂ = a₁ ≫ E'.d₁ ∧
      (E.p₂ ≫ S.functor.map E.i₀) ≫ S.functor.map a₀ =
        a₂ ≫ E'.p₂ ≫ S.functor.map E'.i₀ := by
  let φ := Extension3.completeTwoTermSquare E E' a₀ a₁ ha
  let ψ := strictifyParameterEndpoint S p E E' hE hE' φ
  have ha₀ : ψ.a₀ = a₀ := by
    change (Extension3.strictifyEndpoint φ _ _).a₀ = a₀
    rw [Extension3.strictifyEndpoint_a₀]
    rfl
  have ha₁ : ψ.a₁ = a₁ := by
    change (Extension3.strictifyEndpoint φ _ _).a₁ = a₁
    rw [Extension3.strictifyEndpoint_a₁]
    rfl
  have hf₃ : ψ.f₃ = S.functor.map ψ.f₀ := rfl
  refine ⟨ψ.a₂, ?_, ?_⟩
  · rw [InjectiveComparison.Extension3.d₁, Category.assoc, ψ.comm_i₂,
      ← Category.assoc, ψ.comm_p₁, ha₁]
    simp only [InjectiveComparison.Extension3.d₁, Category.assoc]
  · rw [Category.assoc, ← S.functor.map_comp, ← ha₀, ψ.comm_i₀,
      S.functor.map_comp, ← Category.assoc, ← hf₃, ψ.comm_p₂]
    exact Category.assoc _ _ _

/-- TR3 for arbitrary δ-exact truncations, including the isomorphisms
between the actual exact row and its prescribed triangle vertices. -/
theorem deltaExactTruncation_complete {P₀ P₁ P₂ P₀' P₁' P₂' : C}
    {f : P₀ ⟶ P₁} {g : P₁ ⟶ P₂} {h : P₂ ⟶ S.functor.obj P₀}
    {f' : P₀' ⟶ P₁'} {g' : P₁' ⟶ P₂'} {h' : P₂' ⟶ S.functor.obj P₀'}
    (hT : HellerExactness.DeltaExactTruncation S p f g h)
    (hT' : HellerExactness.DeltaExactTruncation S p f' g' h')
    (a : P₀ ⟶ P₀') (b : P₁ ⟶ P₁') (hab : f ≫ b = a ≫ f') :
    ∃ c : P₂ ⟶ P₂', g ≫ c = b ≫ g' ∧ h ≫ S.functor.map a = c ≫ h' := by
  obtain ⟨M, E, e₀, e₁, e₂, he₀, he₁, he₂, hE⟩ := hT
  obtain ⟨M', E', e₀', e₁', e₂', he₀', he₁', he₂', hE'⟩ := hT'
  let a₀ := e₀.hom ≫ a ≫ e₀'.inv
  let a₁ := e₁.hom ≫ b ≫ e₁'.inv
  have ha : E.d₀ ≫ a₁ = a₀ ≫ E'.d₀ := by
    apply (cancel_mono e₁'.hom).mp
    change (E.d₀ ≫ (e₁.hom ≫ b ≫ e₁'.inv)) ≫ e₁'.hom =
      ((e₀.hom ≫ a ≫ e₀'.inv) ≫ E'.d₀) ≫ e₁'.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hL := congrArg (fun t => t ≫ b) he₀
    have hR := congrArg (fun t => e₀.hom ≫ a ≫ e₀'.inv ≫ t) he₀'
    simp only [InjectiveComparison.Extension3.d₀, Category.assoc] at hL
    simp only [InjectiveComparison.Extension3.d₀, Category.assoc,
      Iso.inv_hom_id_assoc] at hR
    rw [hL, hR, hab]
  obtain ⟨k, hk₁, hk₂⟩ := exists_completed_square S p E E'
    ((HellerExactness.deltaExact_iff_stableComparison S p E).mp hE)
    ((HellerExactness.deltaExact_iff_stableComparison S p E').mp hE') a₀ a₁ ha
  have hg : g = e₁.inv ≫ E.d₁ ≫ e₂.hom := by
    apply (cancel_epi e₁.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact he₁.symm
  have hh : h = e₂.inv ≫ E.p₂ ≫ S.functor.map (E.i₀ ≫ e₀.hom) := by
    apply (cancel_epi e₂.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact he₂.symm
  refine ⟨e₂.inv ≫ k ≫ e₂'.hom, ?_, ?_⟩
  · rw [hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hL := congrArg (fun t => e₁.inv ≫ t ≫ e₂'.hom) hk₁
    have hR := congrArg (fun t => b ≫ e₁'.inv ≫ t) he₁'
    simp only [InjectiveComparison.Extension3.d₁, a₁, Category.assoc,
      Iso.inv_hom_id_assoc] at hL
    simp only [InjectiveComparison.Extension3.d₁, Category.assoc,
      Iso.inv_hom_id_assoc] at hR
    exact hL.trans hR
  · rw [hh]
    apply (cancel_epi e₂.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have ht := congrArg (fun t => t ≫ S.functor.map e₀'.hom) hk₂
    have ht' : E.p₂ ≫ S.functor.map (E.i₀ ≫ e₀.hom) ≫ S.functor.map a =
        k ≫ E'.p₂ ≫ S.functor.map (E'.i₀ ≫ e₀'.hom) := by
      simpa [a₀, Functor.map_comp, Category.assoc] using ht
    rw [ht', he₂']

/-- Transport an actual δ-exact truncation along three ambient isomorphisms. -/
theorem deltaExactTruncation_of_isos {P₀ P₁ P₂ P₀' P₁' P₂' : C}
    {f : P₀ ⟶ P₁} {g : P₁ ⟶ P₂} {h : P₂ ⟶ S.functor.obj P₀}
    {f' : P₀' ⟶ P₁'} {g' : P₁' ⟶ P₂'} {h' : P₂' ⟶ S.functor.obj P₀'}
    (hT : HellerExactness.DeltaExactTruncation S p f g h)
    (e₀ : P₀ ≅ P₀') (e₁ : P₁ ≅ P₁') (e₂ : P₂ ≅ P₂')
    (hf : f ≫ e₁.hom = e₀.hom ≫ f')
    (hg : g ≫ e₂.hom = e₁.hom ≫ g')
    (hh : h ≫ S.functor.map e₀.hom = e₂.hom ≫ h') :
    HellerExactness.DeltaExactTruncation S p f' g' h' := by
  obtain ⟨M, E, a₀, a₁, a₂, ha₀, ha₁, ha₂, hE⟩ := hT
  refine ⟨M, E, a₀ ≪≫ e₀, a₁ ≪≫ e₁, a₂ ≪≫ e₂, ?_, ?_, ?_, hE⟩
  · simp only [Iso.trans_hom]
    rw [← Category.assoc, ha₀, Category.assoc, hf, Category.assoc]
  · simp only [Iso.trans_hom]
    rw [← Category.assoc, ha₁, Category.assoc, hg, Category.assoc]
  · simp only [Iso.trans_hom]
    have ht := congrArg (fun t => t ≫ S.functor.map e₀.hom) ha₂
    simp only [Functor.map_comp, Category.assoc] at ht ⊢
    rw [ht, hh]

/-- Contractibility holds with any chosen zero object as the third vertex. -/
theorem contractible_deltaExact_of_isZero (P Z : C) [Injective P] (hZ : IsZero Z) :
    HellerExactness.DeltaExactTruncation S p (𝟙 P) (0 : P ⟶ Z)
      (0 : Z ⟶ S.functor.obj P) := by
  apply deltaExactTruncation_of_isos S p (contractible_deltaExact S p P)
    (Iso.refl P) (Iso.refl P) ((isZero_zero C).iso hZ)
  all_goals simp

end Parameter

namespace Rotation

open StableCategory.FrobeniusTriangles StableCategory.FrobeniusCommutation

variable (S : C ≌ C) [S.functor.Additive]

omit [HasBinaryBiproducts C] in
lemma mapped_connectingUsing_comp_cokernelComparison {T : ShortComplex C}
    (hT : T.ShortExact) :
    connectingUsing (hT.map_of_exact S.functor)
        (S.functor.map (Injective.ι T.X₁))
        (S.functor.map (extension hT)) (by
          change S.functor.map T.f ≫ S.functor.map (extension hT) = _
          rw [← S.functor.map_comp, f_extension]) ≫
      cokernelComparison (Injective.ι T.X₁) S.functor =
        S.functor.map (connecting hT) := by
  let hST := hT.map_of_exact S.functor
  let b := S.functor.map (extension hT)
  have hb : (T.map S.functor).f ≫ b = S.functor.map (Injective.ι T.X₁) := by
    change S.functor.map T.f ≫ S.functor.map (extension hT) = _
    rw [← S.functor.map_comp, f_extension]
  let c := connectingUsing hST (S.functor.map (Injective.ι T.X₁)) b hb
  change c ≫ cokernelComparison (Injective.ι T.X₁) S.functor = _
  have hc : (T.map S.functor).g ≫ c =
      b ≫ cokernel.π (S.functor.map (Injective.ι T.X₁)) :=
    g_connectingUsing hST _ _ _
  let _ := hST.epi_g
  apply (cancel_epi (T.map S.functor).g).1
  rw [← Category.assoc, hc]
  rw [Category.assoc, π_comp_cokernelComparison]
  rw [← S.functor.map_comp, ← g_connecting hT]
  simpa using S.functor.map_comp T.g (connecting hT)

lemma connecting_map_equivalence {T : ShortComplex C} (hT : T.ShortExact) :
    Q.map (connecting (hT.map_of_exact S.functor)) ≫
        (sigmaComponent S T.X₁).hom =
      (stableFunctor S.functor).map (Q.map (connecting hT)) := by
  let hST := hT.map_of_exact S.functor
  let b := S.functor.map (extension hT)
  have hb : (T.map S.functor).f ≫ b = S.functor.map (Injective.ι T.X₁) := by
    dsimp [b]
    rw [← S.functor.map_comp, f_extension]
  let _ : Mono (Injective.ι (S.functor.obj T.X₁)) := inferInstance
  have hc := connectingUsing_comparison hST
    (Injective.ι (S.functor.obj T.X₁)) (S.functor.map (Injective.ι T.X₁))
    (extension hST) b (f_extension hST) hb
  change Q.map (connecting hST) ≫ (sigmaComponent S T.X₁).hom =
    Q.map (S.functor.map (connecting hT))
  rw [sigmaComponent_hom]
  rw [← Category.assoc]
  change (Q.map (connectingUsing hST (Injective.ι (S.functor.obj T.X₁))
      (extension hST) (f_extension hST)) ≫
      Q.map (Cosyzygy.comparison (Injective.ι (S.functor.obj T.X₁))
        (S.functor.map (Injective.ι T.X₁)))) ≫
      Q.map (cokernelComparison (Injective.ι T.X₁) S.functor) = _
  rw [hc, ← Q.map_comp]
  rw [mapped_connectingUsing_comp_cokernelComparison S hT]

/-- The third row used in forward rotation: apply `S`, and negate its
projection.  Negating the projection (rather than the inclusion) is what
makes the last differential equal to `-S(d₀)` while leaving the preceding
differential unchanged. -/
def signedMapSequence (T : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (S.functor.map T.f) (-S.functor.map T.g) (by
    rw [Preadditive.comp_neg, ← S.functor.map_comp, T.zero,
      S.functor.map_zero, neg_zero])

private def negIso' (X : C) : X ≅ X where
  hom := -𝟙 X
  inv := -𝟙 X
  hom_inv_id := by simp
  inv_hom_id := by simp

def mapIsoSignedMapSequence (T : ShortComplex C) :
    T.map S.functor ≅ signedMapSequence S T :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (negIso' _)
    (by simp [signedMapSequence])
    (by simp [signedMapSequence, negIso'])

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
lemma signedMapSequence_shortExact {T : ShortComplex C} (hT : T.ShortExact) :
    (signedMapSequence S T).ShortExact :=
  ShortComplex.shortExact_of_iso (mapIsoSignedMapSequence S T)
    (hT.map_of_exact S.functor)

lemma signedMap_connecting_eq_neg {T : ShortComplex C} (hT : T.ShortExact) :
    Q.map (connecting (signedMapSequence_shortExact S hT)) =
      -Q.map (connecting (hT.map_of_exact S.functor)) := by
  have h := connecting_naturality (hT.map_of_exact S.functor)
    (signedMapSequence_shortExact S hT) (mapIsoSignedMapSequence S T).hom
  have h' : Q.map (connecting (hT.map_of_exact S.functor)) =
      -Q.map (connecting (signedMapSequence_shortExact S hT)) := by
    simpa [mapIsoSignedMapSequence, signedMapSequence, negIso'] using h
  rw [h']
  simp

/-- The exact stable boundary formula needed for rotation. -/
lemma signedMap_connecting_comp_sigma {T : ShortComplex C} (hT : T.ShortExact) :
    Q.map (connecting (signedMapSequence_shortExact S hT)) ≫
        (sigmaComponent S T.X₁).hom =
      -(stableFunctor S.functor).map (Q.map (connecting hT)) := by
  rw [signedMap_connecting_eq_neg S hT, Preadditive.neg_comp,
    connecting_map_equivalence S hT]


/-- Forward cyclic rotation of the three ambient short exact rows. -/
def rotate {M : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    InjectiveComparison.Extension3 E.Z₁ (S.functor.obj E.Z₁) where
  Z₁ := E.Z₂
  Z₂ := S.functor.obj M
  I₀ := E.I₁
  I₁ := E.I₂
  I₂ := S.functor.obj E.I₀
  i₀ := E.i₁
  p₀ := E.p₁
  i₁ := E.i₂
  p₁ := E.p₂
  i₂ := S.functor.map E.i₀
  p₂ := -S.functor.map E.p₀
  zero₀ := E.zero₁
  zero₁ := E.zero₂
  zero₂ := by
    rw [Preadditive.comp_neg, ← S.functor.map_comp, E.zero₀,
      S.functor.map_zero, neg_zero]
  exact₀ := E.exact₁
  exact₁ := E.exact₂
  exact₂ := signedMapSequence_shortExact S E.exact₀
  injective₀ := E.injective₁
  injective₁ := E.injective₂
  injective₂ := inferInstance

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[simp]
lemma rotate_d₀ {M : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    (rotate S E).d₀ = E.d₁ := rfl

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[simp]
lemma rotate_d₁ {M : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    (rotate S E).d₁ = E.p₂ ≫ S.functor.map E.i₀ := rfl

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
lemma rotate_last_differential {M : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    (rotate S E).p₂ ≫ S.functor.map (rotate S E).i₀ =
      -S.functor.map E.d₀ := by
  change (-S.functor.map E.p₀) ≫ S.functor.map E.i₁ = _
  rw [Preadditive.neg_comp, ← S.functor.map_comp]

/-- Cyclic associativity of the four stable connecting factors. -/
lemma rotate_stableComparison_comp_connecting₀ {M : C}
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    (rotate S E).stableComparison.hom ≫
        (cube StableCategory.InjectiveComparison.F).map
          (StableCategory.InjectiveComparison.Q.map
            (connecting E.exact₀)) =
      StableCategory.InjectiveComparison.Q.map
          (connecting (rotate S E).exact₂) ≫
        StableCategory.InjectiveComparison.F.map E.stableComparison.hom := by
  rw [InjectiveComparison.Extension3.stableComparison_hom,
    InjectiveComparison.Extension3.stableComparison_hom]
  simp only [cube, Functor.comp_map, Functor.map_comp]
  simp only [Category.assoc]

lemma rotate_connecting_comp_map_delta {M : C}
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    StableCategory.InjectiveComparison.Q.map
        (connecting (rotate S E).exact₂) ≫
      StableCategory.InjectiveComparison.F.map
        (p.delta.hom.app (StableCategory.InjectiveComparison.Q.obj M)) =
      (stableFunctor S.functor).map
          (StableCategory.InjectiveComparison.Q.map (connecting E.exact₀)) ≫
        p.delta.hom.app
          (StableCategory.InjectiveComparison.F.obj
            (StableCategory.InjectiveComparison.Q.obj M)) := by
  have hrow := signedMap_connecting_comp_sigma S E.exact₀
  change StableCategory.InjectiveComparison.Q.map
      (connecting (rotate S E).exact₂) ≫
        (sigmaComponent S M).hom =
      -(stableFunctor S.functor).map
        (StableCategory.InjectiveComparison.Q.map (connecting E.exact₀)) at hrow
  have hc := congrArg (fun k =>
      StableCategory.InjectiveComparison.Q.map
          (connecting (rotate S E).exact₂) ≫ k)
    (p.commutes (StableCategory.InjectiveComparison.Q.obj M))
  simp only [Preadditive.comp_add, comp_zero, sigma_hom_app] at hc
  rw [← Category.assoc, hrow, Preadditive.neg_comp] at hc
  simpa using eq_neg_of_add_eq_zero_left hc

lemma delta_comp_cube_map_connecting₀ {M : C}
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    p.delta.hom.app (StableCategory.InjectiveComparison.Q.obj E.Z₁) ≫
        (cube StableCategory.InjectiveComparison.F).map
          (StableCategory.InjectiveComparison.Q.map (connecting E.exact₀)) =
      StableCategory.InjectiveComparison.Q.map
          (connecting (rotate S E).exact₂) ≫
        StableCategory.InjectiveComparison.F.map
          (p.delta.hom.app (StableCategory.InjectiveComparison.Q.obj M)) := by
  rw [rotate_connecting_comp_map_delta S p E]
  exact (p.delta.hom.naturality
    (StableCategory.InjectiveComparison.Q.map (connecting E.exact₀))).symm

/-- The canonical Heller equation is invariant in both directions under the
actual cyclic rotation. -/
theorem canonicalExact_rotate_iff {M : C}
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)
    (E : InjectiveComparison.Extension3 M (S.functor.obj M)) :
    CanonicalExact S p (rotate S E) ↔ CanonicalExact S p E := by
  let c₀ := StableCategory.InjectiveComparison.Q.map (connecting E.exact₀)
  let cr := StableCategory.InjectiveComparison.Q.map
    (connecting (rotate S E).exact₂)
  have : IsIso c₀ := by
    dsimp [c₀]
    rw [← StableCategory.InjectiveComparison.connectingIso_hom E.exact₀]
    infer_instance
  have : IsIso cr := by
    dsimp [cr]
    rw [← StableCategory.InjectiveComparison.connectingIso_hom
      (rotate S E).exact₂]
    infer_instance
  constructor
  · intro hrot
    apply StableCategory.InjectiveComparison.F.map_injective
    apply (cancel_epi cr).1
    dsimp [cr]
    rw [← rotate_stableComparison_comp_connecting₀ S E,
      ← delta_comp_cube_map_connecting₀ S p E]
    exact congrArg (fun k => k ≫
      (cube StableCategory.InjectiveComparison.F).map c₀) hrot
  · intro hE
    apply (cancel_mono
      ((cube StableCategory.InjectiveComparison.F).map c₀)).1
    rw [rotate_stableComparison_comp_connecting₀ S E,
      delta_comp_cube_map_connecting₀ S p E]
    exact congrArg (fun k =>
      StableCategory.InjectiveComparison.Q.map
          (connecting (rotate S E).exact₂) ≫
        StableCategory.InjectiveComparison.F.map k) hE

/-- Forward rotation preserves the actual comparison-diagram truncation. -/
theorem deltaExactTruncation_rotate
    (p : FrobeniusCommutation.StableHellerParameter S)
    {P₀ P₁ P₂ : C} {f : P₀ ⟶ P₁} {g : P₁ ⟶ P₂} {h : P₂ ⟶ S.functor.obj P₀}
    (hT : HellerExactness.DeltaExactTruncation S p f g h) :
    HellerExactness.DeltaExactTruncation S p g h (-S.functor.map f) := by
  obtain ⟨M, E, e₀, e₁, e₂, he₀, he₁, he₂, hE⟩ := hT
  have hR : HellerExactness.DeltaExact S p (rotate S E) :=
    (HellerExactness.deltaExact_iff_stableComparison S p _).mpr
      ((canonicalExact_rotate_iff S p E).mpr
        ((HellerExactness.deltaExact_iff_stableComparison S p E).mp hE))
  refine ⟨E.Z₁, rotate S E, e₁, e₂, S.functor.mapIso e₀, ?_, ?_, ?_, hR⟩
  · exact he₁
  · change (E.p₂ ≫ S.functor.map E.i₀) ≫ S.functor.map e₀.hom = e₂.hom ≫ h
    rw [Category.assoc, ← S.functor.map_comp]
    exact he₂
  · change (-S.functor.map E.p₀) ≫ S.functor.map (E.i₁ ≫ e₁.hom) =
      S.functor.map e₀.hom ≫ (-S.functor.map f)
    have ht := congrArg (fun k => -S.functor.map k) he₀
    simpa only [InjectiveComparison.Extension3.d₀, Functor.map_comp,
      Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using ht

/-- The endpoint isomorphism used for the inverse cyclic row.  Its sign
cancels the sign inserted by `rotate`. -/
def negUnitInvIso (L : C) :
    S.inverse.obj (S.functor.obj L) ≅ L where
  hom := -S.unitIso.inv.app L
  inv := -S.unitIso.hom.app L
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- Apply `S⁻¹` to the last row and put in the inverse rotation sign. -/
def predecessorRow₀ {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    ShortComplex C :=
  ShortComplex.mk (S.inverse.map E'.i₂)
    ((-S.inverse.map E'.p₂) ≫ S.unitIso.inv.app L) (by
      rw [← Category.assoc, Preadditive.comp_neg, ← S.inverse.map_comp,
        E'.zero₂, S.inverse.map_zero, neg_zero, zero_comp])

def mappedLastRowIsoPredecessorRow₀ {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    E'.row₂.map S.inverse ≅ predecessorRow₀ S E' :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (negUnitInvIso S L)
    (by simp [predecessorRow₀])
    (by simp [predecessorRow₀, negUnitInvIso])

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
lemma predecessorRow₀_shortExact {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    (predecessorRow₀ S E').ShortExact :=
  ShortComplex.shortExact_of_iso (mappedLastRowIsoPredecessorRow₀ S E')
    (E'.exact₂.map_of_exact S.inverse)

/-- The old middle row with its endpoint transported to `S(S⁻¹ Z₂)`. -/
def predecessorRow₂ {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    ShortComplex C :=
  ShortComplex.mk E'.i₁
    (E'.p₁ ≫ S.counitIso.inv.app E'.Z₂) (by
      rw [← Category.assoc, E'.zero₁, zero_comp])

def middleRowIsoPredecessorRow₂ {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    E'.row₁ ≅ predecessorRow₂ S E' :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (S.counitIso.app E'.Z₂).symm
    (by simp [predecessorRow₂])
    (by simp [predecessorRow₂])

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive] in
lemma predecessorRow₂_shortExact {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    (predecessorRow₂ S E').ShortExact :=
  ShortComplex.shortExact_of_iso (middleRowIsoPredecessorRow₂ S E')
    E'.exact₁

/-- An actual inverse cyclic predecessor of a three-row extension. -/
abbrev predecessor {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    InjectiveComparison.Extension3 (S.inverse.obj E'.Z₂)
      (S.functor.obj (S.inverse.obj E'.Z₂)) where
  Z₁ := L
  Z₂ := E'.Z₁
  I₀ := S.inverse.obj E'.I₂
  I₁ := E'.I₀
  I₂ := E'.I₁
  i₀ := S.inverse.map E'.i₂
  p₀ := (-S.inverse.map E'.p₂) ≫ S.unitIso.inv.app L
  i₁ := E'.i₀
  p₁ := E'.p₀
  i₂ := E'.i₁
  p₂ := E'.p₁ ≫ S.counitIso.inv.app E'.Z₂
  zero₀ := by
    rw [← Category.assoc, Preadditive.comp_neg, ← S.inverse.map_comp,
      E'.zero₂, S.inverse.map_zero, neg_zero, zero_comp]
  zero₁ := E'.zero₀
  zero₂ := by rw [← Category.assoc, E'.zero₁, zero_comp]
  exact₀ := predecessorRow₀_shortExact S E'
  exact₁ := E'.exact₀
  exact₂ := predecessorRow₂_shortExact S E'
  injective₀ := inferInstance
  injective₁ := E'.injective₀
  injective₂ := E'.injective₁

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[simp]
lemma predecessor_Z₁ {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    (predecessor S E').Z₁ = L := rfl

omit [Abelian C] [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive] in
lemma map_unitInv_eq_counit (L : C) :
    S.functor.map (S.unitIso.inv.app L) =
      S.counitIso.hom.app (S.functor.obj L) := by
  apply (cancel_epi (S.counitIso.inv.app (S.functor.obj L))).1
  rw [S.counitIso_functor_comp]
  simp

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
lemma inverseSign_counit_naturality {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    -S.functor.map
        ((-S.inverse.map E'.p₂) ≫ S.unitIso.inv.app L) =
      S.counitIso.hom.app E'.I₂ ≫ E'.p₂ := by
  rw [S.functor.map_comp, S.functor.map_neg, Preadditive.neg_comp,
    neg_neg, map_unitInv_eq_counit S]
  exact S.counitIso.hom.naturality E'.p₂

/-- The rotated predecessor maps strictly to the given extension; all seven
components are isomorphisms. -/
def rotatePredecessorHom {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    (rotate S (predecessor S E')).Hom E' where
  f₀ := 𝟙 L
  f₁ := 𝟙 E'.Z₁
  f₂ := S.counitIso.hom.app E'.Z₂
  f₃ := 𝟙 (S.functor.obj L)
  a₀ := 𝟙 E'.I₀
  a₁ := 𝟙 E'.I₁
  a₂ := S.counitIso.hom.app E'.I₂
  comm_i₀ := by simp [rotate, predecessor]
  comm_p₀ := by simp [rotate, predecessor]
  comm_i₁ := by simp [rotate, predecessor]
  comm_p₁ := by simp [rotate, predecessor]
  comm_i₂ := by simp [rotate, predecessor]
  comm_p₂ := by
    change (-S.functor.map
      ((-S.inverse.map E'.p₂) ≫ S.unitIso.inv.app L)) ≫ 𝟙 _ = _
    simpa only [Category.comp_id] using inverseSign_counit_naturality S E'

lemma rotatePredecessor_stableComparison {L : C}
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    (rotate S (predecessor S E')).stableComparison.hom =
      E'.stableComparison.hom := by
  have h := (rotatePredecessorHom S E').stableComparison_naturality
  dsimp [rotatePredecessorHom] at h
  simp only [predecessor_Z₁] at h ⊢
  change StableCategory.InjectiveComparison.Q.map (𝟙 (S.functor.obj L)) ≫
      E'.stableComparison.hom =
    (rotate S (predecessor S E')).stableComparison.hom ≫
      (cube StableCategory.InjectiveComparison.F).map
        (StableCategory.InjectiveComparison.Q.map (𝟙 L)) at h
  simpa only [StableCategory.InjectiveComparison.Q.map_id,
    (cube StableCategory.InjectiveComparison.F).map_id,
    Category.id_comp, Category.comp_id] using h.symm

lemma canonicalExact_rotatePredecessor_iff {L : C}
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L)) :
    CanonicalExact S p (rotate S (predecessor S E')) ↔
      CanonicalExact S p E' := by
  unfold CanonicalExact
  change (rotate S (predecessor S E')).stableComparison.hom =
      p.delta.hom.app (StableCategory.InjectiveComparison.Q.obj L) ↔
    E'.stableComparison.hom =
      p.delta.hom.app (StableCategory.InjectiveComparison.Q.obj L)
  rw [rotatePredecessor_stableComparison S E']

/-- Every canonically exact extension is the rotation (up to the strict
endpoint comparison above) of a canonically exact actual predecessor. -/
theorem predecessor_canonicalExact {L : C}
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)
    (E' : InjectiveComparison.Extension3 L (S.functor.obj L))
    (hE' : CanonicalExact S p E') :
    CanonicalExact S p (predecessor S E') := by
  apply (canonicalExact_rotate_iff S p (predecessor S E')).mp
  exact (canonicalExact_rotatePredecessor_iff S p E').mpr hE'

/-- Backward ambient rotation: a rotated δ-exact truncation has an actual
canonically exact predecessor realizing the unrotated truncation. -/
theorem deltaExactTruncation_of_rotate
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)
    {P₀ P₁ P₂ : C} {f : P₀ ⟶ P₁} {g : P₁ ⟶ P₂}
    {h : P₂ ⟶ S.functor.obj P₀}
    (hT : StableCategory.HellerExactness.DeltaExactTruncation
      S p g h (-S.functor.map f)) :
    StableCategory.HellerExactness.DeltaExactTruncation S p f g h := by
  obtain ⟨L, E', e₀, e₁, e₂, he₀, he₁, he₂, hE'⟩ := hT
  let E := predecessor S E'
  let ē₀ : E.I₀ ≅ P₀ :=
    S.inverse.mapIso e₂ ≪≫ (S.unitIso.app P₀).symm
  have hEc : CanonicalExact S p E :=
    predecessor_canonicalExact S p E'
      ((StableCategory.HellerExactness.deltaExact_iff_stableComparison
        S p E').mp hE')
  have hE : StableCategory.HellerExactness.DeltaExact S p E :=
    (StableCategory.HellerExactness.deltaExact_iff_stableComparison
      S p E).mpr hEc
  refine ⟨S.inverse.obj E'.Z₂, E, ē₀, e₀, e₁, ?_, ?_, ?_, hE⟩
  · have ht := congrArg
      (fun k => -S.inverse.map k ≫ S.unitIso.inv.app P₁) he₂
    dsimp [E, ē₀, predecessor, InjectiveComparison.Extension3.d₀]
    simp only [Functor.map_comp, S.inverse.map_neg, Preadditive.neg_comp,
      Preadditive.comp_neg, neg_neg, Category.assoc] at ht ⊢
    have hi₀ : S.inverse.map (S.functor.map E'.i₀) ≫
        S.unitIso.inv.app E'.I₀ ≫ e₀.hom =
      S.unitIso.inv.app L ≫ E'.i₀ ≫ e₀.hom := by
      simpa only [Functor.comp_map, Functor.id_map] using S.unitIso.inv.naturality_assoc E'.i₀ e₀.hom
    have he₀nat : S.inverse.map (S.functor.map e₀.hom) ≫
        S.unitIso.inv.app P₁ =
      S.unitIso.inv.app E'.I₀ ≫ e₀.hom := by
      simpa only [Functor.comp_map, Functor.id_map] using S.unitIso.inv.naturality e₀.hom
    have hfnat : S.inverse.map (S.functor.map f) ≫
        S.unitIso.inv.app P₁ = S.unitIso.inv.app P₀ ≫ f := by
      simpa only [Functor.comp_map, Functor.id_map] using S.unitIso.inv.naturality f
    rw [← hi₀, ← he₀nat]
    rw [hfnat] at ht
    exact ht
  · exact he₀
  · dsimp [E, ē₀, predecessor]
    simp only [Functor.map_comp, Category.assoc]
    have hi₂ : E'.i₂ ≫ S.counitIso.inv.app E'.I₂ ≫
        (S.functor.map (S.inverse.map e₂.hom) ≫
          S.functor.map (S.unitIso.inv.app P₀)) =
      S.counitIso.inv.app E'.Z₂ ≫
        S.functor.map (S.inverse.map E'.i₂) ≫
          (S.functor.map (S.inverse.map e₂.hom) ≫
            S.functor.map (S.unitIso.inv.app P₀)) := by
      simpa only [Functor.comp_map, Functor.id_map] using S.counitIso.inv.naturality_assoc E'.i₂
        (S.functor.map (S.inverse.map e₂.hom) ≫
          S.functor.map (S.unitIso.inv.app P₀))
    have he₂nat : e₂.hom ≫
        S.counitIso.inv.app (S.functor.obj P₀) ≫
          S.functor.map (S.unitIso.inv.app P₀) =
      S.counitIso.inv.app E'.I₂ ≫
        S.functor.map (S.inverse.map e₂.hom) ≫
          S.functor.map (S.unitIso.inv.app P₀) := by
      simpa only [Functor.comp_map, Functor.id_map] using S.counitIso.inv.naturality_assoc e₂.hom
        (S.functor.map (S.unitIso.inv.app P₀))
    rw [← hi₂, ← he₂nat, S.counitIso_functor_comp,
      Category.comp_id]
    simpa only [InjectiveComparison.Extension3.d₁, Category.assoc] using he₁


end Rotation

/-- The integer shift on projective objects constructed from the actual
restricted autoequivalence. -/
@[instance_reducible]
def projectiveHasShift (S : C ≌ C) : HasShift (Projectives (C := C)) ℤ :=
  AutoequivalenceShift.hasShift (projectiveEquivalence S)

/-- Its first shift is canonically the restricted ambient equivalence. -/
def projectiveShiftOneIso (S : C ≌ C) :
    letI := projectiveHasShift S
    shiftFunctor (Projectives (C := C)) (1 : ℤ) ≅ (projectiveEquivalence S).functor :=
  AutoequivalenceShift.shiftOneIso (projectiveEquivalence S)

section WithShift

variable (S : C ≌ C) [S.functor.Additive]
  (p : FrobeniusCommutation.StableHellerParameter S)
  [HasShift (Projectives (C := C)) ℤ]
  (e : shiftFunctor (Projectives (C := C)) (1 : ℤ) ≅ (projectiveEquivalence S).functor)

/-- Distinguished projective triangles are exactly the actual ambient
δ-exact truncations, with the constructed first shift compared to `S`. -/
def distinguishedTriangles : Set (Triangle (Projectives (C := C))) :=
  {T | HellerExactness.DeltaExactTruncation S p T.mor₁.hom T.mor₂.hom
    ((T.mor₃ ≫ e.hom.app T.obj₁).hom)}

/-- The genuine projective-category version of the fixed-morphism TR1 axiom. -/
theorem distinguished_cocone_triangle {X Y : Projectives (C := C)} (f : X ⟶ Y) :
    ∃ (Z : Projectives (C := C)) (g : Y ⟶ Z)
      (h : Z ⟶ (shiftFunctor (Projectives (C := C)) (1 : ℤ)).obj X),
      Triangle.mk f g h ∈ distinguishedTriangles S p e := by
  obtain ⟨Z, g, h, hZ, hT⟩ := exists_deltaExact_completion S p f.hom
  let Z' : Projectives (C := C) :=
    ⟨Z, (FrobeniusAbelian.projective_iff_injective _).mpr hZ⟩
  let g' : Y ⟶ Z' := ObjectProperty.homMk g
  let h' : Z' ⟶ (projectiveEquivalence S).functor.obj X := ObjectProperty.homMk h
  refine ⟨Z', g', h' ≫ e.inv.app X, ?_⟩
  change HellerExactness.DeltaExactTruncation S p f.hom g
    (((h' ≫ e.inv.app X) ≫ e.hom.app X).hom)
  simp only [Category.assoc, e.inv_hom_id_app, Category.comp_id]
  exact hT

/-- The genuine projective-category contractibility axiom. -/
theorem contractible_distinguished (X : Projectives (C := C)) :
    Pretriangulated.contractibleTriangle X ∈ distinguishedTriangles S p e := by
  change HellerExactness.DeltaExactTruncation S p (𝟙 X.obj)
    (0 : X.obj ⟶ (0 : Projectives (C := C)).obj)
    (((0 : (0 : Projectives (C := C)) ⟶ _ ) ≫ e.hom.app X).hom)
  rw [zero_comp]
  apply contractible_deltaExact_of_isZero S p
  exact (projectives (C := C)).ι.map_isZero (isZero_zero (Projectives (C := C)))

/-- The genuine projective-category TR3 filling axiom. -/
theorem complete_distinguished_triangle_morphism
    (T₁ T₂ : Triangle (Projectives (C := C)))
    (hT₁ : T₁ ∈ distinguishedTriangles S p e)
    (hT₂ : T₂ ∈ distinguishedTriangles S p e)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (hab : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ (shiftFunctor (Projectives (C := C)) (1 : ℤ)).map a = c ≫ T₂.mor₃ := by
  obtain ⟨c, hc₁, hc₂⟩ := deltaExactTruncation_complete S p hT₁ hT₂ a.hom b.hom
    (congrArg (fun t => t.hom) hab)
  refine ⟨ObjectProperty.homMk c, ObjectProperty.hom_ext _ hc₁, ?_⟩
  apply (cancel_mono (e.hom.app T₂.obj₁)).mp
  rw [Category.assoc, e.hom.naturality, ← Category.assoc]
  apply ObjectProperty.hom_ext
  simpa only [ObjectProperty.FullSubcategory.comp_hom,
    projectiveEquivalence_map_hom, projectiveEquivalence, Equivalence.congrFullSubcategory,
    ObjectProperty.lift, ObjectProperty.homMk, ObjectProperty.ι, inducedFunctor,
    Functor.comp_obj, Functor.comp_map, Category.assoc] using hc₂

/-- Distinguished triangles are closed under actual triangle isomorphisms. -/
theorem isomorphic_distinguished (T₁ : Triangle (Projectives (C := C)))
    (hT₁ : T₁ ∈ distinguishedTriangles S p e)
    (T₂ : Triangle (Projectives (C := C))) (i : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles S p e := by
  apply deltaExactTruncation_of_isos S p hT₁
    ((projectives (C := C)).ι.mapIso (Triangle.π₁.mapIso i.symm))
    ((projectives (C := C)).ι.mapIso (Triangle.π₂.mapIso i.symm))
    ((projectives (C := C)).ι.mapIso (Triangle.π₃.mapIso i.symm))
  · exact congrArg (fun t => t.hom) i.inv.comm₁
  · exact congrArg (fun t => t.hom) i.inv.comm₂
  · have ht := i.inv.comm₃
    have ht' := congrArg (fun t => t ≫ e.hom.app T₂.obj₁) ht
    rw [Category.assoc, e.hom.naturality] at ht'
    simpa only [ObjectProperty.FullSubcategory.comp_hom,
      projectiveEquivalence_map_hom, projectiveEquivalence, Equivalence.congrFullSubcategory,
      ObjectProperty.lift, ObjectProperty.homMk, ObjectProperty.ι, inducedFunctor, Functor.mapIso,
      Functor.comp_obj, Functor.comp_map,
      Triangle.π₁, Triangle.π₃, Iso.symm_hom, Category.assoc] using congrArg (fun t => t.hom) ht'

/-- Forward TR2 for genuine projective triangles. -/
theorem rotate_distinguished_forward (T : Triangle (Projectives (C := C)))
    (hT : T ∈ distinguishedTriangles S p e) :
    T.rotate ∈ distinguishedTriangles S p e := by
  have hR := Rotation.deltaExactTruncation_rotate S p hT
  apply deltaExactTruncation_of_isos S p hR (Iso.refl _) (Iso.refl _)
    ((projectives (C := C)).ι.mapIso (e.app T.obj₁)).symm
  · simp
  · have ht : (T.mor₃ ≫ e.hom.app T.obj₁) ≫ e.inv.app T.obj₁ = T.mor₃ := by simp
    simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.ι,
      inducedFunctor, Functor.mapIso, Iso.app_inv, Iso.symm_hom, Iso.refl_hom,
      Category.id_comp, Triangle.rotate, Triangle.mk] using congrArg (fun t => t.hom) ht
  · simp only [Iso.refl_hom, S.functor.map_id, Category.comp_id]
    have ht := congrArg (fun t => e.inv.app T.obj₁ ≫ t) (e.hom.naturality T.mor₁)
    simp only [← Category.assoc, e.inv_hom_id_app, Category.id_comp] at ht
    have hn := congrArg (fun t => -(t.hom)) ht.symm
    simpa only [ObjectProperty.FullSubcategory.comp_hom,
      projectiveEquivalence_map_hom, projectiveEquivalence, Equivalence.congrFullSubcategory,
      ObjectProperty.lift, ObjectProperty.homMk, ObjectProperty.ι, inducedFunctor,
      Functor.comp_obj, Functor.comp_map, Functor.mapIso, Iso.symm_hom,
      Triangle.rotate, Triangle.mk, Iso.app_inv, Iso.refl_hom, projective_neg_hom,
      Preadditive.comp_neg,
      Preadditive.neg_comp, Category.assoc, Functor.map_id, Category.comp_id, Functor.map_id] using hn

/-- Backward TR2 uses the actual inverse cyclic extension. -/
theorem rotate_distinguished_backward (T : Triangle (Projectives (C := C)))
    (hT : T.rotate ∈ distinguishedTriangles S p e) :
    T ∈ distinguishedTriangles S p e := by
  apply Rotation.deltaExactTruncation_of_rotate S p
  apply deltaExactTruncation_of_isos S p hT (Iso.refl _) (Iso.refl _)
    ((projectives (C := C)).ι.mapIso (e.app T.obj₁))
  · simp
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, S.functor.map_id, Category.comp_id]
    have ht := congrArg (fun t => -(t.hom)) (e.hom.naturality T.mor₁)
    simpa only [ObjectProperty.FullSubcategory.comp_hom,
      projectiveEquivalence_map_hom, projectiveEquivalence, Equivalence.congrFullSubcategory,
      ObjectProperty.lift, ObjectProperty.homMk, ObjectProperty.ι, inducedFunctor,
      Functor.comp_obj, Functor.comp_map, Functor.mapIso, Iso.app_hom,
      Triangle.rotate, Triangle.mk, projective_neg_hom,
      Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using ht

/-- The actual bidirectional rotation axiom. -/
theorem rotate_distinguished_triangle (T : Triangle (Projectives (C := C))) :
    T ∈ distinguishedTriangles S p e ↔ T.rotate ∈ distinguishedTriangles S p e :=
  ⟨rotate_distinguished_forward S p e T, rotate_distinguished_backward S p e T⟩

variable [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]

/-- The positive direction of Heller's theorem: the parameter constructs an
actual pretriangulated structure on the genuine projective full subcategory.
Every axiom is supplied by a proved construction above. -/
@[instance_reducible]
def pretriangulated : Pretriangulated (Projectives (C := C)) where
  distinguishedTriangles := distinguishedTriangles S p e
  isomorphic_distinguished := isomorphic_distinguished S p e
  contractible_distinguished := contractible_distinguished S p e
  distinguished_cocone_triangle := distinguished_cocone_triangle S p e
  rotate_distinguished_triangle := rotate_distinguished_triangle S p e
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism S p e

end WithShift

/-- Positive Heller existence with the integer shift actually constructed
from the ambient equivalence; no shift or pretriangulation is postulated. -/
@[instance_reducible]
def constructedPretriangulated (S : C ≌ C) [S.functor.Additive]
    (p : FrobeniusCommutation.StableHellerParameter S) :
    letI := projectiveHasShift S
    letI : ∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive :=
      fun n => AutoequivalenceShift.shift_additive (projectiveEquivalence S) n
    Pretriangulated (Projectives (C := C)) :=
  letI := projectiveHasShift S
  letI : ∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive :=
    fun n => AutoequivalenceShift.shift_additive (projectiveEquivalence S) n
  pretriangulated S p (projectiveShiftOneIso S)

end PretriangulatedV2.HellerClassification
