import PretriangulatedV2.Cosyzygy
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Triangulated.Rotate
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Triangles arising from Frobenius short exact sequences

The connecting morphism is constructed using actual injective extensions and
ambient cokernel universal properties. Its stable class and naturality are
proved in the projective stable quotient.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory CategoryTheory.Limits
open PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory.FrobeniusTriangles

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- Descent through the actual cokernel map of a short exact sequence. -/
abbrev desc {S : ShortComplex C} (hS : S.ShortExact) {W : C}
    (a : S.X₂ ⟶ W) (ha : S.f ≫ a = 0) : S.X₃ ⟶ W :=
  (CokernelCofork.IsColimit.desc' hS.gIsCokernel a ha).val

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[reassoc (attr := simp)]
theorem g_desc {S : ShortComplex C} (hS : S.ShortExact) {W : C}
    (a : S.X₂ ⟶ W) (ha : S.f ≫ a = 0) :
    S.g ≫ desc hS a ha = a :=
  (CokernelCofork.IsColimit.desc' hS.gIsCokernel a ha).property

/-- The ambient connecting morphism for an arbitrary injective embedding and
an extension along the first arrow of the short exact sequence. -/
def connectingUsing {S : ShortComplex C} (hS : S.ShortExact) {I : C}
    (i : S.X₁ ⟶ I) (a : S.X₂ ⟶ I) (ha : S.f ≫ a = i) :
    S.X₃ ⟶ cokernel i :=
  desc hS (a ≫ cokernel.π i) (by rw [← Category.assoc, ha]; simp)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[reassoc (attr := simp)]
theorem g_connectingUsing {S : ShortComplex C} (hS : S.ShortExact) {I : C}
    (i : S.X₁ ⟶ I) (a : S.X₂ ⟶ I) (ha : S.f ≫ a = i) :
    S.g ≫ connectingUsing hS i a ha = a ≫ cokernel.π i :=
  g_desc hS _ _

/-- Changing the extension does not change the stable connecting morphism. -/
theorem connectingUsing_stable_eq {S : ShortComplex C} (hS : S.ShortExact)
    {I : C} [Injective I] (i : S.X₁ ⟶ I) (a b : S.X₂ ⟶ I)
    (ha : S.f ≫ a = i) (hb : S.f ≫ b = i) :
    (projectiveStableQuotient (C := C)).map (connectingUsing hS i a ha) =
      (projectiveStableQuotient (C := C)).map (connectingUsing hS i b hb) := by
  let _ := hS.epi_g
  apply sub_eq_zero.mp
  rw [← Functor.map_sub, functor_map_eq_zero_iff]
  have hd : S.f ≫ (a - b) = 0 := by rw [Preadditive.comp_sub, ha, hb, sub_self]
  refine ⟨I, (FrobeniusAbelian.projective_iff_injective I).mpr inferInstance,
    desc hS (a - b) hd, cokernel.π i, ?_⟩
  apply (cancel_epi S.g).1
  simp [Preadditive.comp_sub, Preadditive.sub_comp]

/-- Extending the chosen injective embedding across a short exact sequence. -/
def extension {S : ShortComplex C} (hS : S.ShortExact) :
    S.X₂ ⟶ Injective.under S.X₁ :=
  have := hS.mono_f
  Injective.factorThru (Injective.ι S.X₁) S.f

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem f_extension {S : ShortComplex C} (hS : S.ShortExact) :
    S.f ≫ extension hS = Injective.ι S.X₁ := by
  have := hS.mono_f
  exact Injective.comp_factorThru _ _

/-- The genuine ambient connecting map into the chosen cosyzygy. -/
def connecting {S : ShortComplex C} (hS : S.ShortExact) :
    S.X₃ ⟶ Cosyzygy.obj S.X₁ :=
  connectingUsing hS (Injective.ι S.X₁) (extension hS) (f_extension hS)

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem g_connecting {S : ShortComplex C} (hS : S.ShortExact) :
    S.g ≫ connecting hS = extension hS ≫ cokernel.π (Injective.ι S.X₁) :=
  g_connectingUsing _ _ _ _

/-- Naturality of the stable connecting map for an actual map of short exact
sequences. The discrepancy factors through the target injective object. -/
theorem connecting_naturality {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    (projectiveStableQuotient (C := C)).map (connecting hS) ≫
        (Cosyzygy.functor (C := C)).map ((projectiveStableQuotient (C := C)).map φ.τ₁) =
      (projectiveStableQuotient (C := C)).map φ.τ₃ ≫
        (projectiveStableQuotient (C := C)).map (connecting hT) := by
  let _ := hS.epi_g
  change (projectiveStableQuotient (C := C)).map (connecting hS) ≫
      (projectiveStableQuotient (C := C)).map (Cosyzygy.map φ.τ₁) =
    (projectiveStableQuotient (C := C)).map φ.τ₃ ≫
      (projectiveStableQuotient (C := C)).map (connecting hT)
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply sub_eq_zero.mp
  rw [← Functor.map_sub, functor_map_eq_zero_iff]
  let d := extension hS ≫ Cosyzygy.extension φ.τ₁ - φ.τ₂ ≫ extension hT
  have hd : S.f ≫ d = 0 := by
    dsimp [d]
    rw [Preadditive.comp_sub]
    simp only [← Category.assoc, f_extension]
    rw [← φ.comm₁₂]
    simp
  refine ⟨Injective.under T.X₁,
    (FrobeniusAbelian.projective_iff_injective _).mpr inferInstance,
    desc hS d hd, cokernel.π (Injective.ι T.X₁), ?_⟩
  apply (cancel_epi S.g).1
  simp only [Preadditive.comp_sub, g_connecting_assoc]
  rw [← Category.assoc S.g φ.τ₃ _, ← φ.comm₂₃, Category.assoc, g_connecting]
  simp [d, Preadditive.sub_comp, Category.assoc, Cosyzygy.π_map]

/-- A commutative square in the actual stable quotient can be represented by
a strictly commutative square without changing its stable middle component. -/
theorem strictify_square {S T : ShortComplex C} (hS : S.ShortExact)
    (a : S.X₁ ⟶ T.X₁) (b : S.X₂ ⟶ T.X₂)
    (h : (projectiveStableQuotient (C := C)).map S.f ≫
        (projectiveStableQuotient (C := C)).map b =
      (projectiveStableQuotient (C := C)).map a ≫
        (projectiveStableQuotient (C := C)).map T.f) :
    ∃ b' : S.X₂ ⟶ T.X₂, S.f ≫ b' = a ≫ T.f ∧
      (projectiveStableQuotient (C := C)).map b' =
        (projectiveStableQuotient (C := C)).map b := by
  have := hS.mono_f
  rw [← Functor.map_comp, ← Functor.map_comp, CategoryTheory.Quotient.functor_map_eq_iff] at h
  obtain ⟨P, hP, u, v, huv⟩ := h
  let _ : Injective P := (FrobeniusAbelian.projective_iff_injective P).mp hP
  let u' : S.X₂ ⟶ P := Injective.factorThru u S.f
  have hu' : S.f ≫ u' = u := Injective.comp_factorThru _ _
  refine ⟨b - u' ≫ v, ?_, ?_⟩
  · rw [Preadditive.comp_sub, ← Category.assoc, hu', huv]
    abel
  · rw [Functor.map_sub]
    have hz : (projectiveStableQuotient (C := C)).map (u' ≫ v) = 0 := by
      rw [functor_map_eq_zero_iff]
      exact ⟨P, hP, u', v, rfl⟩
    rw [hz, sub_zero]

/-- Extending a strict square between short exact sequences to a genuine
ambient short-complex morphism using the cokernel universal property. -/
def completeStrictSquare {S T : ShortComplex C}
    (hS : S.ShortExact) (a : S.X₁ ⟶ T.X₁) (b : S.X₂ ⟶ T.X₂)
    (hab : S.f ≫ b = a ≫ T.f) : S ⟶ T where
  τ₁ := a
  τ₂ := b
  τ₃ := desc hS (b ≫ T.g) (by rw [← Category.assoc, hab]; simp)
  comm₁₂ := hab.symm
  comm₂₃ := by simp

/-- The filling property for stable images of short exact sequences, including
the connecting square. This is the core of the eventual TR3 proof. -/
theorem complete_stable_square {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (a : S.X₁ ⟶ T.X₁) (b : S.X₂ ⟶ T.X₂)
    (h : (projectiveStableQuotient (C := C)).map S.f ≫
        (projectiveStableQuotient (C := C)).map b =
      (projectiveStableQuotient (C := C)).map a ≫
        (projectiveStableQuotient (C := C)).map T.f) :
    ∃ c : S.X₃ ⟶ T.X₃,
      (projectiveStableQuotient (C := C)).map S.g ≫
          (projectiveStableQuotient (C := C)).map c =
        (projectiveStableQuotient (C := C)).map b ≫
          (projectiveStableQuotient (C := C)).map T.g ∧
      (projectiveStableQuotient (C := C)).map (connecting hS) ≫
          (Cosyzygy.functor (C := C)).map ((projectiveStableQuotient (C := C)).map a) =
        (projectiveStableQuotient (C := C)).map c ≫
          (projectiveStableQuotient (C := C)).map (connecting hT) := by
  obtain ⟨b', hb', hb⟩ := strictify_square hS a b h
  let φ := completeStrictSquare hS a b' hb'
  refine ⟨φ.τ₃, ?_, connecting_naturality hS hT φ⟩
  rw [← hb, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (projectiveStableQuotient (C := C)).map φ.comm₂₃.symm

/-- Connecting maps for different injective embeddings are identified by the
natural stable cokernel comparison. -/
theorem connectingUsing_comparison {S : ShortComplex C} (hS : S.ShortExact)
    {I J : C} (i : S.X₁ ⟶ I) (j : S.X₁ ⟶ J) [Mono i] [Injective J]
    (a : S.X₂ ⟶ I) (b : S.X₂ ⟶ J)
    (ha : S.f ≫ a = i) (hb : S.f ≫ b = j) :
    (projectiveStableQuotient (C := C)).map (connectingUsing hS i a ha) ≫
        (projectiveStableQuotient (C := C)).map (Cosyzygy.comparison i j) =
      (projectiveStableQuotient (C := C)).map (connectingUsing hS j b hb) := by
  let _ := hS.epi_g
  rw [← Functor.map_comp]
  apply sub_eq_zero.mp
  rw [← Functor.map_sub, functor_map_eq_zero_iff]
  let d := a ≫ Injective.factorThru j i - b
  have hd : S.f ≫ d = 0 := by
    simp [d, Preadditive.comp_sub, ← Category.assoc, ha, hb]
  refine ⟨J, (FrobeniusAbelian.projective_iff_injective J).mpr inferInstance,
    desc hS d hd, cokernel.π j, ?_⟩
  apply (cancel_epi S.g).1
  simp [d, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]

/-- Completing an ambient arrow to a short exact sequence by adding its chosen
injective embedding to the target. -/
def standardSequence {X Y : C} (f : X ⟶ Y) : ShortComplex C :=
  ShortComplex.cokernelSequence (biprod.lift f (Injective.ι X))

theorem standardSequence_shortExact {X Y : C} (f : X ⟶ Y) :
    (standardSequence f).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    dsimp [standardSequence, ShortComplex.cokernelSequence]
    infer_instance
  epi_g := by
    dsimp [standardSequence, ShortComplex.cokernelSequence]
    infer_instance

/-- Adding an injective summand does not change an object in the actual stable
quotient. This is the middle-object comparison used to complete any arrow. -/
def stableBiprodInjectiveIso (Y I : C) [Injective I] :
    (projectiveStableQuotient (C := C)).obj (Y ⊞ I) ≅
      (projectiveStableQuotient (C := C)).obj Y where
  hom := (projectiveStableQuotient (C := C)).map biprod.fst
  inv := (projectiveStableQuotient (C := C)).map biprod.inl
  hom_inv_id := by
    rw [← Functor.map_comp]
    change (projectiveStableQuotient (C := C)).map (biprod.fst ≫ biprod.inl) =
      (projectiveStableQuotient (C := C)).map (𝟙 (Y ⊞ I))
    apply sub_eq_zero.mp
    rw [← Functor.map_sub, functor_map_eq_zero_iff]
    refine ⟨I, (FrobeniusAbelian.projective_iff_injective I).mpr inferInstance,
      -biprod.snd, biprod.inr, ?_⟩
    rw [Preadditive.neg_comp]
    have ht := biprod.total (X := Y) (Y := I)
    rw [← ht]
    abel
  inv_hom_id := by simp [← Functor.map_comp]

/-- The connecting morphism with its codomain expressed as the actual stable
cosyzygy functor's object. -/
def stableConnecting {S : ShortComplex C} (hS : S.ShortExact) :
    (projectiveStableQuotient (C := C)).obj S.X₃ ⟶
      (Cosyzygy.functor (C := C)).obj ((projectiveStableQuotient (C := C)).obj S.X₁) :=
  (projectiveStableQuotient (C := C)).map (connecting hS)

theorem stableConnecting_naturality {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    stableConnecting hS ≫
        (Cosyzygy.functor (C := C)).map ((projectiveStableQuotient (C := C)).map φ.τ₁) =
      (projectiveStableQuotient (C := C)).map φ.τ₃ ≫ stableConnecting hT :=
  connecting_naturality hS hT φ

/-- The first map in the ambient short exact sequence realizing rotation. -/
def rotationFirst {S : ShortComplex C} (hS : S.ShortExact) :
    S.X₂ ⟶ S.X₃ ⊞ Injective.under S.X₁ :=
  biprod.lift S.g (extension hS)

/-- The second map in the ambient short exact sequence realizing rotation.
The minus sign is the sign in mathlib's triangle rotation. -/
def rotationSecond {S : ShortComplex C} (hS : S.ShortExact) :
    S.X₃ ⊞ Injective.under S.X₁ ⟶ Cosyzygy.obj S.X₁ :=
  biprod.desc (connecting hS) (-cokernel.π (Injective.ι S.X₁))

theorem rotation_condition {S : ShortComplex C} (hS : S.ShortExact) :
    rotationFirst hS ≫ rotationSecond hS = 0 := by
  simp [rotationFirst, rotationSecond, biprod.lift_desc, Preadditive.comp_neg]

theorem f_rotationFirst {S : ShortComplex C} (hS : S.ShortExact) :
    S.f ≫ rotationFirst hS = Injective.ι S.X₁ ≫ biprod.inr := by
  ext <;> simp [rotationFirst]

theorem rotationFirst_mono {S : ShortComplex C} (hS : S.ShortExact) :
    Mono (rotationFirst hS) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro W t ht
  have htg : t ≫ S.g = 0 := by
    simpa [rotationFirst] using ht =≫ biprod.fst
  have hta : t ≫ extension hS = 0 := by
    simpa [rotationFirst] using ht =≫ biprod.snd
  let u := KernelFork.IsLimit.lift' hS.fIsKernel t htg
  have hu : u.val ≫ S.f = t := u.property
  have hz : u.val ≫ Injective.ι S.X₁ = 0 := by
    rw [← f_extension hS, ← Category.assoc, hu, hta]
  have hu0 : u.val = 0 := by
    rw [← cancel_mono (Injective.ι S.X₁), hz, zero_comp]
  rw [← hu, hu0, zero_comp]

theorem rotationSecond_epi {S : ShortComplex C} (hS : S.ShortExact) :
    Epi (rotationSecond hS) := by
  have : Epi ((biprod.inr : Injective.under S.X₁ ⟶ _) ≫ rotationSecond hS) := by
    simpa [rotationSecond] using (inferInstance : Epi (-cokernel.π (Injective.ι S.X₁)))
  exact epi_of_epi biprod.inr (rotationSecond hS)

/-- The kernel condition needed to descend out of the rotated cokernel. -/
theorem rotation_desc_condition {S : ShortComplex C} (hS : S.ShortExact)
    {W : C} (k : S.X₃ ⊞ Injective.under S.X₁ ⟶ W)
    (hk : rotationFirst hS ≫ k = 0) :
    Injective.ι S.X₁ ≫ (biprod.inr ≫ k) = 0 := by
  rw [← Category.assoc, ← f_rotationFirst hS, Category.assoc, hk, comp_zero]

/-- The explicit descent making the rotated second map a cokernel. -/
def rotationDesc {S : ShortComplex C} (hS : S.ShortExact)
    {W : C} (k : S.X₃ ⊞ Injective.under S.X₁ ⟶ W)
    (hk : rotationFirst hS ≫ k = 0) : Cosyzygy.obj S.X₁ ⟶ W :=
  -cokernel.desc (Injective.ι S.X₁) (biprod.inr ≫ k) (rotation_desc_condition hS k hk)

theorem rotationSecond_rotationDesc {S : ShortComplex C} (hS : S.ShortExact)
    {W : C} (k : S.X₃ ⊞ Injective.under S.X₁ ⟶ W)
    (hk : rotationFirst hS ≫ k = 0) :
    rotationSecond hS ≫ rotationDesc hS k hk = k := by
  have := hS.epi_g
  apply biprod.hom_ext'
  · apply (cancel_epi S.g).1
    have hsum : S.g ≫ biprod.inl ≫ k + extension hS ≫ biprod.inr ≫ k = 0 := by
      simpa [rotationFirst, biprod.lift_eq, Preadditive.add_comp, Category.assoc] using hk
    simp [rotationSecond, rotationDesc, Preadditive.comp_neg]
    exact neg_eq_iff_add_eq_zero.mpr (by simpa [add_comm] using hsum)
  · simp [rotationSecond, rotationDesc, Preadditive.neg_comp,
      Preadditive.comp_neg]

/-- The genuine cokernel universal property of the rotated ambient sequence. -/
def rotationIsCokernel {S : ShortComplex C} (hS : S.ShortExact) :
    IsColimit (CokernelCofork.ofπ (rotationSecond hS) (rotation_condition hS)) := by
  let _ := rotationSecond_epi hS
  exact CokernelCofork.IsColimit.ofπ' (rotationSecond hS) (rotation_condition hS)
    (fun k hk => ⟨rotationDesc hS k hk, rotationSecond_rotationDesc hS k hk⟩)

/-- The actual short exact sequence realizing the rotation of a stable short
exact triangle. -/
abbrev rotationSequence {S : ShortComplex C} (hS : S.ShortExact) : ShortComplex C :=
  ShortComplex.mk (rotationFirst hS) (rotationSecond hS) (rotation_condition hS)

theorem rotationSequence_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    (rotationSequence hS).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (rotationIsCokernel hS)
  mono_f := rotationFirst_mono hS
  epi_g := rotationSecond_epi hS

/-- The first component of a convenient injective extension for the rotated
short exact sequence. -/
def rotationExtensionLeft {S : ShortComplex C} (hS : S.ShortExact) :
    S.X₃ ⟶ Injective.under S.X₂ :=
  desc hS (Injective.ι S.X₂ - extension hS ≫ Cosyzygy.extension S.f) (by
    simp [Preadditive.comp_sub, ← Category.assoc])

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem g_rotationExtensionLeft {S : ShortComplex C} (hS : S.ShortExact) :
    S.g ≫ rotationExtensionLeft hS =
      Injective.ι S.X₂ - extension hS ≫ Cosyzygy.extension S.f :=
  g_desc _ _ _

/-- A specific extension for rotation whose resulting connecting map has an
explicit signed cosyzygy formula. -/
def rotationExtension {S : ShortComplex C} (hS : S.ShortExact) :
    S.X₃ ⊞ Injective.under S.X₁ ⟶ Injective.under S.X₂ :=
  biprod.desc (rotationExtensionLeft hS) (Cosyzygy.extension S.f)

theorem rotationFirst_rotationExtension {S : ShortComplex C} (hS : S.ShortExact) :
    rotationFirst hS ≫ rotationExtension hS = Injective.ι S.X₂ := by
  simp [rotationFirst, rotationExtension, biprod.lift_desc]

/-- The computed connecting map of rotation, before passage to stable classes. -/
theorem rotation_connectingUsing {S : ShortComplex C} (hS : S.ShortExact) :
    connectingUsing (rotationSequence_shortExact hS) (Injective.ι S.X₂)
      (rotationExtension hS) (rotationFirst_rotationExtension hS) = -Cosyzygy.map S.f := by
  let _ := rotationSecond_epi hS
  apply (cancel_epi (rotationSecond hS)).1
  change (rotationSequence hS).g ≫ connectingUsing _ _ _ _ = _
  rw [g_connectingUsing]
  apply biprod.hom_ext'
  · let _ := hS.epi_g
    apply (cancel_epi S.g).1
    simp [rotationSequence, rotationSecond, rotationExtension, Category.assoc,
      Preadditive.comp_neg, Preadditive.sub_comp]
  · simp [rotationSequence, rotationSecond, rotationExtension, Preadditive.neg_comp,
      Preadditive.comp_neg]

/-- The stable connecting morphism of rotation is the negative cosyzygy image
of the original first morphism. -/
theorem connecting_rotationSequence {S : ShortComplex C} (hS : S.ShortExact) :
    (projectiveStableQuotient (C := C)).map (connecting (rotationSequence_shortExact hS)) =
      -(projectiveStableQuotient (C := C)).map (Cosyzygy.map S.f) := by
  rw [connecting, connectingUsing_stable_eq (rotationSequence_shortExact hS)
    (Injective.ι S.X₂) _ (rotationExtension hS) (f_extension _)
      (rotationFirst_rotationExtension hS)]
  rw [rotation_connectingUsing, Functor.map_neg]

/-- A projective lift of the chosen projective presentation of the last object. -/
def predecessorLift {S : ShortComplex C} (hS : S.ShortExact) :
    Projective.over S.X₃ ⟶ S.X₂ :=
  have := hS.epi_g
  Projective.factorThru (Projective.π S.X₃) S.g

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem predecessorLift_g {S : ShortComplex C} (hS : S.ShortExact) :
    predecessorLift hS ≫ S.g = Projective.π S.X₃ := by
  have := hS.epi_g
  exact Projective.factorThru_comp _ _

/-- The kernel lift relating the projective presentation to the original
short exact sequence. -/
def predecessorKernelLift {S : ShortComplex C} (hS : S.ShortExact) :
    kernel (Projective.π S.X₃) ⟶ S.X₁ :=
  (KernelFork.IsLimit.lift' hS.fIsKernel
    (kernel.ι (Projective.π S.X₃) ≫ predecessorLift hS) (by simp)).val

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem predecessorKernelLift_f {S : ShortComplex C} (hS : S.ShortExact) :
    predecessorKernelLift hS ≫ S.f =
      kernel.ι (Projective.π S.X₃) ≫ predecessorLift hS :=
  (KernelFork.IsLimit.lift' hS.fIsKernel _ _).property

/-- The first map in an ambient short exact predecessor to the given triangle. -/
def predecessorFirst {S : ShortComplex C} (hS : S.ShortExact) :
    kernel (Projective.π S.X₃) ⟶ S.X₁ ⊞ Projective.over S.X₃ :=
  biprod.lift (-predecessorKernelLift hS) (kernel.ι (Projective.π S.X₃))

/-- The second map in the predecessor, with projective summand lifted to the
middle object of the original short exact sequence. -/
def predecessorSecond {S : ShortComplex C} (hS : S.ShortExact) :
    S.X₁ ⊞ Projective.over S.X₃ ⟶ S.X₂ :=
  biprod.desc S.f (predecessorLift hS)

theorem predecessor_condition {S : ShortComplex C} (hS : S.ShortExact) :
    predecessorFirst hS ≫ predecessorSecond hS = 0 := by
  simp [predecessorFirst, predecessorSecond, biprod.lift_desc, Preadditive.neg_comp]

theorem predecessorSecond_epi {S : ShortComplex C} (hS : S.ShortExact) :
    Epi (predecessorSecond hS) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro W t ht
  have hf : S.f ≫ t = 0 := by
    simpa [predecessorSecond] using biprod.inl ≫= ht
  have ha : predecessorLift hS ≫ t = 0 := by
    simpa [predecessorSecond] using biprod.inr ≫= ht
  let u := desc hS t hf
  have hu : S.g ≫ u = t := g_desc _ _ _
  have hp : Projective.π S.X₃ ≫ u = 0 := by
    rw [← predecessorLift_g hS, Category.assoc, hu, ha]
  have hu0 : u = 0 := by
    rw [← cancel_epi (Projective.π S.X₃), hp, comp_zero]
  rw [← hu, hu0, comp_zero]

theorem predecessor_kernel_condition {S : ShortComplex C} (hS : S.ShortExact)
    {W : C} (t : W ⟶ S.X₁ ⊞ Projective.over S.X₃)
    (ht : t ≫ predecessorSecond hS = 0) :
    (t ≫ biprod.snd) ≫ Projective.π S.X₃ = 0 := by
  simpa [predecessorSecond, biprod.desc_eq, Preadditive.comp_add,
    Preadditive.add_comp, Category.assoc] using ht =≫ S.g

def predecessorKernelFactor {S : ShortComplex C} (hS : S.ShortExact)
    {W : C} (t : W ⟶ S.X₁ ⊞ Projective.over S.X₃)
    (ht : t ≫ predecessorSecond hS = 0) : W ⟶ kernel (Projective.π S.X₃) :=
  kernel.lift (Projective.π S.X₃) (t ≫ biprod.snd) (predecessor_kernel_condition hS t ht)

theorem predecessorKernelFactor_first {S : ShortComplex C} (hS : S.ShortExact)
    {W : C} (t : W ⟶ S.X₁ ⊞ Projective.over S.X₃)
    (ht : t ≫ predecessorSecond hS = 0) :
    predecessorKernelFactor hS t ht ≫ predecessorFirst hS = t := by
  have := hS.mono_f
  apply biprod.hom_ext
  · apply (cancel_mono S.f).1
    have hsum : t ≫ biprod.fst ≫ S.f + t ≫ biprod.snd ≫ predecessorLift hS = 0 := by
      simpa [predecessorSecond, biprod.desc_eq, Preadditive.comp_add, Category.assoc] using ht
    simp [predecessorFirst, predecessorKernelFactor, Category.assoc,
      Preadditive.comp_neg, Preadditive.neg_comp]
    exact neg_eq_iff_add_eq_zero.mpr (by simpa [add_comm] using hsum)
  · simp [predecessorFirst, predecessorKernelFactor]

def predecessorIsKernel {S : ShortComplex C} (hS : S.ShortExact) :
    IsLimit (KernelFork.ofι (predecessorFirst hS) (predecessor_condition hS)) := by
  let _ : Mono (predecessorFirst hS) := by
    dsimp [predecessorFirst]
    infer_instance
  exact KernelFork.IsLimit.ofι' (predecessorFirst hS) (predecessor_condition hS)
    (fun t ht => ⟨predecessorKernelFactor hS t ht, predecessorKernelFactor_first hS t ht⟩)

/-- A genuine ambient short exact predecessor exists for every short exact
sequence, using enough projectives rather than a triangulation assumption. -/
abbrev predecessorSequence {S : ShortComplex C} (hS : S.ShortExact) : ShortComplex C :=
  ShortComplex.mk (predecessorFirst hS) (predecessorSecond hS) (predecessor_condition hS)

theorem predecessorSequence_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    (predecessorSequence hS).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (predecessorIsKernel hS)
  mono_f := by
    dsimp [predecessorFirst]
    infer_instance
  epi_g := predecessorSecond_epi hS

/-- The cokernel of the kernel of a projective presentation is the object
presented; the comparison is the ambient universal-property isomorphism. -/
def projectivePresentationCokernelIso (Z : C) :
    cokernel (kernel.ι (Projective.π Z)) ≅ Z :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (kernel.ι (Projective.π Z)))
    (Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι (Projective.π Z)) (kernel.condition _))
      (kernelIsKernel (Projective.π Z)))

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem π_projectivePresentationCokernelIso (Z : C) :
    cokernel.π (kernel.ι (Projective.π Z)) ≫
      (projectivePresentationCokernelIso Z).hom = Projective.π Z := by
  simpa [projectivePresentationCokernelIso] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (kernel.ι (Projective.π Z)))
      (Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι (Projective.π Z)) (kernel.condition _))
        (kernelIsKernel (Projective.π Z))) WalkingParallelPair.one

/-- The stable suspension of the kernel of a projective presentation, with
the explicit presentation comparison exposed for the triangle identities. -/
def kernelSuspensionIso (Z : C) :
    (Cosyzygy.functor (C := C)).obj
        ((projectiveStableQuotient (C := C)).obj (kernel (Projective.π Z))) ≅
      (projectiveStableQuotient (C := C)).obj Z := by
  let _ : Injective (Projective.over Z) :=
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  exact Cosyzygy.stableCokernelIso (Injective.ι (kernel (Projective.π Z)))
    (kernel.ι (Projective.π Z)) ≪≫
      (projectiveStableQuotient (C := C)).mapIso (projectivePresentationCokernelIso Z)

theorem predecessor_connecting_comparison {S : ShortComplex C} (hS : S.ShortExact) :
    stableConnecting (predecessorSequence_shortExact hS) ≫ (kernelSuspensionIso S.X₃).hom =
      (projectiveStableQuotient (C := C)).map S.g := by
  let _ : Injective (Projective.over S.X₃) :=
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  have hp : predecessorFirst hS ≫ biprod.snd = kernel.ι (Projective.π S.X₃) := by
    simp [predecessorFirst]
  change (projectiveStableQuotient (C := C)).map (connecting (predecessorSequence_shortExact hS)) ≫
    ((projectiveStableQuotient (C := C)).map
        (Cosyzygy.comparison (Injective.ι (kernel (Projective.π S.X₃)))
          (kernel.ι (Projective.π S.X₃))) ≫
      (projectiveStableQuotient (C := C)).map (projectivePresentationCokernelIso S.X₃).hom) = _
  rw [← Category.assoc, connecting]
  rw [connectingUsing_comparison (predecessorSequence_shortExact hS) _ _ _ biprod.snd
    (f_extension _) hp]
  rw [← Functor.map_comp]
  congr 1
  let _ := predecessorSecond_epi hS
  apply (cancel_epi (predecessorSecond hS)).1
  change (predecessorSequence hS).g ≫ _ = _
  rw [← Category.assoc, g_connectingUsing]
  simp [predecessorSecond, Category.assoc, biprod.desc_eq, Preadditive.add_comp]

theorem kernelSuspension_connecting {S : ShortComplex C} (hS : S.ShortExact) :
    (kernelSuspensionIso S.X₃).hom ≫ stableConnecting hS =
      (Cosyzygy.functor (C := C)).map
        ((projectiveStableQuotient (C := C)).map (predecessorKernelLift hS)) := by
  let _ : Injective (Projective.over S.X₃) :=
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  let k := kernel.ι (Projective.π S.X₃)
  let i := Injective.ι (kernel (Projective.π S.X₃))
  let a := Injective.factorThru k i ≫ predecessorLift hS ≫ extension hS
  have ha : i ≫ a = predecessorKernelLift hS ≫ Injective.ι S.X₁ := by
    simp only [a, ← Category.assoc, Injective.comp_factorThru]
    rw [← predecessorKernelLift_f hS, Category.assoc, f_extension]
  have hpδ : Projective.π S.X₃ ≫ connecting hS =
      predecessorLift hS ≫ extension hS ≫ cokernel.π (Injective.ι S.X₁) := by
    rw [← predecessorLift_g hS, Category.assoc, g_connecting]
  have hc : Cosyzygy.comparison i k ≫ (projectivePresentationCokernelIso S.X₃).hom ≫
      connecting hS = cokernel.map i (Injective.ι S.X₁) (predecessorKernelLift hS) a ha := by
    apply (cancel_epi (cokernel.π i)).1
    simp only [Cosyzygy.π_comparison_assoc, cokernel.map, cokernel.π_desc]
    dsimp [k]
    rw [π_projectivePresentationCokernelIso_assoc, hpδ]
    simp [a, k, Category.assoc]
  change ((projectiveStableQuotient (C := C)).map (Cosyzygy.comparison i k) ≫
      (projectiveStableQuotient (C := C)).map (projectivePresentationCokernelIso S.X₃).hom) ≫
      (projectiveStableQuotient (C := C)).map (connecting hS) =
    (projectiveStableQuotient (C := C)).map (Cosyzygy.map (predecessorKernelLift hS))
  rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hc]
  exact (Cosyzygy.stable_map_eq (predecessorKernelLift hS) a ha).symm

section WithCompatibleShift

variable [HasShift (projectiveStableCategory C) ℤ]
  (e : Cosyzygy.functor (C := C) ≅ shiftFunctor (projectiveStableCategory C) (1 : ℤ))

open CategoryTheory.Pretriangulated

/-- A genuine mathlib triangle associated to an ambient short exact sequence,
using an explicit identification of the chosen suspension with shift by one. -/
def triangle {S : ShortComplex C} (hS : S.ShortExact) :
    Triangle (projectiveStableCategory C) :=
  Triangle.mk ((projectiveStableQuotient (C := C)).map S.f)
    ((projectiveStableQuotient (C := C)).map S.g)
    (stableConnecting hS ≫
      e.hom.app ((projectiveStableQuotient (C := C)).obj S.X₁))

/-- An ambient map of short exact sequences induces a genuine triangle map. -/
def triangleMap {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) : triangle e hS ⟶ triangle e hT where
  hom₁ := (projectiveStableQuotient (C := C)).map φ.τ₁
  hom₂ := (projectiveStableQuotient (C := C)).map φ.τ₂
  hom₃ := (projectiveStableQuotient (C := C)).map φ.τ₃
  comm₁ := by
    dsimp [triangle, Triangle.mk]
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂]
  comm₂ := by
    dsimp [triangle, Triangle.mk]
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃]
  comm₃ := by
    dsimp [triangle, Triangle.mk]
    rw [Category.assoc, ← e.hom.naturality]
    rw [← Category.assoc, stableConnecting_naturality hS hT φ]
    simp only [Category.assoc]

/-- The class of triangles isomorphic to stable images of ambient short exact
sequences. Triangulation axioms are obligations about this explicit class. -/
def distinguishedTriangles : Set (Triangle (projectiveStableCategory C)) :=
  {T | ∃ (S : ShortComplex C) (hS : S.ShortExact), Nonempty (T ≅ triangle e hS)}

/-- The defining class is closed under triangle isomorphisms. -/
theorem isomorphic_distinguished {T₁ T₂ : Triangle (projectiveStableCategory C)}
    (hT : T₁ ∈ distinguishedTriangles e) (φ : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles e := by
  obtain ⟨S, hS, ⟨ψ⟩⟩ := hT
  exact ⟨S, hS, ⟨φ ≪≫ ψ⟩⟩

/-- The explicit standard triangle completing an ambient morphism. -/
def standardTriangle {X Y : C} (f : X ⟶ Y) : Triangle (projectiveStableCategory C) :=
  Triangle.mk ((projectiveStableQuotient (C := C)).map f)
    ((projectiveStableQuotient (C := C)).map
      ((biprod.inl : Y ⟶ Y ⊞ Injective.under X) ≫ cokernel.π (biprod.lift f (Injective.ι X))))
    (stableConnecting (standardSequence_shortExact f) ≫
      e.hom.app ((projectiveStableQuotient (C := C)).obj X))

/-- The standard triangle is isomorphic to the image of its genuine short exact
sequence, removing the injective summand from the middle object. -/
def standardTriangleIso {X Y : C} (f : X ⟶ Y) :
    standardTriangle e f ≅ triangle e (standardSequence_shortExact f) := by
  let E := stableBiprodInjectiveIso Y (Injective.under X)
  refine Triangle.isoMk _ _ (Iso.refl _) E.symm (Iso.refl _) ?_ ?_ ?_
  · dsimp [standardTriangle, triangle, Triangle.mk, standardSequence,
      ShortComplex.cokernelSequence]
    simp only [Category.id_comp]
    apply (cancel_mono E.hom).1
    simp [E, stableBiprodInjectiveIso, ← Functor.map_comp]
  · dsimp [standardTriangle, triangle, Triangle.mk, standardSequence,
      ShortComplex.cokernelSequence, E, stableBiprodInjectiveIso]
    simp [← Functor.map_comp]
  · dsimp [standardTriangle, triangle, Triangle.mk, standardSequence,
      ShortComplex.cokernelSequence]
    simp

theorem standardTriangle_distinguished {X Y : C} (f : X ⟶ Y) :
    standardTriangle e f ∈ distinguishedTriangles e :=
  ⟨standardSequence f, standardSequence_shortExact f, ⟨standardTriangleIso e f⟩⟩

/-- Every morphism in the actual stable quotient occurs as the first arrow of a
triangle in the explicitly constructed class. This is the existence part of TR1. -/
theorem distinguished_cocone_triangle {X Y : projectiveStableCategory C} (f : X ⟶ Y) :
    ∃ (Z : projectiveStableCategory C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles e := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f', rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
  exact ⟨(standardTriangle e f').obj₃, (standardTriangle e f').mor₂,
    (standardTriangle e f').mor₃, standardTriangle_distinguished e f'⟩

/-- Contractible triangles belong to the explicit class. -/
theorem contractible_distinguished (X : projectiveStableCategory C) :
    contractibleTriangle X ∈ distinguishedTriangles e := by
  obtain ⟨X⟩ := X
  let S := ShortComplex.cokernelSequence (𝟙 X)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _, mono_f := by
        dsimp [S, ShortComplex.cokernelSequence]
        infer_instance }
  have hz : IsZero ((projectiveStableQuotient (C := C)).obj S.X₃) :=
    (projectiveStableQuotient (C := C)).map_isZero (isZero_cokernel_of_epi (𝟙 X))
  refine ⟨S, hS, ⟨Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) hz.isoZero.symm ?_ ?_ ?_⟩⟩
  · dsimp [contractibleTriangle, triangle, Triangle.mk, S, ShortComplex.cokernelSequence]
    simp
  · apply hz.eq_of_tgt
  · apply (isZero_zero (projectiveStableCategory C)).eq_of_src

/-- The filling property for two triangles directly arising from short exact
sequences. Stable square representatives are strictified before descent. -/
theorem complete_shortExact_triangle_morphism {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (a : (triangle e hS).obj₁ ⟶ (triangle e hT).obj₁)
    (b : (triangle e hS).obj₂ ⟶ (triangle e hT).obj₂)
    (h : (triangle e hS).mor₁ ≫ b = a ≫ (triangle e hT).mor₁) :
    ∃ c : (triangle e hS).obj₃ ⟶ (triangle e hT).obj₃,
      (triangle e hS).mor₂ ≫ c = b ≫ (triangle e hT).mor₂ ∧
      (triangle e hS).mor₃ ≫ a⟦1⟧' = c ≫ (triangle e hT).mor₃ := by
  obtain ⟨a', rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective a
  obtain ⟨b', rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective b
  obtain ⟨c, hc₁, hc₂⟩ := complete_stable_square hS hT a' b' h
  refine ⟨(projectiveStableQuotient (C := C)).map c, hc₁, ?_⟩
  dsimp [triangle, Triangle.mk]
  rw [Category.assoc, ← e.hom.naturality]
  rw [← Category.assoc]
  have hc₂' : stableConnecting hS ≫
      (Cosyzygy.functor (C := C)).map ((projectiveStableQuotient (C := C)).map a') =
    (projectiveStableQuotient (C := C)).map c ≫ stableConnecting hT := hc₂
  rw [hc₂']
  simp only [Category.assoc]

/-- TR3 for the entire isomorphism-closed class of stable short exact triangles. -/
theorem complete_distinguished_triangle_morphism
    (T₁ T₂ : Triangle (projectiveStableCategory C))
    (h₁ : T₁ ∈ distinguishedTriangles e) (h₂ : T₂ ∈ distinguishedTriangles e)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (h : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨S, hS, ⟨E₁⟩⟩ := h₁
  obtain ⟨T, hT, ⟨E₂⟩⟩ := h₂
  let a' := E₁.inv.hom₁ ≫ a ≫ E₂.hom.hom₁
  let b' := E₁.inv.hom₂ ≫ b ≫ E₂.hom.hom₂
  have h' : (triangle e hS).mor₁ ≫ b' = a' ≫ (triangle e hT).mor₁ := by
    dsimp [a', b']
    rw [← Category.assoc, E₁.inv.comm₁, Category.assoc, ← Category.assoc T₁.mor₁,
      h, Category.assoc, E₂.hom.comm₁]
    simp only [Category.assoc]
  obtain ⟨c', hc₁, hc₂⟩ := complete_shortExact_triangle_morphism e hS hT a' b' h'
  let ψ := Triangle.homMk (triangle e hS) (triangle e hT) a' b' c' h' hc₁ hc₂
  let φ : T₁ ⟶ T₂ := E₁.hom ≫ ψ ≫ E₂.inv
  have ha : φ.hom₁ = a := by
    simp [φ, ψ, a', Category.assoc]
  have hb : φ.hom₂ = b := by
    simp [φ, ψ, b', Category.assoc]
  exact ⟨φ.hom₃, by simpa only [hb] using φ.comm₂,
    by simpa only [ha] using φ.comm₃⟩

/-- The rotated stable triangle is identified with a genuine ambient short
exact sequence, with the connecting morphism computed including its sign. -/
def rotationTriangleIso {S : ShortComplex C} (hS : S.ShortExact) :
    (triangle e hS).rotate ≅ triangle e (rotationSequence_shortExact hS) := by
  let E := stableBiprodInjectiveIso S.X₃ (Injective.under S.X₁)
  refine Triangle.isoMk _ _ (Iso.refl _) E.symm
    (e.symm.app ((projectiveStableQuotient (C := C)).obj S.X₁)) ?_ ?_ ?_
  · dsimp [Triangle.rotate, triangle, Triangle.mk]
    simp only [Category.id_comp]
    apply (cancel_mono E.hom).1
    simp [E, stableBiprodInjectiveIso, rotationFirst, ← Functor.map_comp]
  · dsimp [Triangle.rotate, triangle, Triangle.mk]
    simp [E, stableBiprodInjectiveIso, rotationSecond, stableConnecting,
      ← Functor.map_comp]
  · dsimp [Triangle.rotate, triangle, Triangle.mk]
    have hc : stableConnecting (rotationSequence_shortExact hS) =
        -(Cosyzygy.functor (C := C)).map ((projectiveStableQuotient (C := C)).map S.f) :=
      connecting_rotationSequence hS
    rw [hc]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    rw [e.hom.naturality]
    simp

/-- The explicit distinguished class is closed under forward rotation. -/
theorem rotate_distinguished {T : Triangle (projectiveStableCategory C)}
    (hT : T ∈ distinguishedTriangles e) : T.rotate ∈ distinguishedTriangles e := by
  obtain ⟨S, hS, ⟨E⟩⟩ := hT
  exact ⟨rotationSequence hS, rotationSequence_shortExact hS,
    ⟨(CategoryTheory.Pretriangulated.rotate (projectiveStableCategory C)).mapIso E ≪≫
      rotationTriangleIso e hS⟩⟩

/-- A genuine short exact predecessor rotates to the original stable triangle.
This supplies inverse rotation without assuming a pretriangulation. -/
def predecessorRotationIso {S : ShortComplex C} (hS : S.ShortExact) :
    (triangle e (predecessorSequence_shortExact hS)).rotate ≅ triangle e hS := by
  let _ : Injective (Projective.over S.X₃) :=
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  let _ : (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).Additive :=
    Functor.additive_of_iso e
  let E := stableBiprodInjectiveIso S.X₁ (Projective.over S.X₃)
  refine Triangle.isoMk _ _ E (Iso.refl _)
    (e.symm.app ((projectiveStableQuotient (C := C)).obj (kernel (Projective.π S.X₃))) ≪≫
      kernelSuspensionIso S.X₃) ?_ ?_ ?_
  · dsimp [Triangle.rotate, triangle, Triangle.mk]
    simp only [Category.comp_id]
    change (projectiveStableQuotient (C := C)).map (predecessorSecond hS) =
      (projectiveStableQuotient (C := C)).map biprod.fst ≫
        (projectiveStableQuotient (C := C)).map S.f
    have hz : (projectiveStableQuotient (C := C)).map
        ((biprod.snd : S.X₁ ⊞ Projective.over S.X₃ ⟶ _) ≫ predecessorLift hS) = 0 := by
      rw [functor_map_eq_zero_iff]
      exact ⟨Projective.over S.X₃, inferInstance, biprod.snd, predecessorLift hS, rfl⟩
    simp [predecessorSecond, biprod.desc_eq, Functor.map_add, hz, Functor.map_comp]
  · dsimp [Triangle.rotate, triangle, Triangle.mk]
    simpa [Category.assoc] using predecessor_connecting_comparison hS
  · dsimp [Triangle.rotate, triangle, Triangle.mk]
    have hr : (projectiveStableQuotient (C := C)).map (predecessorFirst hS) ≫ E.hom =
        -(projectiveStableQuotient (C := C)).map (predecessorKernelLift hS) := by
      simp [E, stableBiprodInjectiveIso, predecessorFirst, ← Functor.map_comp]
    rw [Preadditive.neg_comp, ← Functor.map_comp, hr, Functor.map_neg, neg_neg]
    rw [Category.assoc, ← Category.assoc (kernelSuspensionIso S.X₃).hom,
      kernelSuspension_connecting hS]
    rw [e.hom.naturality]
    simp

/-- Every member of the constructed class has a distinguished predecessor
under the rotation equivalence. -/
theorem exists_distinguished_predecessor {T : Triangle (projectiveStableCategory C)}
    (hT : T ∈ distinguishedTriangles e) :
    ∃ U : Triangle (projectiveStableCategory C),
      U ∈ distinguishedTriangles e ∧ Nonempty (U.rotate ≅ T) := by
  obtain ⟨S, hS, ⟨E⟩⟩ := hT
  exact ⟨triangle e (predecessorSequence_shortExact hS),
    ⟨predecessorSequence hS, predecessorSequence_shortExact hS, ⟨Iso.refl _⟩⟩,
    ⟨predecessorRotationIso e hS ≪≫ E.symm⟩⟩

variable [∀ n : ℤ, (shiftFunctor (projectiveStableCategory C) n).Additive]

/-- TR2 in both directions for the explicit distinguished class. -/
theorem rotate_distinguished_iff (T : Triangle (projectiveStableCategory C)) :
    T ∈ distinguishedTriangles e ↔ T.rotate ∈ distinguishedTriangles e := by
  refine ⟨rotate_distinguished e, ?_⟩
  intro hT
  obtain ⟨U, hU, ⟨E⟩⟩ := exists_distinguished_predecessor e hT
  let E' : U ≅ T :=
    (CategoryTheory.Pretriangulated.rotate (projectiveStableCategory C)).preimageIso E
  exact isomorphic_distinguished e hU E'.symm

/-- The canonical pretriangulated structure, with all axioms proved from
ambient Frobenius exact sequences and the actual stable quotient. -/
@[instance_reducible]
def pretriangulated : CategoryTheory.Pretriangulated (projectiveStableCategory C) where
  distinguishedTriangles := distinguishedTriangles e
  isomorphic_distinguished := by
    intro T₁ h₁ T₂ E
    exact isomorphic_distinguished e h₁ E
  contractible_distinguished := contractible_distinguished e
  distinguished_cocone_triangle := distinguished_cocone_triangle e
  rotate_distinguished_triangle := rotate_distinguished_iff e
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism e

end WithCompatibleShift

end PretriangulatedV2.StableCategory.FrobeniusTriangles
