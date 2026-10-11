import PretriangulatedV2.Frobenius

/-!
# Cosyzygy on the actual projective stable quotient

An object is embedded into a chosen ambient injective object and its cosyzygy
is the ambient cokernel. A morphism is extended across these embeddings using
injectivity. The extension is not unique, but its cokernel map has a unique
class in the quotient by ambient projective objects.
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open PretriangulatedV2.IdealQuotient

namespace PretriangulatedV2.StableCategory.Cosyzygy

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

/-- Two extensions of one map induce the same map in the stable quotient.
The difference factors through the injective target of the embeddings. -/
theorem cokernelMap_stable_eq {X Y I J : C} (i : X ⟶ I) (j : Y ⟶ J)
    [Injective J] (f : X ⟶ Y) (a b : I ⟶ J)
    (ha : i ≫ a = f ≫ j) (hb : i ≫ b = f ≫ j) :
    (projectiveStableQuotient (C := C)).map (cokernel.map i j f a ha) =
      (projectiveStableQuotient (C := C)).map (cokernel.map i j f b hb) := by
  apply sub_eq_zero.mp
  rw [← Functor.map_sub, functor_map_eq_zero_iff]
  have hd : i ≫ (a - b) = 0 := by
    rw [Preadditive.comp_sub, ha, hb, sub_self]
  refine ⟨J, (FrobeniusAbelian.projective_iff_injective J).mpr inferInstance,
    cokernel.desc i (a - b) hd, cokernel.π j, ?_⟩
  apply (cancel_epi (cokernel.π i)).1
  simp [cokernel.map, Preadditive.comp_sub, Preadditive.sub_comp]

/-- The ambient cokernel of the chosen injective embedding. -/
abbrev obj (X : C) : C := cokernel (Injective.ι X)

/-- An injective extension of a morphism to the chosen injective objects. -/
def extension {X Y : C} (f : X ⟶ Y) : Injective.under X ⟶ Injective.under Y :=
  Injective.factorThru (f ≫ Injective.ι Y) (Injective.ι X)

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem ι_extension {X Y : C} (f : X ⟶ Y) :
    Injective.ι X ≫ extension f = f ≫ Injective.ι Y :=
  Injective.comp_factorThru _ _

/-- The ambient cokernel map; its stable class is independent of the extension. -/
def map {X Y : C} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  cokernel.map (Injective.ι X) (Injective.ι Y) f (extension f) (ι_extension f)

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem π_map {X Y : C} (f : X ⟶ Y) :
    cokernel.π (Injective.ι X) ≫ map f = extension f ≫ cokernel.π (Injective.ι Y) :=
  cokernel.π_desc _ _ _

/-- Comparison with any chosen extension of the same morphism. -/
theorem stable_map_eq {X Y : C} (f : X ⟶ Y)
    (a : Injective.under X ⟶ Injective.under Y)
    (ha : Injective.ι X ≫ a = f ≫ Injective.ι Y) :
    (projectiveStableQuotient (C := C)).map (map f) =
      (projectiveStableQuotient (C := C)).map
        (cokernel.map (Injective.ι X) (Injective.ι Y) f a ha) :=
  cokernelMap_stable_eq _ _ f _ _ (ι_extension f) ha

@[simp]
theorem stable_map_id (X : C) :
    (projectiveStableQuotient (C := C)).map (map (𝟙 X)) =
      𝟙 ((projectiveStableQuotient (C := C)).obj (obj X)) := by
  rw [stable_map_eq (𝟙 X) (𝟙 _) (by simp)]
  simp [obj]

theorem stable_map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (projectiveStableQuotient (C := C)).map (map (f ≫ g)) =
      (projectiveStableQuotient (C := C)).map (map f) ≫
        (projectiveStableQuotient (C := C)).map (map g) := by
  rw [stable_map_eq (f ≫ g) (extension f ≫ extension g) (by simp)]
  rw [← Functor.map_comp]
  congr 1
  apply (cancel_epi (cokernel.π (Injective.ι X))).1
  simp [obj, map, cokernel.map, Category.assoc]

theorem stable_map_add {X Y : C} (f g : X ⟶ Y) :
    (projectiveStableQuotient (C := C)).map (map (f + g)) =
      (projectiveStableQuotient (C := C)).map (map f) +
        (projectiveStableQuotient (C := C)).map (map g) := by
  rw [stable_map_eq (f + g) (extension f + extension g) (by
    simp [Preadditive.comp_add, Preadditive.add_comp])]
  rw [← Functor.map_add]
  congr 1
  apply (cancel_epi (cokernel.π (Injective.ι X))).1
  simp [map, cokernel.map, Preadditive.comp_add, Preadditive.add_comp]

/-- The ambient cosyzygy construction is a functor after taking stable classes. -/
def toStable : C ⥤ projectiveStableCategory C where
  obj X := (projectiveStableQuotient (C := C)).obj (obj X)
  map f := (projectiveStableQuotient (C := C)).map (map f)
  map_id := stable_map_id
  map_comp := stable_map_comp

instance toStable_additive : (toStable (C := C)).Additive where
  map_add := by
    intro X Y f g
    exact stable_map_add f g

/-- Morphisms factoring through ambient projectives are killed by cosyzygy. -/
theorem toStable_map_eq_zero_of_factorsThrough {X Y : C} (f : X ⟶ Y)
    (hf : FactorsThrough (projectiveObjects : C → Prop) f) :
    (toStable (C := C)).map f = 0 := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  let _ : Injective P := (FrobeniusAbelian.projective_iff_injective P).mp hP
  let a' : Injective.under X ⟶ P := Injective.factorThru a (Injective.ι X)
  have ha' : Injective.ι X ≫ a' = a := Injective.comp_factorThru _ _
  change (projectiveStableQuotient (C := C)).map (map f) = 0
  rw [stable_map_eq f (a' ≫ b ≫ Injective.ι Y) (by simp [← Category.assoc, ha', hab])]
  have hzero : cokernel.map (Injective.ι X) (Injective.ι Y) f
      (a' ≫ b ≫ Injective.ι Y) (by simp [← Category.assoc, ha', hab]) = 0 := by
    apply (cancel_epi (cokernel.π (Injective.ι X))).1
    simp [cokernel.map]
  simp only [hzero, Functor.map_zero]

theorem toStable_respects_relation {X Y : C} (f g : X ⟶ Y)
    (h : factorRelation (projectiveObjects : C → Prop) f g) :
    (toStable (C := C)).map f = (toStable (C := C)).map g := by
  apply sub_eq_zero.mp
  rw [← Functor.map_sub]
  exact toStable_map_eq_zero_of_factorsThrough (f - g) h

/-- Cosyzygy is an additive endofunctor of the actual quotient by projectives. -/
def functor : projectiveStableCategory C ⥤ projectiveStableCategory C :=
  CategoryTheory.Quotient.lift (factorRelation (projectiveObjects : C → Prop))
    (toStable (C := C)) (fun _ _ f g h => toStable_respects_relation f g h)

@[simp]
theorem functor_obj (X : C) :
    (functor (C := C)).obj ((projectiveStableQuotient (C := C)).obj X) =
      (projectiveStableQuotient (C := C)).obj (obj X) := rfl

@[simp]
theorem functor_map {X Y : C} (f : X ⟶ Y) :
    (functor (C := C)).map ((projectiveStableQuotient (C := C)).map f) =
      (projectiveStableQuotient (C := C)).map (map f) := rfl

theorem functor_spec : projectiveStableQuotient (C := C) ⋙ functor = toStable :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance functor_additive : (functor (C := C)).Additive := by
  have : (projectiveStableQuotient (C := C) ⋙ functor).Additive := by
    rw [functor_spec]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp (projectiveStableQuotient (C := C)) functor

/-- Every ambient map of cosyzygies has a stable preimage. This uses the
projectivity of the chosen injective object and normality of the target mono. -/
theorem exists_stable_preimage {X Y : C} (t : obj X ⟶ obj Y) :
    ∃ f : X ⟶ Y, (projectiveStableQuotient (C := C)).map (map f) =
      (projectiveStableQuotient (C := C)).map t := by
  let _ : Projective (Injective.under X) :=
    (FrobeniusAbelian.projective_iff_injective _).mpr inferInstance
  let a := Projective.factorThru (cokernel.π (Injective.ι X) ≫ t)
    (cokernel.π (Injective.ι Y))
  have ha : a ≫ cokernel.π (Injective.ι Y) = cokernel.π (Injective.ι X) ≫ t :=
    Projective.factorThru_comp _ _
  have hz : (Injective.ι X ≫ a) ≫ cokernel.π (Injective.ι Y) = 0 := by
    rw [Category.assoc, ha]
    simp
  let f := Abelian.monoLift (Injective.ι Y) (Injective.ι X ≫ a) hz
  have hf : Injective.ι X ≫ a = f ≫ Injective.ι Y :=
    (Abelian.monoLift_comp _ _ _).symm
  refine ⟨f, ?_⟩
  rw [stable_map_eq f a hf]
  congr 1
  apply (cancel_epi (cokernel.π (Injective.ι X))).1
  simpa [cokernel.map] using ha

/-- If a cosyzygy map is stably zero, the original morphism factors through
the chosen injective object, which is projective in a Frobenius category. -/
theorem factorsThrough_of_stable_map_eq_zero {X Y : C} (f : X ⟶ Y)
    (h : (projectiveStableQuotient (C := C)).map (map f) = 0) :
    FactorsThrough (projectiveObjects : C → Prop) f := by
  rw [functor_map_eq_zero_iff] at h
  obtain ⟨P, hP, a, b, hab⟩ := h
  let _ : Projective P := hP
  let b' := Projective.factorThru b (cokernel.π (Injective.ι Y))
  have hb' : b' ≫ cokernel.π (Injective.ι Y) = b := Projective.factorThru_comp _ _
  let d := extension f - cokernel.π (Injective.ι X) ≫ a ≫ b'
  have hd : d ≫ cokernel.π (Injective.ι Y) = 0 := by
    dsimp [d]
    rw [Preadditive.sub_comp]
    simp only [Category.assoc, hb']
    rw [hab, π_map, sub_self]
  let c := Abelian.monoLift (Injective.ι Y) d hd
  have hc : c ≫ Injective.ι Y = d := Abelian.monoLift_comp _ _ _
  have hf : Injective.ι X ≫ c = f := by
    apply (cancel_mono (Injective.ι Y)).1
    rw [Category.assoc, hc]
    simp [d, Preadditive.comp_sub]
  exact ⟨Injective.under X,
    (FrobeniusAbelian.projective_iff_injective _).mpr inferInstance,
    Injective.ι X, c, hf⟩

instance functor_full : (functor (C := C)).Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ t
    obtain ⟨t', ht'⟩ := (projectiveStableQuotient (C := C)).map_surjective t
    obtain ⟨f, hf⟩ := exists_stable_preimage t'
    exact ⟨(projectiveStableQuotient (C := C)).map f, hf.trans ht'⟩

instance functor_faithful : (functor (C := C)).Faithful where
  map_injective := by
    rintro ⟨X⟩ ⟨Y⟩ f g h
    obtain ⟨f', rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
    obtain ⟨g', rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective g
    apply sub_eq_zero.mp
    rw [← Functor.map_sub, functor_map_eq_zero_iff]
    apply factorsThrough_of_stable_map_eq_zero
    change (toStable (C := C)).map (f' - g') = 0
    rw [Functor.map_sub]
    exact sub_eq_zero.mpr h

/-- Comparing two injective presentations of the same object. -/
def comparison {X I J : C} (i : X ⟶ I) (j : X ⟶ J) [Mono i] [Injective J] :
    cokernel i ⟶ cokernel j :=
  cokernel.map i j (𝟙 X) (Injective.factorThru j i) (by simp)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
@[reassoc (attr := simp)]
theorem π_comparison {X I J : C} (i : X ⟶ I) (j : X ⟶ J)
    [Mono i] [Injective J] :
    cokernel.π i ≫ comparison i j = Injective.factorThru j i ≫ cokernel.π j :=
  cokernel.π_desc _ _ _

/-- Different ambient injective presentations give isomorphic objects in the
stable quotient. Neither embedding is assumed to be a chosen presentation. -/
def stableCokernelIso {X I J : C} (i : X ⟶ I) (j : X ⟶ J)
    [Mono i] [Mono j] [Injective I] [Injective J] :
    (projectiveStableQuotient (C := C)).obj (cokernel i) ≅
      (projectiveStableQuotient (C := C)).obj (cokernel j) where
  hom := (projectiveStableQuotient (C := C)).map (comparison i j)
  inv := (projectiveStableQuotient (C := C)).map (comparison j i)
  hom_inv_id := by
    rw [← Functor.map_comp]
    have h : i ≫ (Injective.factorThru j i ≫ Injective.factorThru i j) = (𝟙 X) ≫ i := by
      simp
    have hc : comparison i j ≫ comparison j i =
        cokernel.map i i (𝟙 X)
          (Injective.factorThru j i ≫ Injective.factorThru i j) h := by
      apply (cancel_epi (cokernel.π i)).1
      simp [comparison, cokernel.map, Category.assoc]
    rw [hc, cokernelMap_stable_eq i i (𝟙 X) _ (𝟙 I) h (by simp)]
    simp
  inv_hom_id := by
    rw [← Functor.map_comp]
    have h : j ≫ (Injective.factorThru i j ≫ Injective.factorThru j i) = (𝟙 X) ≫ j := by
      simp
    have hc : comparison j i ≫ comparison i j =
        cokernel.map j j (𝟙 X)
          (Injective.factorThru i j ≫ Injective.factorThru j i) h := by
      apply (cancel_epi (cokernel.π j)).1
      simp [comparison, cokernel.map, Category.assoc]
    rw [hc, cokernelMap_stable_eq j j (𝟙 X) _ (𝟙 J) h (by simp)]
    simp

/-- Comparing injective presentations commutes with maps after passage to the
stable quotient. Thus comparison is natural, as well as invertible. -/
theorem comparison_naturality {X Y I₁ I₂ J₁ J₂ : C}
    (i₁ : X ⟶ I₁) (i₂ : Y ⟶ I₂) (j₁ : X ⟶ J₁) (j₂ : Y ⟶ J₂)
    [Mono i₁] [Mono i₂] [Injective J₁] [Injective J₂]
    (f : X ⟶ Y) (a : I₁ ⟶ I₂) (b : J₁ ⟶ J₂)
    (ha : i₁ ≫ a = f ≫ i₂) (hb : j₁ ≫ b = f ≫ j₂) :
    (projectiveStableQuotient (C := C)).map (cokernel.map i₁ i₂ f a ha) ≫
        (projectiveStableQuotient (C := C)).map (comparison i₂ j₂) =
      (projectiveStableQuotient (C := C)).map (comparison i₁ j₁) ≫
        (projectiveStableQuotient (C := C)).map (cokernel.map j₁ j₂ f b hb) := by
  have hl : i₁ ≫ (a ≫ Injective.factorThru j₂ i₂) = f ≫ j₂ := by
    rw [← Category.assoc, ha, Category.assoc, Injective.comp_factorThru]
  have hr : i₁ ≫ (Injective.factorThru j₁ i₁ ≫ b) = f ≫ j₂ := by
    rw [← Category.assoc, Injective.comp_factorThru, hb]
  have hleft : cokernel.map i₁ i₂ f a ha ≫ comparison i₂ j₂ =
      cokernel.map i₁ j₂ f (a ≫ Injective.factorThru j₂ i₂) hl := by
    apply (cancel_epi (cokernel.π i₁)).1
    simp [comparison, cokernel.map, Category.assoc]
  have hright : comparison i₁ j₁ ≫ cokernel.map j₁ j₂ f b hb =
      cokernel.map i₁ j₂ f (Injective.factorThru j₁ i₁ ≫ b) hr := by
    apply (cancel_epi (cokernel.π i₁)).1
    simp [comparison, cokernel.map, Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, hleft, hright]
  exact cokernelMap_stable_eq i₁ j₂ f _ _ hl hr

/-- The kernel of an ambient projective presentation has cosyzygy stably
isomorphic to the object presented. -/
def cosyzygyKernelProjectiveIso (Y : C) :
    (projectiveStableQuotient (C := C)).obj (obj (kernel (Projective.π Y))) ≅
      (projectiveStableQuotient (C := C)).obj Y := by
  let _ : Injective (Projective.over Y) :=
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  let e : cokernel (kernel.ι (Projective.π Y)) ≅ Y :=
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (kernel.ι (Projective.π Y)))
      (Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι (Projective.π Y)) (kernel.condition _))
        (kernelIsKernel (Projective.π Y)))
  exact stableCokernelIso (Injective.ι (kernel (Projective.π Y)))
    (kernel.ι (Projective.π Y)) ≪≫ (projectiveStableQuotient (C := C)).mapIso e

instance functor_essSurj : (functor (C := C)).EssSurj where
  mem_essImage := by
    rintro ⟨Y⟩
    exact ⟨(projectiveStableQuotient (C := C)).obj (kernel (Projective.π Y)),
      ⟨cosyzygyKernelProjectiveIso Y⟩⟩

/-- The actual cosyzygy functor is an autoequivalence of the stable quotient. -/
instance functor_isEquivalence : (functor (C := C)).IsEquivalence where

/-- The cosyzygy autoequivalence, with an inverse supplied by the proven
fully faithful and essentially surjective construction. -/
def equivalence : projectiveStableCategory C ≌ projectiveStableCategory C :=
  (functor (C := C)).asEquivalence

end PretriangulatedV2.StableCategory.Cosyzygy
