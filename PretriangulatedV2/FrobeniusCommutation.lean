import PretriangulatedV2.Cosyzygy
import PretriangulatedV2.StableFunctor
import PretriangulatedV2.Heller
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Canonical commutation with cosyzygy

An ambient additive autoequivalence descends to an autoequivalence of the
actual projective stable quotient. Its commutation with cosyzygy is constructed
from injective presentations and the preservation of their cokernels. No
commutation isomorphism is supplied as a hypothesis.
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.StableCategory.FrobeniusCommutation

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  (S : C ≌ C) [S.functor.Additive]

/-- The ambient unit descends componentwise to the projective stable quotient. -/
def stableUnitIso :
    𝟭 (projectiveStableCategory C) ≅ stableFunctor S.functor ⋙ stableFunctor S.inverse :=
  NatIso.ofComponents
    (fun X => (projectiveStableQuotient (C := C)).mapIso (S.unitIso.app X.as)) (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
      change (projectiveStableQuotient (C := C)).map f ≫
          (projectiveStableQuotient (C := C)).map (S.unitIso.hom.app Y) =
        (projectiveStableQuotient (C := C)).map (S.unitIso.hom.app X) ≫
          (projectiveStableQuotient (C := C)).map (S.inverse.map (S.functor.map f))
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (projectiveStableQuotient (C := C)).congr_map (S.unitIso.hom.naturality f))

/-- The ambient counit descends componentwise to the stable quotient. -/
def stableCounitIso :
    stableFunctor S.inverse ⋙ stableFunctor S.functor ≅ 𝟭 (projectiveStableCategory C) :=
  NatIso.ofComponents
    (fun X => (projectiveStableQuotient (C := C)).mapIso (S.counitIso.app X.as)) (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
      change (projectiveStableQuotient (C := C)).map (S.functor.map (S.inverse.map f)) ≫
          (projectiveStableQuotient (C := C)).map (S.counitIso.hom.app Y) =
        (projectiveStableQuotient (C := C)).map (S.counitIso.hom.app X) ≫
          (projectiveStableQuotient (C := C)).map f
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (projectiveStableQuotient (C := C)).congr_map (S.counitIso.hom.naturality f))

/-- The actual descended autoequivalence, including its ambient-induced inverse. -/
def stableEquivalence : projectiveStableCategory C ≌ projectiveStableCategory C where
  functor := stableFunctor S.functor
  inverse := stableFunctor S.inverse
  unitIso := stableUnitIso S
  counitIso := stableCounitIso S
  functor_unitIso_comp := by
    rintro ⟨X⟩
    change (projectiveStableQuotient (C := C)).map (S.functor.map (S.unitIso.hom.app X)) ≫
        (projectiveStableQuotient (C := C)).map (S.counitIso.hom.app (S.functor.obj X)) =
      𝟙 ((projectiveStableQuotient (C := C)).obj (S.functor.obj X))
    have h := S.functor_unitIso_comp X
    change S.functor.map (S.unitIso.hom.app X) ≫
      S.counitIso.hom.app (S.functor.obj X) = 𝟙 (S.functor.obj X) at h
    rw [← Functor.map_comp, h]
    exact (projectiveStableQuotient (C := C)).map_id _

instance stableFunctor_isEquivalence : (stableFunctor S.functor).IsEquivalence :=
  (stableEquivalence S).isEquivalence_functor

variable [FrobeniusAbelian C]

/-- Cosyzygy of `S X` is compared with the cokernel of `S` applied to the
injective presentation of `X`, and then with `S` of its cosyzygy. -/
def sigmaComponent (X : C) :
    (projectiveStableQuotient (C := C)).obj (Cosyzygy.obj (S.functor.obj X)) ≅
      (projectiveStableQuotient (C := C)).obj (S.functor.obj (Cosyzygy.obj X)) :=
  Cosyzygy.stableCokernelIso (Injective.ι (S.functor.obj X))
    (S.functor.map (Injective.ι X)) ≪≫
      (projectiveStableQuotient (C := C)).mapIso
        (PreservesCokernel.iso S.functor (Injective.ι X)).symm

/-- The canonical component is the stable class of the injective-presentation
comparison followed by the ordinary cokernel comparison for `S`. -/
theorem sigmaComponent_hom (X : C) :
    (sigmaComponent S X).hom =
      (projectiveStableQuotient (C := C)).map
        (Cosyzygy.comparison (Injective.ι (S.functor.obj X))
          (S.functor.map (Injective.ι X))) ≫
      (projectiveStableQuotient (C := C)).map
        (cokernelComparison (Injective.ι X) S.functor) := by
  simp only [sigmaComponent, Iso.trans_hom, Cosyzygy.stableCokernelIso,
    Functor.mapIso_hom, Iso.symm_hom, PreservesCokernel.iso_inv]

/-- The component comparison is natural for ambient morphisms. -/
theorem sigmaComponent_naturality {X Y : C} (f : X ⟶ Y) :
    (projectiveStableQuotient (C := C)).map (Cosyzygy.map (S.functor.map f)) ≫
        (sigmaComponent S Y).hom =
      (sigmaComponent S X).hom ≫
        (projectiveStableQuotient (C := C)).map (S.functor.map (Cosyzygy.map f)) := by
  have hb : S.functor.map (Injective.ι X) ≫ S.functor.map (Cosyzygy.extension f) =
      S.functor.map f ≫ S.functor.map (Injective.ι Y) := by
    rw [← S.functor.map_comp, Cosyzygy.ι_extension, S.functor.map_comp]
  have hc := Cosyzygy.comparison_naturality
    (Injective.ι (S.functor.obj X)) (Injective.ι (S.functor.obj Y))
    (S.functor.map (Injective.ι X)) (S.functor.map (Injective.ι Y))
    (S.functor.map f) (Cosyzygy.extension (S.functor.map f))
    (S.functor.map (Cosyzygy.extension f)) (Cosyzygy.ι_extension _) hb
  have hn := cokernel_map_comp_cokernelComparison (Injective.ι X) S.functor
    (Injective.ι Y) f (Cosyzygy.extension f) (Cosyzygy.ι_extension f)
  simp only [sigmaComponent, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesCokernel.iso_inv, Cosyzygy.stableCokernelIso, Cosyzygy.map]
  rw [← Category.assoc, hc, Category.assoc, ← Functor.map_comp, hn, Functor.map_comp]
  rw [Category.assoc]

/-- The paper's canonical commutation `Ω⁻¹ S ≅ S Ω⁻¹`, expressed using
Lean's left-to-right functor composition, on the actual stable quotient. -/
def sigma :
    stableFunctor S.functor ⋙ Cosyzygy.functor ≅
      Cosyzygy.functor ⋙ stableFunctor S.functor :=
  NatIso.ofComponents (fun X => sigmaComponent S X.as) (by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨f, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
    exact sigmaComponent_naturality S f)

@[simp]
theorem sigma_hom_app (X : C) :
    (sigma S).hom.app ((projectiveStableQuotient (C := C)).obj X) =
      (sigmaComponent S X).hom := rfl

@[simp]
theorem sigma_inv_app (X : C) :
    (sigma S).inv.app ((projectiveStableQuotient (C := C)).obj X) =
      (sigmaComponent S X).inv := rfl

/-- Heller parameters on the actual quotient now use the constructed canonical
commutation. This is the parameter type, not a classification or triangulation. -/
abbrev StableHellerParameter : Type _ :=
  HellerParameter (Cosyzygy.functor (C := C)) (stableFunctor S.functor) (sigma S)

end PretriangulatedV2.StableCategory.FrobeniusCommutation
