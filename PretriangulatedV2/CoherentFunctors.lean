import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.WeakKernels
import Mathlib.Algebra.Category.Grp.EpiMono
import PretriangulatedV2.Frobenius

/-!
# Coherent contravariant additive functors

The objects here are actual group-valued presheaves. A presentation is the
cokernel universal property for `Hom(-, C₁) → Hom(-, C₀) → F`, rather than an
abstract replacement category or an assumed abelian/Frobenius structure.

This module proves the weak-kernel criterion for `mod(C)` to be abelian and
the Frobenius conclusion for pretriangulated `C`. With split idempotents it
constructs the Yoneda equivalence with projective-injective functors, and it
extends an additive autoequivalence by inverse precomposition. The Heller
classification and its transport are separate mathematical obligations.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open ZeroObject

namespace PretriangulatedV2.CoherentFunctors

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The ambient category of contravariant group-valued functors. -/
abbrev Presheaf := Cᵒᵖ ⥤ AddCommGrpCat.{v}

/-- A finite presentation by two representable functors, including its cokernel
universal property. In an additive category a finite sum of representables is
again representable, so these are the paper's presentations. -/
structure Presentation (F : Presheaf C) where
  relations : C
  generators : C
  differential : relations ⟶ generators
  projection : preadditiveYoneda.obj generators ⟶ F
  condition : preadditiveYoneda.map differential ≫ projection = 0
  isColimit : IsColimit (CokernelCofork.ofπ projection condition)

/-- Coherence is a property of genuine presheaves, given by existence of a
finite representable presentation. Additivity will follow from the
presentation. -/
def coherent : ObjectProperty (Presheaf C) := fun F => Nonempty (Presentation C F)

/-- The category `mod(C)` of coherent functors, with all natural transformations
as its morphisms. -/
abbrev Mod := (coherent C).FullSubcategory

variable {C}

instance preadditiveYoneda_additive :
    (preadditiveYoneda : C ⥤ Presheaf C).Additive where
  map_add := by
    intro X Y f g
    ext Z x
    dsimp [preadditiveYoneda, preadditiveYonedaObj] at x ⊢
    apply comp_add

instance preadditiveYoneda_preservesBinaryBiproducts :
    PreservesBinaryBiproducts (preadditiveYoneda : C ⥤ Presheaf C) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

namespace Presentation

variable {F : Presheaf C} (P : Presentation C F)

instance projection_epi : Epi P.projection := epi_of_isColimit_cofork P.isColimit

include P in
/-- A cokernel of a map between additive presheaves is additive. Here the
epimorphism from a representable supplies the needed cancellation. -/
theorem additive : F.Additive := by
  constructor
  intro X Y f g
  apply (cancel_epi (P.projection.app X)).1
  rw [Preadditive.comp_add, ← P.projection.naturality f,
    ← P.projection.naturality g, ← P.projection.naturality (f + g),
    Functor.map_add, Preadditive.add_comp]

/-- The presentation gives the exact sequence in the paper's definition. -/
theorem exact :
    (ShortComplex.mk (preadditiveYoneda.map P.differential)
      P.projection P.condition).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P.isColimit

/-- Objectwise exactness of the finite presentation, stated in elementary
group language for subsequent weak-kernel arguments. -/
theorem exactAt (X : Cᵒᵖ) (x : X.unop ⟶ P.generators)
    (hx : P.projection.app X x = 0) :
    ∃ y : X.unop ⟶ P.relations, y ≫ P.differential = x := by
  have h := P.exact.map_of_epi_of_preservesCokernel ((evaluation _ _).obj X)
    inferInstance inferInstance
  exact (ShortComplex.ab_exact_iff _).mp h x hx

end Presentation

instance additive_obj (F : Mod C) : F.obj.Additive := F.property.some.additive

/-- A representable has the trivial presentation with zero differential. -/
def representablePresentation (X : C) : Presentation C (preadditiveYoneda.obj X) where
  relations := X
  generators := X
  differential := 0
  projection := 𝟙 _
  condition := by simp
  isColimit := by
    apply CokernelCofork.IsColimit.ofId
    simp

theorem coherent_representable (X : C) : coherent C (preadditiveYoneda.obj X) :=
  ⟨representablePresentation X⟩

/-- The Yoneda embedding into the actual coherent-functor category. -/
def yoneda : C ⥤ Mod C :=
  (coherent C).lift preadditiveYoneda coherent_representable

instance yoneda_full : (yoneda (C := C)).Full := by
  unfold yoneda
  infer_instance

instance yoneda_faithful : (yoneda (C := C)).Faithful := by
  unfold yoneda
  infer_instance

instance yoneda_additive : (yoneda (C := C)).Additive := by
  unfold yoneda
  infer_instance

namespace Presentation

variable {F G : Presheaf C}

/-- Transport a genuine finite presentation across a natural isomorphism. -/
def ofIso (P : Presentation C F) (e : F ≅ G) : Presentation C G where
  relations := P.relations
  generators := P.generators
  differential := P.differential
  projection := P.projection ≫ e.hom
  condition := by simp [← Category.assoc, P.condition]
  isColimit := IsColimit.ofIsoColimit P.isColimit (Cofork.ext e)

end Presentation

instance coherent_closedUnderIsomorphisms :
    (coherent C).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨h.some.ofIso e⟩

section AdditiveYonedaLemma

variable {F : Presheaf C} [F.Additive]

/-- An element of an additive functor gives a group-valued natural
transformation from a representable, by the Yoneda formula. -/
def homOfElement (X : C) (x : F.obj (op X)) : preadditiveYoneda.obj X ⟶ F where
  app Y := AddCommGrpCat.ofHom
    { toFun := fun g => F.map g.op x
      map_zero' := by simp
      map_add' := by
        intro f g
        dsimp [preadditiveYoneda, preadditiveYonedaObj] at f g ⊢
        rw [Functor.map_add]
        rfl }
  naturality Y Z f := by
    ext g
    dsimp [preadditiveYoneda, preadditiveYonedaObj] at g ⊢
    rw [Functor.map_comp]
    rfl

@[simp]
lemma homOfElement_id (X : C) (x : F.obj (op X)) :
    (homOfElement X x).app (op X) (𝟙 X) = x := by
  change F.map (𝟙 (op X)) x = x
  simp

omit [F.Additive] in
/-- A natural transformation out of a representable is determined by its
value at the identity. -/
lemma representable_hom_ext (X : C)
    {α β : preadditiveYoneda.obj X ⟶ F}
    (h : α.app (op X) (𝟙 X) = β.app (op X) (𝟙 X)) : α = β := by
  ext Y f
  have hα := congrArg (fun k => k (𝟙 X)) (α.naturality f.op)
  have hβ := congrArg (fun k => k (𝟙 X)) (β.naturality f.op)
  change α.app Y (f ≫ 𝟙 X) = F.map f.op (α.app (op X) (𝟙 X)) at hα
  change β.app Y (f ≫ 𝟙 X) = F.map f.op (β.app (op X) (𝟙 X)) at hβ
  simpa only [Category.comp_id] using hα.trans ((congrArg (F.map f.op) h).trans hβ.symm)

/-- The additive Yoneda lemma, with actual natural transformations and group
elements as its two sides. -/
def yonedaEquiv (X : C) : (preadditiveYoneda.obj X ⟶ F) ≃ F.obj (op X) where
  toFun α := α.app (op X) (𝟙 X)
  invFun := homOfElement X
  left_inv _ := representable_hom_ext X (homOfElement_id X _)
  right_inv := homOfElement_id X

/-- Representables lift through epimorphisms of additive presheaves. -/
theorem representable_lifting {F G : Presheaf C} [F.Additive]
    (X : C) (p : F ⟶ G) [Epi p] (f : preadditiveYoneda.obj X ⟶ G) :
    ∃ g : preadditiveYoneda.obj X ⟶ F, g ≫ p = f := by
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective (p.app (op X))).mp
    inferInstance (f.app (op X) (𝟙 X))
  refine ⟨homOfElement X x, ?_⟩
  apply representable_hom_ext X
  change p.app (op X) ((homOfElement X x).app (op X) (𝟙 X)) = _
  rw [homOfElement_id]
  exact hx

end AdditiveYonedaLemma

section Cokernels

variable [HasBinaryBiproducts C]

/-- Cokernels of maps of finitely presented additive presheaves are finitely
presented. The relations consist of the target's relations and a lift of the
source's generators. -/
theorem coherent_cokernel {F G : Presheaf C} (a : F ⟶ G)
    (hF : coherent C F) (hG : coherent C G) : coherent C (cokernel a) := by
  let P := hF.some
  let Q := hG.some
  let : F.Additive := P.additive
  obtain ⟨t, ht⟩ := representable_lifting P.generators Q.projection (P.projection ≫ a)
  let l := preadditiveYoneda.preimage t
  have hl : preadditiveYoneda.map l = t := preadditiveYoneda.map_preimage t
  let d : Q.relations ⊞ P.generators ⟶ Q.generators := biprod.desc Q.differential l
  let p := Q.projection ≫ cokernel.π a
  have w : preadditiveYoneda.map d ≫ p = 0 := by
    ext W x
    dsimp [d, p, preadditiveYoneda, preadditiveYonedaObj] at x ⊢
    have h₁ := congrArg (fun k => k.app W (x ≫ biprod.fst)) Q.condition
    have h₂ := congrArg (fun k => k.app W (x ≫ biprod.snd))
      (show preadditiveYoneda.map l ≫ Q.projection ≫ cokernel.π a = 0 by
        rw [hl, ← Category.assoc, ht]
        simp)
    change (cokernel.π a).app W
      (Q.projection.app W (x ≫ biprod.desc Q.differential l)) = 0
    rw [biprod.desc_eq, Preadditive.comp_add, map_add, map_add]
    change Q.projection.app W ((x ≫ biprod.fst) ≫ Q.differential) = 0 at h₁
    change (cokernel.π a).app W (Q.projection.app W ((x ≫ biprod.snd) ≫ l)) = 0 at h₂
    simp only [Category.assoc] at h₁ h₂
    rw [h₁, map_zero, h₂, zero_add]
  refine ⟨{
    relations := Q.relations ⊞ P.generators
    generators := Q.generators
    differential := d
    projection := p
    condition := w
    isColimit := ?_ }⟩
  apply CokernelCofork.IsColimit.ofπ' p w
  intro Z k hk
  have hk₁ : preadditiveYoneda.map Q.differential ≫ k = 0 := by
    have hh := congrArg (fun z => preadditiveYoneda.map biprod.inl ≫ z) hk
    simpa only [← Category.assoc, ← Functor.map_comp, d, biprod.inl_desc, comp_zero] using hh
  have hk₂ : t ≫ k = 0 := by
    have hh := congrArg (fun z => preadditiveYoneda.map biprod.inr ≫ z) hk
    simpa only [← Category.assoc, ← Functor.map_comp, d, biprod.inr_desc, hl, comp_zero] using hh
  let q : G ⟶ Z := Q.isColimit.desc (CokernelCofork.ofπ k hk₁)
  have hq : Q.projection ≫ q = k := Q.isColimit.fac _ WalkingParallelPair.one
  have haq : a ≫ q = 0 := by
    apply (cancel_epi P.projection).1
    rw [comp_zero, ← Category.assoc, ← ht, Category.assoc, hq, hk₂]
  refine ⟨cokernel.desc a q haq, ?_⟩
  dsimp [p]
  rw [Category.assoc, cokernel.π_desc, hq]

instance coherent_closedUnderCokernels : (coherent C).IsClosedUnderCokernels where
  cokernels_le := by
    intro F h
    rcases h with ⟨a, k, hk, hF, hG⟩
    exact (coherent C).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel a) hk)
      (coherent_cokernel a hF hG)

end Cokernels

section Projectives

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- The zero presheaf has a presentation by the identity of a representable. -/
def zeroPresentation : Presentation C (0 : Presheaf C) where
  relations := 0
  generators := 0
  differential := 𝟙 _
  projection := 0
  condition := by simp
  isColimit := by
    apply CokernelCofork.IsColimit.ofEpiOfIsZero
    · infer_instance
    · exact isZero_zero (Presheaf C)

instance coherent_containsZero : (coherent C).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, ⟨zeroPresentation⟩⟩

/-- The inclusion preserves epimorphisms because coherent functors are closed
under ambient cokernels. -/
instance inclusion_preservesEpimorphisms : (coherent C).ι.PreservesEpimorphisms :=
  (coherent C).preservesEpimorphisms_ι_of_isNormalMonoCategory

/-- Representables are projective in the coherent-functor category. -/
instance representable_projective (X : C) : Projective ((yoneda (C := C)).obj X) where
  factors {F G} f e _ := by
    have : Epi e.hom := (coherent C).ι.map_epi e
    obtain ⟨g, hg⟩ := representable_lifting X e.hom f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

/-- Every coherent functor has an epimorphism from a representable. -/
def projectivePresentation (F : Mod C) : ProjectivePresentation F where
  p := (yoneda (C := C)).obj F.property.some.generators
  f := ObjectProperty.homMk F.property.some.projection
  epi := (coherent C).ι.epi_of_epi_map F.property.some.projection_epi

instance enoughProjectives : EnoughProjectives (Mod C) where
  presentation F := ⟨projectivePresentation F⟩

/-- Split idempotents ensure that every projective coherent functor is
representable: split the idempotent induced by a section of its presentation. -/
theorem projective_iff_representable [IsIdempotentComplete C] (F : Mod C) :
    Projective F ↔ ∃ X : C, Nonempty (F ≅ (yoneda (C := C)).obj X) := by
  constructor
  · intro hF
    let Z := F.property.some.generators
    let p : (yoneda (C := C)).obj Z ⟶ F := (projectivePresentation F).f
    let i := Projective.factorThru (𝟙 F) p
    have hip : i ≫ p = 𝟙 F := Projective.factorThru_comp _ _
    let e := p ≫ i
    let h := (yoneda (C := C)).preimage e
    have hh : (yoneda (C := C)).map h = e := (yoneda (C := C)).map_preimage _
    have hid : h ≫ h = h := by
      apply (yoneda (C := C)).map_injective
      rw [Functor.map_comp, hh]
      dsimp [e]
      rw [Category.assoc, ← Category.assoc i p i, hip]
      simp
    obtain ⟨Y, j, r, hjr, hrj⟩ := IsIdempotentComplete.idempotents_split Z h hid
    refine ⟨Y, ⟨{
      hom := i ≫ (yoneda (C := C)).map r
      inv := (yoneda (C := C)).map j ≫ p
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩⟩
    · calc
        (i ≫ yoneda.map r) ≫ (yoneda.map j ≫ p) = i ≫ yoneda.map (r ≫ j) ≫ p := by
          simp [Functor.map_comp, Category.assoc]
        _ = i ≫ e ≫ p := by rw [hrj, hh]
        _ = (i ≫ p) ≫ (i ≫ p) := by simp [e, Category.assoc]
        _ = 𝟙 F := by rw [hip]; simp
    · calc
        (yoneda.map j ≫ p) ≫ (i ≫ yoneda.map r) = yoneda.map j ≫ e ≫ yoneda.map r := by
          simp [e, Category.assoc]
        _ = yoneda.map (j ≫ h ≫ r) := by rw [← hh]; simp [Functor.map_comp]
        _ = yoneda.map (j ≫ r) := by
          simp only [← hrj, ← Category.assoc, hjr, Category.id_comp]
        _ = 𝟙 _ := by
          rw [hjr]
          exact (yoneda (C := C)).map_id Y
  · rintro ⟨X, ⟨e⟩⟩
    exact Projective.of_iso e.symm inferInstance

end Projectives

omit [Preadditive C] in
/-- Exactness in the group-valued functor category can be checked by an
elementwise image/kernel calculation at each object. -/
theorem exact_of_pointwise {F G H : Presheaf C} (s : F ⟶ G) (k : G ⟶ H)
    (w : s ≫ k = 0)
    (h : ∀ (W : Cᵒᵖ) (x : G.obj W), k.app W x = 0 →
      ∃ y : F.obj W, s.app W y = x) :
    (ShortComplex.mk s k w).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  apply (NatTrans.epi_iff_epi_app _).mpr
  intro W
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro y
  have hy := congrArg (fun z => z.app W y) (kernel.condition k)
  change k.app W ((kernel.ι k).app W y) = 0 at hy
  obtain ⟨x, hx⟩ := h W ((kernel.ι k).app W y) hy
  refine ⟨x, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective ((kernel.ι k).app W)).mp inferInstance
  have hf := congrArg (fun z => z.app W x) (kernel.lift_ι k s w)
  change (kernel.ι k).app W ((kernel.lift k s w).app W x) = s.app W x at hf
  exact hf.trans hx

omit [Preadditive C] in
/-- Every element annihilated by a natural transformation lifts to the
objectwise value of its categorical kernel. -/
theorem kernel_element {F G : Presheaf C} (k : F ⟶ G) (W : Cᵒᵖ)
    (x : F.obj W) (hx : k.app W x = 0) :
    ∃ y : (kernel k).obj W, (kernel.ι k).app W y = x := by
  let S := ShortComplex.mk (kernel.ι k) k (kernel.condition k)
  have h : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel k)
  have h' := h.map_of_mono_of_preservesKernel ((evaluation _ _).obj W)
    inferInstance inferInstance
  exact (ShortComplex.ab_exact_iff _).mp h' x hx

section Kernels

variable [HasBinaryBiproducts C] [HasWeakKernels C]

omit [HasBinaryBiproducts C] in
/-- A weak kernel in `C` becomes an exact image/kernel pair after applying the
contravariant additive Yoneda embedding. -/
theorem weakKernel_yoneda_exact {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (preadditiveYoneda.map (weakKernel.ι f))
      (preadditiveYoneda.map f) (by simp [← Functor.map_comp])).Exact := by
  apply exact_of_pointwise
  intro W x hx
  change x ≫ f = 0 at hx
  exact ⟨weakKernel.lift f x hx, weakKernel.lift_ι f x hx⟩

/-- Kernels of maps from representables to coherent functors are coherent.
The two weak kernels used below supply the generators and relations. -/
theorem coherent_kernel_from_representable {F : Presheaf C} (hF : coherent C F)
    (X : C) (k : preadditiveYoneda.obj X ⟶ F) : coherent C (kernel k) := by
  let P := hF.some
  obtain ⟨t, ht⟩ := representable_lifting X P.projection k
  let l := preadditiveYoneda.preimage t
  have hl : preadditiveYoneda.map l ≫ P.projection = k := by
    dsimp [l]
    rw [Functor.map_preimage]
    exact ht
  let d : X ⊞ P.relations ⟶ P.generators := biprod.desc l (-P.differential)
  let r : weakKernel d ⟶ X := weakKernel.ι d ≫ biprod.fst
  have hr : r ≫ l = weakKernel.ι d ≫ biprod.snd ≫ P.differential := by
    apply sub_eq_zero.mp
    calc
      r ≫ l - weakKernel.ι d ≫ biprod.snd ≫ P.differential =
          weakKernel.ι d ≫ d := by
        simp [r, d, biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg,
          sub_eq_add_neg, Category.assoc]
      _ = 0 := weakKernel.condition d
  have w : preadditiveYoneda.map r ≫ k = 0 := by
    rw [← hl, ← Category.assoc, ← Functor.map_comp, hr]
    simp only [Functor.map_comp, Category.assoc, P.condition, comp_zero]
  have he : (ShortComplex.mk (preadditiveYoneda.map r) k w).Exact := by
    apply exact_of_pointwise
    intro W x hx
    obtain ⟨y, hy⟩ := P.exactAt W (x ≫ l) (by
      have h := congrArg (fun z => z.app W x) hl
      change P.projection.app W (x ≫ l) = k.app W x at h
      exact h.trans hx)
    have hd : biprod.lift x y ≫ d = 0 := by
      dsimp [d]
      rw [biprod.lift_desc, Preadditive.comp_neg, hy, add_neg_cancel]
    refine ⟨weakKernel.lift d (biprod.lift x y) hd, ?_⟩
    change weakKernel.lift d (biprod.lift x y) hd ≫ r = x
    dsimp [r]
    rw [← Category.assoc, weakKernel.lift_ι, biprod.lift_fst]
  let p := kernel.lift k (preadditiveYoneda.map r) w
  have hp : Epi p := he.epi_kernelLift
  have w' : preadditiveYoneda.map (weakKernel.ι r) ≫ p = 0 := by
    apply (cancel_mono (kernel.ι k)).1
    simp [p, ← Functor.map_comp]
  have he' : (ShortComplex.mk (preadditiveYoneda.map (weakKernel.ι r)) p w').Exact := by
    apply exact_of_pointwise
    intro W x hx
    have h := congrArg (fun z => z.app W x) (kernel.lift_ι k (preadditiveYoneda.map r) w)
    change (kernel.ι k).app W (p.app W x) = x ≫ r at h
    have hrx : x ≫ r = 0 := by rw [← h, hx]; exact map_zero _
    exact ⟨weakKernel.lift r x hrx, weakKernel.lift_ι r x hrx⟩
  exact ⟨{
    relations := weakKernel r
    generators := weakKernel d
    differential := weakKernel.ι r
    projection := p
    condition := w'
    isColimit := he'.gIsCokernel }⟩

/-- With weak kernels in `C`, coherent functors are closed under kernels.
This descends the kernel along a representable epimorphism, presenting the
desired kernel as a cokernel of two kernels out of a representable. -/
theorem coherent_kernel {F G : Presheaf C} (a : F ⟶ G)
    (hF : coherent C F) (hG : coherent C G) : coherent C (kernel a) := by
  let P := hF.some
  let f := P.projection
  let m := kernel.map f (f ≫ a) (𝟙 _) a (by simp)
  let q := kernel.map (f ≫ a) a f (𝟙 _) (by simp)
  have hmι : m ≫ kernel.ι (f ≫ a) = kernel.ι f := by simp [m]
  have hqι : q ≫ kernel.ι a = kernel.ι (f ≫ a) ≫ f := by simp [q]
  have w : m ≫ q = 0 := by
    apply (cancel_mono (kernel.ι a)).1
    simp [m, q]
  have hq : Epi q := by
    apply (NatTrans.epi_iff_epi_app _).mpr
    intro W
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro y
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective (f.app W)).mp
      inferInstance ((kernel.ι a).app W y)
    have hy := congrArg (fun z => z.app W y) (kernel.condition a)
    change a.app W ((kernel.ι a).app W y) = 0 at hy
    obtain ⟨z, hz⟩ := kernel_element (f ≫ a) W x (by
      change a.app W (f.app W x) = 0
      rw [hx]
      exact hy)
    refine ⟨z, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective ((kernel.ι a).app W)).mp inferInstance
    have h := congrArg (fun t => t.app W z) hqι
    change (kernel.ι a).app W (q.app W z) = f.app W ((kernel.ι (f ≫ a)).app W z) at h
    exact h.trans ((congrArg (f.app W) hz).trans hx)
  have he : (ShortComplex.mk m q w).Exact := by
    apply exact_of_pointwise
    intro W x hx
    have h := congrArg (fun t => t.app W x) hqι
    change (kernel.ι a).app W (q.app W x) = f.app W ((kernel.ι (f ≫ a)).app W x) at h
    have hz : f.app W ((kernel.ι (f ≫ a)).app W x) = 0 := by
      rw [← h, hx]
      exact map_zero _
    obtain ⟨y, hy⟩ := kernel_element f W ((kernel.ι (f ≫ a)).app W x) hz
    refine ⟨y, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective ((kernel.ι (f ≫ a)).app W)).mp inferInstance
    have hm := congrArg (fun t => t.app W y) hmι
    change (kernel.ι (f ≫ a)).app W (m.app W y) = (kernel.ι f).app W y at hm
    exact hm.trans hy
  have hkf : coherent C (kernel f) := coherent_kernel_from_representable hF _ f
  have hkfa : coherent C (kernel (f ≫ a)) := coherent_kernel_from_representable hG _ (f ≫ a)
  exact (coherent C).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel m) he.gIsCokernel)
    (coherent_cokernel m hkf hkfa)

instance coherent_closedUnderKernels : (coherent C).IsClosedUnderKernels where
  kernels_le := by
    intro F h
    rcases h with ⟨a, k, hk, hF, hG⟩
    exact (coherent C).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel a) hk)
      (coherent_kernel a hF hG)

end Kernels

section FiniteProducts

variable [HasBinaryBiproducts C]

/-- Representable functors take a biproduct to a biproduct; hence a natural
transformation out of it is determined by the two summand inclusions. -/
theorem representable_biprod_hom_ext {X Y : C} {F : Presheaf C}
    {a b : preadditiveYoneda.obj (X ⊞ Y) ⟶ F}
    (h₁ : preadditiveYoneda.map biprod.inl ≫ a = preadditiveYoneda.map biprod.inl ≫ b)
    (h₂ : preadditiveYoneda.map biprod.inr ≫ a = preadditiveYoneda.map biprod.inr ≫ b) : a = b := by
  apply (cancel_epi (Functor.mapBiprod preadditiveYoneda X Y).inv).1
  rw [Functor.mapBiprod_inv]
  apply biprod.hom_ext' <;> simp [h₁, h₂]

/-- Finite presentations are closed under binary biproducts. -/
theorem coherent_biprod {F G : Presheaf C}
    (hF : coherent C F) (hG : coherent C G) : coherent C (F ⊞ G) := by
  let P := hF.some
  let Q := hG.some
  let d := biprod.map P.differential Q.differential
  let p := biprod.lift (preadditiveYoneda.map biprod.fst ≫ P.projection)
    (preadditiveYoneda.map biprod.snd ≫ Q.projection)
  have hp₁ : preadditiveYoneda.map biprod.inl ≫ p = P.projection ≫ biprod.inl := by
    apply biprod.hom_ext <;> simp only [p, Category.assoc, biprod.lift_fst, biprod.lift_snd,
      biprod.inl_fst, biprod.inl_snd, comp_zero, Category.comp_id]
    all_goals simp [← Category.assoc, ← Functor.map_comp]
  have hp₂ : preadditiveYoneda.map biprod.inr ≫ p = Q.projection ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp only [p, Category.assoc, biprod.lift_fst, biprod.lift_snd,
      biprod.inr_fst, biprod.inr_snd, comp_zero, Category.comp_id]
    all_goals simp [← Category.assoc, ← Functor.map_comp]
  have hp : Epi p := by
    have h : (Functor.mapBiprod preadditiveYoneda P.generators Q.generators).inv ≫ p =
        biprod.map P.projection Q.projection := by
      apply biprod.hom_ext' <;> simp [hp₁, hp₂]
    exact epi_of_epi_fac h
  have w : preadditiveYoneda.map d ≫ p = 0 := by
    apply representable_biprod_hom_ext
    · rw [← Category.assoc, ← Functor.map_comp]
      simp only [d, biprod.inl_map, Functor.map_comp]
      rw [Category.assoc, hp₁, ← Category.assoc, P.condition, zero_comp, comp_zero]
    · rw [← Category.assoc, ← Functor.map_comp]
      simp only [d, biprod.inr_map, Functor.map_comp]
      rw [Category.assoc, hp₂, ← Category.assoc, Q.condition, zero_comp, comp_zero]
  refine ⟨{
    relations := P.relations ⊞ Q.relations
    generators := P.generators ⊞ Q.generators
    differential := d
    projection := p
    condition := w
    isColimit := ?_ }⟩
  apply CokernelCofork.IsColimit.ofπ' p w
  intro Z k hk
  have hk₁ : preadditiveYoneda.map P.differential ≫
      (preadditiveYoneda.map biprod.inl ≫ k) = 0 := by
    have h := congrArg (fun t => preadditiveYoneda.map biprod.inl ≫ t) hk
    simp only [← Category.assoc, ← Functor.map_comp, d, biprod.inl_map] at h
    simpa only [Functor.map_comp, Category.assoc, comp_zero] using h
  have hk₂ : preadditiveYoneda.map Q.differential ≫
      (preadditiveYoneda.map biprod.inr ≫ k) = 0 := by
    have h := congrArg (fun t => preadditiveYoneda.map biprod.inr ≫ t) hk
    simp only [← Category.assoc, ← Functor.map_comp, d, biprod.inr_map] at h
    simpa only [Functor.map_comp, Category.assoc, comp_zero] using h
  let a := P.isColimit.desc (CokernelCofork.ofπ _ hk₁)
  let b := Q.isColimit.desc (CokernelCofork.ofπ _ hk₂)
  have ha : P.projection ≫ a = preadditiveYoneda.map biprod.inl ≫ k :=
    P.isColimit.fac _ WalkingParallelPair.one
  have hb : Q.projection ≫ b = preadditiveYoneda.map biprod.inr ≫ k :=
    Q.isColimit.fac _ WalkingParallelPair.one
  refine ⟨biprod.desc a b, ?_⟩
  apply representable_biprod_hom_ext
  · rw [← Category.assoc, hp₁, Category.assoc, biprod.inl_desc, ha]
  · rw [← Category.assoc, hp₂, Category.assoc, biprod.inr_desc, hb]

instance coherent_closedUnderBinaryProducts : (coherent C).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro F ⟨p⟩
    let X := p.diag.obj ⟨WalkingPair.left⟩
    let Y := p.diag.obj ⟨WalkingPair.right⟩
    have h := (IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag)
      p.toLimitPresentation.cone).2 p.isLimit
    exact (coherent C).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) h)
      (coherent_biprod (p.prop_diag_obj ⟨WalkingPair.left⟩)
        (p.prop_diag_obj ⟨WalkingPair.right⟩))

instance coherent_closedUnderFiniteProducts [HasZeroObject C] :
    (coherent C).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

end FiniteProducts

/-- The weak-kernel criterion for the coherent-functor category to be
abelian, proved by the concrete closure calculations above. -/
instance mod_abelian [HasZeroObject C] [HasBinaryBiproducts C] [HasWeakKernels C] :
    Abelian (Mod C) := inferInstanceAs (Abelian (coherent C).FullSubcategory)

section Autoequivalences

variable (e : C ≌ C) [e.functor.Additive]

/-- Precomposition with the inverse equivalence carries a representable to
the representable of the corresponding image object. -/
def yonedaPrecompIso :
    preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj e.inverse.op ≅
      e.functor ⋙ preadditiveYoneda := by
  let : e.symm.functor.Additive := by
    change e.inverse.Additive
    infer_instance
  exact NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun W => (e.symm.toAdjunction.homAddEquiv W.unop X).toAddCommGrpIso)
      (fun f => by
        ext x
        exact e.symm.toAdjunction.homEquiv_naturality_left f.unop x))
    (fun f => by
      ext W x
      exact e.symm.toAdjunction.homEquiv_naturality_right x f)

/-- An additive equivalence of the source preserves the finite representable
presentation property under inverse precomposition. -/
theorem coherent_precomp {F : Presheaf C} (hF : coherent C F) :
    coherent C (e.inverse.op ⋙ F) := by
  let P := hF.some
  let E := e.op.congrLeft (E := AddCommGrpCat.{v})
  let α := yonedaPrecompIso e
  have hnat : preadditiveYoneda.map (e.functor.map P.differential) ≫
      (α.app P.generators).inv =
      (α.app P.relations).inv ≫ E.functor.map (preadditiveYoneda.map P.differential) := by
    exact α.inv.naturality P.differential
  let mapped := (CokernelCofork.ofπ P.projection P.condition).map E.functor
  have hcol : IsColimit mapped :=
    CokernelCofork.mapIsColimit _ P.isColimit E.functor
  have hiff : ∀ ⦃Z : Presheaf C⦄ (φ : E.functor.obj (preadditiveYoneda.obj P.generators) ⟶ Z),
      E.functor.map (preadditiveYoneda.map P.differential) ≫ φ = 0 ↔
      preadditiveYoneda.map (e.functor.map P.differential) ≫
        (α.app P.generators).inv ≫ φ = 0 := by
    intro Z φ
    rw [← Category.assoc, hnat, Category.assoc]
    exact ⟨fun h => by rw [h, comp_zero], fun h =>
      (cancel_epi (α.app P.relations).inv).1 (by simpa using h)⟩
  exact ⟨{
    relations := e.functor.obj P.relations
    generators := e.functor.obj P.generators
    differential := e.functor.map P.differential
    projection := (α.app P.generators).inv ≫ E.functor.map P.projection
    condition := by
      rw [← Category.assoc, hnat, Category.assoc, ← E.functor.map_comp, P.condition]
      simp
    isColimit := CokernelCofork.isColimitOfIsColimitOfIff hcol
      (preadditiveYoneda.map (e.functor.map P.differential))
      (α.app P.generators).symm hiff }⟩

/-- The autoequivalence induced on coherent functors by inverse
precomposition. This is an actual equivalence of the full functor subcategory. -/
def autoequivalence : Mod C ≌ Mod C := by
  let : e.symm.functor.Additive := by
    change e.inverse.Additive
    infer_instance
  let E := e.op.congrLeft (E := AddCommGrpCat.{v})
  let L := (coherent C).lift ((coherent C).ι ⋙ E.functor)
    (fun F => coherent_precomp e F.property)
  let R := (coherent C).lift ((coherent C).ι ⋙ E.inverse)
    (fun F => coherent_precomp e.symm F.property)
  exact {
    functor := L
    inverse := R
    unitIso := NatIso.ofComponents
      (fun F => ObjectProperty.isoMk (coherent C) (E.unitIso.app F.obj))
      (fun f => ObjectProperty.hom_ext _ (E.unitIso.hom.naturality f.hom))
    counitIso := NatIso.ofComponents
      (fun F => ObjectProperty.isoMk (coherent C) (E.counitIso.app F.obj))
      (fun f => ObjectProperty.hom_ext _ (E.counitIso.hom.naturality f.hom))
    functor_unitIso_comp := fun F => ObjectProperty.hom_ext _ (E.functor_unitIso_comp F.obj) }

instance autoequivalence_functor_additive : (autoequivalence e).functor.Additive := by
  dsimp [autoequivalence]
  infer_instance

/-- The induced equivalence restricts on the Yoneda image to the original
equivalence, as a natural isomorphism. -/
def yonedaAutoequivalenceIso :
    yoneda ⋙ (autoequivalence e).functor ≅ e.functor ⋙ yoneda :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk (coherent C) ((yonedaPrecompIso e).app X))
    (fun f => ObjectProperty.hom_ext _ ((yonedaPrecompIso e).hom.naturality f))

end Autoequivalences

section Pretriangulated

variable [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

open CategoryTheory.Pretriangulated

/-- Representables are injective in the coherent-functor category of a
pretriangulated category. The extension is constructed from a triangle on a
representable cover of the pullback of the given monomorphism. -/
instance representable_injective (X : C) : Injective ((yoneda (C := C)).obj X) where
  factors {F G} a m _ := by
    let Z := G.property.some.generators
    let p : (yoneda (C := C)).obj Z ⟶ G := ObjectProperty.homMk G.property.some.projection
    have : Epi p := (coherent C).ι.epi_of_epi_map G.property.some.projection_epi
    let K := pullback p m
    let j : K ⟶ (yoneda (C := C)).obj Z := pullback.fst p m
    let e : K ⟶ F := pullback.snd p m
    let B := K.property.some.generators
    let q : (yoneda (C := C)).obj B ⟶ K := ObjectProperty.homMk K.property.some.projection
    have : Epi q := (coherent C).ι.epi_of_epi_map K.property.some.projection_epi
    let h := (yoneda (C := C)).preimage (q ≫ j)
    let g := (yoneda (C := C)).preimage (q ≫ e ≫ a)
    have hh : (yoneda (C := C)).map h = q ≫ j :=
      (yoneda (C := C)).map_preimage _
    have hg : (yoneda (C := C)).map g = q ≫ e ≫ a :=
      (yoneda (C := C)).map_preimage _
    obtain ⟨A, s, t, hT⟩ := distinguished_cocone_triangle₁ h
    have hs : (yoneda (C := C)).map s ≫ q = 0 := by
      apply (cancel_mono j).1
      rw [Category.assoc, ← hh, ← Functor.map_comp]
      have hsh := comp_distTriang_mor_zero₁₂ (Triangle.mk s h t) hT
      simpa using (yoneda (C := C)).congr_map hsh
    have hsg : s ≫ g = 0 := by
      apply (yoneda (C := C)).map_injective
      rw [Functor.map_comp, hg, ← Category.assoc, hs]
      simp
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ (Triangle.mk s h t) hT g hsg
    change Z ⟶ X at r
    change g = h ≫ r at hr
    have hjr : j ≫ (yoneda (C := C)).map r = e ≫ a := by
      apply (cancel_epi q).1
      rw [← Category.assoc, ← hh, ← Functor.map_comp, ← hr, hg]
    let l : kernel p ⟶ K := pullback.lift (kernel.ι p) 0 (by simp)
    have hl₁ : l ≫ j = kernel.ι p := by simp [l, j]
    have hl₂ : l ≫ e = 0 := by simp [l, e]
    have hκ : kernel.ι p ≫ (yoneda (C := C)).map r = 0 := by
      rw [← hl₁, Category.assoc, hjr, ← Category.assoc, hl₂, zero_comp]
    let b := Abelian.epiDesc p ((yoneda (C := C)).map r) hκ
    have hb : p ≫ b = (yoneda (C := C)).map r := Abelian.comp_epiDesc _ _ _
    refine ⟨b, ?_⟩
    apply (cancel_epi e).1
    rw [← Category.assoc]
    change (pullback.snd p m ≫ m) ≫ b = _
    rw [← pullback.condition, Category.assoc, hb]
    exact hjr

omit [HasBinaryBiproducts C] in
/-- A coherent functor embeds in a representable by completing its finite
presentation differential to a distinguished triangle. -/
theorem exists_representable_embedding (F : Mod C) :
    ∃ (X : C) (f : F ⟶ (yoneda (C := C)).obj X), Mono f := by
  let P := F.property.some
  obtain ⟨X, g, h, hT⟩ := distinguished_cocone_triangle P.differential
  have w : preadditiveYoneda.map P.differential ≫ preadditiveYoneda.map g = 0 := by
    rw [← Functor.map_comp]
    have hfg := comp_distTriang_mor_zero₁₂ (Triangle.mk P.differential g h) hT
    simpa using preadditiveYoneda.congr_map hfg
  have he : (ShortComplex.mk (preadditiveYoneda.map P.differential)
      (preadditiveYoneda.map g) w).Exact := by
    apply exact_of_pointwise
    intro W x hx
    change x ≫ g = 0 at hx
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ (Triangle.mk P.differential g h) hT x hx
    exact ⟨y, hy.symm⟩
  let u := P.isColimit.desc (CokernelCofork.ofπ (preadditiveYoneda.map g) w)
  have hu : P.projection ≫ u = preadditiveYoneda.map g :=
    P.isColimit.fac _ WalkingParallelPair.one
  let c := cokernel.desc (preadditiveYoneda.map P.differential) (preadditiveYoneda.map g) w
  have : Mono c := he.mono_cokernelDesc
  let e := IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (preadditiveYoneda.map P.differential)) P.isColimit
  have hi : P.projection ≫ e.inv = cokernel.π (preadditiveYoneda.map P.differential) := by
    dsimp [e]
    exact IsColimit.comp_coconePointUniqueUpToIso_inv
      (cokernelIsCokernel (preadditiveYoneda.map P.differential))
      P.isColimit WalkingParallelPair.one
  have heq : u = e.inv ≫ c := by
    apply (cancel_epi P.projection).1
    rw [hu, ← Category.assoc, hi]
    exact (cokernel.π_desc _ _ _).symm
  have hm : Mono u := by rw [heq]; infer_instance
  exact ⟨X, ObjectProperty.homMk u, (coherent C).ι.mono_of_mono_map hm⟩

/-- An injective presentation with a representable middle object. -/
def injectivePresentation (F : Mod C) : InjectivePresentation F where
  J := (yoneda (C := C)).obj (exists_representable_embedding F).choose
  f := (exists_representable_embedding F).choose_spec.choose
  mono := (exists_representable_embedding F).choose_spec.choose_spec

instance enoughInjectives : EnoughInjectives (Mod C) where
  presentation F := ⟨injectivePresentation F⟩

/-- Projective and injective coherent functors coincide, since either class is
a retract of a representable and representables belong to both classes. -/
theorem projective_iff_injective (F : Mod C) : Projective F ↔ Injective F := by
  constructor
  · intro hF
    let P := projectivePresentation F
    let : Injective P.p := by dsimp [P, projectivePresentation]; infer_instance
    obtain ⟨i, hi⟩ := Projective.factors (𝟙 F) P.f
    exact (⟨i, P.f, hi⟩ : Retract F P.p).injective
  · intro hF
    let I := injectivePresentation F
    let : Projective I.J := by dsimp [I, injectivePresentation]; infer_instance
    obtain ⟨r, hr⟩ := Injective.factors (𝟙 F) I.f
    exact (⟨I.f, r, hr⟩ : Retract F I.J).projective

/-- The coherent-functor category of a pretriangulated category is Frobenius
abelian. This instance is derived from the presentations and triangles above. -/
instance mod_frobenius : FrobeniusAbelian (Mod C) where
  enoughProjectives := inferInstance
  enoughInjectives := inferInstance
  projective_iff_injective := projective_iff_injective

/-- The actual full subcategory of projective-injective coherent functors. -/
def projectiveInjectives : ObjectProperty (Mod C) :=
  fun F => Projective F ∧ Injective F

/-- Yoneda with codomain restricted to projective-injective functors. -/
def projectiveInjectiveYoneda : C ⥤ (projectiveInjectives (C := C)).FullSubcategory :=
  (projectiveInjectives (C := C)).lift yoneda (fun _ => ⟨inferInstance, inferInstance⟩)

instance projectiveInjectiveYoneda_full : (projectiveInjectiveYoneda (C := C)).Full := by
  unfold projectiveInjectiveYoneda
  infer_instance

instance projectiveInjectiveYoneda_faithful : (projectiveInjectiveYoneda (C := C)).Faithful := by
  unfold projectiveInjectiveYoneda
  infer_instance

instance projectiveInjectiveYoneda_additive : (projectiveInjectiveYoneda (C := C)).Additive := by
  unfold projectiveInjectiveYoneda
  infer_instance

instance projectiveInjectiveYoneda_essSurj [IsIdempotentComplete C] :
    (projectiveInjectiveYoneda (C := C)).EssSurj where
  mem_essImage F := by
    obtain ⟨X, ⟨e⟩⟩ := (projective_iff_representable F.obj).mp F.property.1
    exact ⟨X, ⟨ObjectProperty.isoMk (projectiveInjectives (C := C)) e.symm⟩⟩

instance projectiveInjectiveYoneda_isEquivalence [IsIdempotentComplete C] :
    (projectiveInjectiveYoneda (C := C)).IsEquivalence where

/-- For split idempotents, Yoneda identifies the given category with the full
subcategory of projective-injective coherent functors. -/
def projectiveInjectiveEquivalence [IsIdempotentComplete C] :
    C ≌ (projectiveInjectives (C := C)).FullSubcategory :=
  (projectiveInjectiveYoneda (C := C)).asEquivalence

/-- The pretriangulated suspension extends to an autoequivalence of the
coherent-functor category by inverse precomposition. -/
def suspension : Mod C ≌ Mod C := by
  let : (shiftEquiv C (1 : ℤ)).functor.Additive := by
    change (shiftFunctor C (1 : ℤ)).Additive
    infer_instance
  exact autoequivalence (shiftEquiv C (1 : ℤ))

/-- Yoneda commutes with the concrete suspension extension. -/
def yonedaSuspensionIso :
    yoneda ⋙ (suspension (C := C)).functor ≅ shiftFunctor C (1 : ℤ) ⋙ yoneda := by
  let : (shiftEquiv C (1 : ℤ)).functor.Additive := by
    change (shiftFunctor C (1 : ℤ)).Additive
    infer_instance
  exact yonedaAutoequivalenceIso (shiftEquiv C (1 : ℤ))

end Pretriangulated

end PretriangulatedV2.CoherentFunctors
