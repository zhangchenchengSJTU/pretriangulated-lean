import Mathlib.CategoryTheory.Shift.Induced
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Data.Int.Init
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.CategoryTheory.HomCongr
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Integer shifts from an autoequivalence

The construction uses a category of bi-infinite chains whose adjacent terms
are identified by the given autoequivalence. Translation of the integer index
has coherent composition. Evaluation at zero transfers this actual shift to
the original category.
-/

noncomputable section

universe v u

open CategoryTheory

namespace PretriangulatedV2.AutoequivalenceShift

variable {C : Type u} [Category.{v} C] (E : C ≌ C)

/-- A bi-infinite orbit, retaining its adjacent comparison isomorphisms. -/
@[ext]
structure Chain where
  obj : ℤ → C
  step : ∀ n : ℤ, E.functor.obj (obj n) ≅ obj (n + 1)

/-- Compatible morphisms of bi-infinite orbits. -/
@[ext]
structure ChainHom (X Y : Chain E) where
  app : ∀ n : ℤ, X.obj n ⟶ Y.obj n
  comm : ∀ n : ℤ,
    E.functor.map (app n) ≫ (Y.step n).hom = (X.step n).hom ≫ app (n + 1)

instance chainCategory : Category.{v} (Chain E) where
  Hom := ChainHom E
  id X := { app := fun n => 𝟙 (X.obj n), comm := by intro n; simp }
  comp f g := {
    app := fun n => f.app n ≫ g.app n
    comm := by
      intro n
      rw [E.functor.map_comp, Category.assoc, g.comm, ← Category.assoc,
        f.comm, Category.assoc] }
  id_comp := by intros; ext n; exact Category.id_comp _
  comp_id := by intros; ext n; exact Category.comp_id _
  assoc := by intros; ext n; exact Category.assoc _ _ _

/-- Evaluation at one degree. -/
def evaluation (n : ℤ) : Chain E ⥤ C where
  obj X := X.obj n
  map f := f.app n

/-- Adjacent degrees have naturally isomorphic evaluation functors. -/
def evaluationStep (n : ℤ) :
    evaluation E n ⋙ E.functor ≅ evaluation E (n + 1) :=
  NatIso.ofComponents (fun X => X.step n) (fun f => f.comm n)

/-- The bijection transporting one component of a chain morphism forward. -/
def homStep (X Y : Chain E) (n : ℤ) :
    (X.obj n ⟶ Y.obj n) ≃ (X.obj (n + 1) ⟶ Y.obj (n + 1)) :=
  (Functor.FullyFaithful.ofFullyFaithful E.functor).homEquiv.trans
    ((X.step n).homCongr (Y.step n))

@[simp]
theorem homStep_apply (X Y : Chain E) (n : ℤ) (f : X.obj n ⟶ Y.obj n) :
    homStep E X Y n f = (X.step n).inv ≫ E.functor.map f ≫ (Y.step n).hom := rfl

theorem homStep_app {X Y : Chain E} (f : X ⟶ Y) (n : ℤ) :
    homStep E X Y n (f.app n) = f.app (n + 1) := by
  rw [homStep_apply, f.comm, Iso.inv_hom_id_assoc]

instance evaluation_faithful (n : ℤ) : (evaluation E n).Faithful where
  map_injective := by
    intro X Y f g h
    apply ChainHom.ext
    funext i
    have hn : f.app n = g.app n := h
    have hall : ∀ j : ℤ, f.app (n + j) = g.app (n + j) := by
      intro j
      induction j using Int.induction_on with
      | zero =>
        rw [Int.add_zero]
        exact hn
      | succ j hj =>
        have hs := congrArg (homStep E X Y (n + j)) hj
        rw [homStep_app, homStep_app] at hs
        rw [← Int.add_assoc]
        exact hs
      | pred j hj =>
        apply (homStep E X Y (n + (-(j : ℤ) - 1))).injective
        rw [homStep_app, homStep_app]
        have hi : n + (-(j : ℤ) - 1) + 1 = n + -(j : ℤ) := by omega
        rw [hi]
        exact hj
    have hi : n + (i - n) = i := by omega
    have h := hall (i - n)
    rw [hi] at h
    exact h

theorem cast_dep_apply {α : ℤ → Type v} (s : ∀ n, α n) {k n : ℤ} (h : k = n) :
    cast (congrArg α h) (s k) = s n := by
  subst n
  rfl

theorem cast_equiv_symm {α : ℤ → Type v} (e : ∀ n, α n ≃ α (n + 1))
    (n k : ℤ) (h : k = n) (hd : α k = α n) (hc : α (n + 1) = α (k + 1))
    (x : α (n + 1)) : e n (cast hd ((e k).symm (cast hc x))) = x := by
  subst k
  exact (e n).apply_symm_apply x

/-- A family of bijections along the integer line admits a compatible section
with any specified value at zero. This supplies actual chain morphisms. -/
theorem exists_integer_section {α : ℤ → Type v}
    (e : (n : ℤ) → α n ≃ α (n + 1)) (a : α 0) :
    ∃ s : (n : ℤ) → α n, s 0 = a ∧ ∀ n : ℤ, e n (s n) = s (n + 1) := by
  let next : ∀ k : ℤ, α k → α (k + 1) := fun k x => e k x
  let prev : ∀ k : ℤ, α k → α (k - 1) := fun k x =>
    (e (k - 1)).symm (cast (congrArg α (show k = k - 1 + 1 by omega)) x)
  let s : ∀ n : ℤ, α n := fun n =>
    n.inductionOn' 0 a (fun k _ x => next k x) (fun k _ x => prev k x)
  refine ⟨s, ?_, ?_⟩
  · exact Int.inductionOn'_self
  · intro n
    by_cases hn : 0 ≤ n
    · change next n (s n) = s (n + 1)
      exact (Int.inductionOn'_add_one hn).symm
    · have hpred : s (n + 1 - 1) = prev (n + 1) (s (n + 1)) :=
        Int.inductionOn'_sub_one (show n + 1 ≤ 0 by omega)
      have hi : n + 1 - 1 = n := by omega
      have ht := congrArg (fun x => cast (congrArg α hi) x) hpred
      rw [cast_dep_apply s hi] at ht
      rw [ht]
      exact cast_equiv_symm e n (n + 1 - 1) hi _ _ _

instance evaluation_zero_full : (evaluation E 0).Full where
  map_surjective := by
    intro X Y f
    obtain ⟨s, hzero, hs⟩ := exists_integer_section (homStep E X Y) f
    refine ⟨{ app := s, comm := ?_ }, hzero⟩
    intro n
    have h := congrArg (fun t => (X.step n).hom ≫ t) (hs n)
    simpa only [homStep_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h

/-- Forward iterates on objects, with no coherence hypothesis. -/
def positiveObj (X : C) : ℕ → C
  | 0 => X
  | n + 1 => E.functor.obj (positiveObj X n)

/-- Backward iterates on objects, using the supplied inverse equivalence. -/
def negativeObj (X : C) : ℕ → C
  | 0 => X
  | n + 1 => E.inverse.obj (negativeObj X n)

/-- Every ambient object admits a bi-infinite orbit. -/
def orbit (X : C) : Chain E where
  obj
    | Int.ofNat n => positiveObj E X n
    | Int.negSucc n => negativeObj E X (n + 1)
  step := by
    intro n
    cases n with
    | ofNat n => exact Iso.refl _
    | negSucc n =>
      cases n with
      | zero => exact E.counitIso.app X
      | succ n => exact E.counitIso.app (negativeObj E X (n + 1))

instance evaluation_zero_essSurj : (evaluation E 0).EssSurj where
  mem_essImage X := ⟨orbit E X, ⟨Iso.refl X⟩⟩

instance evaluation_zero_isEquivalence : (evaluation E 0).IsEquivalence where

/-- The evaluation equivalence follows from the proved full, faithful, and
essentially surjective functor, rather than being assumed. -/
def evaluationEquivalence : Chain E ≌ C :=
  (evaluation E 0).asEquivalence

/-- Integer translation of a bi-infinite orbit. -/
def reindexObj (k : ℤ) (X : Chain E) : Chain E where
  obj n := X.obj (n + k)
  step n := X.step (n + k) ≪≫ eqToIso (congrArg X.obj (by omega))

/-- Integer translation acts on every component of compatible morphisms. -/
def reindex (k : ℤ) : Chain E ⥤ Chain E where
  obj := reindexObj E k
  map := fun {X Y} f => {
    app := fun n => f.app (n + k)
    comm := by
      intro n
      dsimp [reindexObj]
      rw [← Category.assoc, f.comm]
      simp only [Category.assoc]
      exact congrArg (fun t => (X.step (n + k)).hom ≫ t)
        (eqToHom_naturality f.app
          (j := n + k + 1) (j' := n + 1 + k) (by omega)) }

theorem isoTransEqToIso_heq {A B D : C} (i : A ≅ B) (h : B = D) :
    i ≪≫ eqToIso h ≍ i := by
  subst D
  simp

theorem dependent_heq {A : Sort*} {B : A → Sort*} (f : ∀ a, B a)
    {a b : A} (h : a = b) : f a ≍ f b := by
  subst b
  rfl

theorem reindexObj_zero (X : Chain E) : reindexObj E 0 X = X := by
  apply Chain.ext
  · funext n
    exact congrArg X.obj (Int.add_zero n)
  · apply Function.hfunext rfl
    intro n n' hn
    cases hn
    exact (isoTransEqToIso_heq _ _).trans (dependent_heq X.step (Int.add_zero n))

theorem reindexObj_add (m n : ℤ) (X : Chain E) :
    reindexObj E (m + n) X = reindexObj E n (reindexObj E m X) := by
  apply Chain.ext
  · funext i
    exact congrArg X.obj (by omega)
  · apply Function.hfunext rfl
    intro i i' hi
    cases hi
    dsimp [reindexObj]
    simp only [Iso.trans_assoc, eqToIso_trans]
    exact (isoTransEqToIso_heq _ _).trans
      ((dependent_heq X.step (show i + (m + n) = i + n + m by omega)).trans
        (isoTransEqToIso_heq _ _).symm)

theorem chainHom_hext {X Y X' Y' : Chain E} (hx : X = X') (hy : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : f.app ≍ g.app) : f ≍ g := by
  subst X'
  subst Y'
  apply heq_of_eq
  apply ChainHom.ext
  exact eq_of_heq h

theorem reindex_zero : reindex E 0 = 𝟭 (Chain E) := by
  apply Functor.hext (reindexObj_zero E)
  intro X Y f
  apply chainHom_hext E (reindexObj_zero E X) (reindexObj_zero E Y)
  apply Function.hfunext rfl
  intro i i' hi
  cases hi
  exact dependent_heq f.app (Int.add_zero i)

theorem reindex_add (m n : ℤ) :
    reindex E (m + n) = reindex E m ⋙ reindex E n := by
  apply Functor.hext (reindexObj_add E m n)
  intro X Y f
  apply chainHom_hext E (reindexObj_add E m n X) (reindexObj_add E m n Y)
  apply Function.hfunext rfl
  intro i i' hi
  cases hi
  exact dependent_heq f.app (show i + (m + n) = i + n + m by omega)

/-- Translation is an actual coherent integer action on the chain category. -/
def chainShiftCore : ShiftMkCore (Chain E) ℤ where
  F := reindex E
  zero := eqToIso (reindex_zero E)
  add m n := eqToIso (reindex_add E m n)
  assoc_hom_app := by
    intro m n p X
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans]
  zero_add_hom_app := by
    intro n X
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]
  add_zero_hom_app := by
    intro n X
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans]

@[instance_reducible]
def chainHasShift : HasShift (Chain E) ℤ :=
  hasShiftMk (Chain E) ℤ (chainShiftCore E)

section Transport

variable {D : Type*} [Category D] (e : D ≌ C) [HasShift D ℤ]

/-- Explicit functors transporting an already constructed integer shift
across an actual equivalence. -/
def transportedFunctor (n : ℤ) : C ⥤ C :=
  e.inverse ⋙ shiftFunctor D n ⋙ e.functor

/-- The comparison uses only the actual equivalence unit. -/
def transportComparison (n : ℤ) :
    e.functor ⋙ transportedFunctor e n ≅ shiftFunctor D n ⋙ e.functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e.unitIso.symm _ ≪≫ Functor.leftUnitor _

/-- The library's induced-shift construction proves all coherence of this
transport from the actual coherence on the source category. -/
@[instance_reducible]
def transportedHasShift : HasShift C ℤ :=
  HasShift.induced e.functor ℤ (transportedFunctor e) (transportComparison e)

variable [Preadditive D] [Preadditive C] [e.functor.Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

instance transportedFunctor_additive (n : ℤ) : (transportedFunctor e n).Additive := by
  dsimp [transportedFunctor]
  infer_instance

end Transport

/-- The selected coherent integer shift constructed from the arbitrary
autoequivalence. This is a value, so it can be installed locally or scoped. -/
@[instance_reducible]
def hasShift : HasShift C ℤ := by
  letI := chainHasShift E
  exact transportedHasShift (evaluationEquivalence E)

theorem shiftFunctor_eq (n : ℤ) :
    letI := hasShift E
    shiftFunctor C n =
      (evaluationEquivalence E).inverse ⋙ reindex E n ⋙ evaluation E 0 := rfl

/-- The constructed shift by one is naturally isomorphic to the supplied
autoequivalence, via the adjacent chain comparison and evaluation counit. -/
def shiftOneIso :
    letI := hasShift E
    shiftFunctor C (1 : ℤ) ≅ E.functor := by
  change ((evaluationEquivalence E).inverse ⋙ reindex E 1 ⋙ evaluation E 0) ≅ E.functor
  have hReindex : reindex E 1 ⋙ evaluation E 0 ≅ evaluation E 1 := Iso.refl _
  exact Functor.isoWhiskerLeft _ hReindex ≪≫
    Functor.isoWhiskerLeft _ (evaluationStep E 0).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (evaluationEquivalence E).counitIso _ ≪≫
    Functor.leftUnitor _

section Additive

variable [Preadditive C] [E.functor.Additive]

/-- Compatibility is closed under the pointwise abelian group operations. -/
def compatibleHomSubgroup (X Y : Chain E) :
    AddSubgroup (∀ n : ℤ, X.obj n ⟶ Y.obj n) where
  carrier := fun f => ∀ n, E.functor.map (f n) ≫ (Y.step n).hom =
    (X.step n).hom ≫ f (n + 1)
  zero_mem' := by intro n; simp
  add_mem' := by
    intro f g hf hg n
    simp only [Pi.add_apply, E.functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, hf n, hg n]
  neg_mem' := by
    intro f hf n
    simp only [Pi.neg_apply, E.functor.map_neg, Preadditive.neg_comp,
      Preadditive.comp_neg, hf n]

/-- Compatible families and the morphisms of the chain category coincide. -/
def compatibleHomEquiv (X Y : Chain E) :
    (X ⟶ Y) ≃ compatibleHomSubgroup E X Y where
  toFun f := ⟨f.app, f.comm⟩
  invFun f := { app := f.val, comm := f.property }
  left_inv _ := rfl
  right_inv _ := rfl

instance chainPreadditive : Preadditive (Chain E) where
  homGroup X Y := (compatibleHomEquiv E X Y).addCommGroup
  add_comp := by intros; apply ChainHom.ext; funext n; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; apply ChainHom.ext; funext n; exact Preadditive.comp_add _ _ _ _ _ _

@[simp]
theorem chain_add_app {X Y : Chain E} (f g : X ⟶ Y) (n : ℤ) :
    (f + g).app n = f.app n + g.app n := rfl

instance evaluation_additive (n : ℤ) : (evaluation E n).Additive where
  map_add := by intros; rfl

instance reindex_additive (n : ℤ) : (reindex E n).Additive where
  map_add := by intros; apply ChainHom.ext; rfl

theorem chainShift_additive (n : ℤ) :
    letI := chainHasShift E
    (shiftFunctor (Chain E) n).Additive := by
  change (reindex E n).Additive
  infer_instance

end Additive

/-- Every integer shift of the constructed action is additive whenever the
original autoequivalence is additive. -/
theorem shift_additive [Preadditive C] [E.functor.Additive] (n : ℤ) :
    letI := hasShift E
    (shiftFunctor C n).Additive := by
  change ((evaluationEquivalence E).inverse ⋙ reindex E n ⋙ evaluation E 0).Additive
  have : (evaluationEquivalence E).functor.Additive := by
    change (evaluation E 0).Additive
    infer_instance
  infer_instance

end PretriangulatedV2.AutoequivalenceShift
