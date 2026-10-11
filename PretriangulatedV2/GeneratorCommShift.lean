import PretriangulatedV2.AutoequivalenceShift
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Pullback

/-!
Integer-shift commutation from a genuine comparison at the generator.
The comparison is extended through the actual orbit-chain strictification.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u v' u'

open CategoryTheory

namespace PretriangulatedV2.GeneratorCommShift

open AutoequivalenceShift

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [HasShift D ℤ] (E : C ≌ C) (F : D ⥤ C)
  (δ : shiftFunctor D (1 : ℤ) ⋙ F ≅ F ⋙ E.functor)

local instance : HasShift (Chain E) ℤ := chainHasShift E

/-- The actual bi-infinite orbit associated with the generator comparison. -/
def orbit (X : D) : Chain E where
  obj n := F.obj (X⟦n⟧)
  step n := (δ.app (X⟦n⟧)).symm ≪≫ F.mapIso ((shiftFunctorAdd D n 1).app X).symm

/-- Actual shifted morphisms give a compatible morphism of the orbit chains. -/
def orbitMap {X Y : D} (f : X ⟶ Y) : orbit E F δ X ⟶ orbit E F δ Y where
  app n := F.map (f⟦n⟧')
  comm n := by
    dsimp only [orbit, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
    change (F ⋙ E.functor).map (f⟦n⟧') ≫ δ.inv.app (Y⟦n⟧) ≫
      F.map ((shiftFunctorAdd D n 1).inv.app Y) = _
    rw [δ.inv.naturality_assoc]
    dsimp only [Functor.comp_map]
    have hn := (shiftFunctorAdd D n 1).inv.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [← F.map_comp, hn, F.map_comp]
    simp only [Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]

/-- The actual orbit-chain functor. -/
def orbitFunctor : D ⥤ Chain E where
  obj := orbit E F δ
  map := orbitMap E F δ
  map_id := by
    intro X
    apply ChainHom.ext
    funext n
    change F.map ((shiftFunctor D n).map (𝟙 X)) = 𝟙 _
    simp
  map_comp := by
    intro X Y Z f g
    apply ChainHom.ext
    funext n
    change F.map ((shiftFunctor D n).map (f ≫ g)) =
      F.map ((shiftFunctor D n).map f) ≫ F.map ((shiftFunctor D n).map g)
    simp

/-- Componentwise isomorphisms whose hom maps form a chain morphism give
an actual isomorphism in the orbit-chain category. -/
def chainIso {X Y : Chain E} (e : ∀ n, X.obj n ≅ Y.obj n)
    (comm : ∀ n, E.functor.map (e n).hom ≫ (Y.step n).hom =
      (X.step n).hom ≫ (e (n + 1)).hom) : X ≅ Y where
  hom := ⟨fun n => (e n).hom, comm⟩
  inv :=
    { app := fun n => (e n).inv
      comm := by
        intro n
        apply (cancel_epi (E.functor.map (e n).hom)).mp
        simp only [← E.functor.map_comp_assoc, Iso.hom_inv_id, E.functor.map_id,
          Category.id_comp]
        rw [← Category.assoc, comm, Category.assoc, Iso.hom_inv_id, Category.comp_id] }
  hom_inv_id := by apply ChainHom.ext; funext n; exact (e n).hom_inv_id
  inv_hom_id := by apply ChainHom.ext; funext n; exact (e n).inv_hom_id

/-- The components dictated by the actual source shift addition. -/
def orbitShiftComponent (n : ℤ) (X : D) (t : ℤ) :
    (orbit E F δ (X⟦n⟧)).obj t ≅ ((reindex E n).obj (orbit E F δ X)).obj t :=
  F.mapIso ((shiftFunctorAdd' D n t (t + n) (add_comm n t)).app X).symm

theorem orbitShiftComponent_comm (n : ℤ) (X : D) (t : ℤ) :
    E.functor.map (orbitShiftComponent E F δ n X t).hom ≫
        (((reindex E n).obj (orbit E F δ X)).step t).hom =
      ((orbit E F δ (X⟦n⟧)).step t).hom ≫
        (orbitShiftComponent E F δ n X (t + 1)).hom := by
  dsimp only [orbitShiftComponent, orbit, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom]
  dsimp only [reindex, reindexObj, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.comp_map, δ.inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  have hs := shiftFunctorAdd'_assoc_inv_app (C := D) n t (1 : ℤ) (t + n) (t + 1)
    (t + 1 + n) (add_comm n t) rfl (by omega) X
  have hF := F.congr_map hs
  simpa only [shiftFunctorAdd', Iso.trans_inv, Iso.app_inv, eqToIso.inv,
    NatTrans.comp_app, eqToHom_app, Functor.map_comp, eqToHom_map, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Iso.trans_hom, Category.assoc, eqToHom_refl,
    Category.comp_id, Functor.map_id, Category.id_comp,
    shiftFunctorAdd'_eq_shiftFunctorAdd] using
    congrArg (fun k => δ.inv.app ((X⟦n⟧)⟦t⟧) ≫ k) hF

/-- Actual source shift addition gives the full family of natural
commutation isomorphisms for the orbit functor. -/
def orbitShiftIso (n : ℤ) : shiftFunctor D n ⋙ orbitFunctor E F δ ≅
    orbitFunctor E F δ ⋙ shiftFunctor (Chain E) n :=
  NatIso.ofComponents
    (fun X => chainIso E (orbitShiftComponent E F δ n X)
      (orbitShiftComponent_comm E F δ n X))
    (fun f => by
      apply ChainHom.ext
      funext t
      change F.map ((f⟦n⟧')⟦t⟧') ≫
          F.map ((shiftFunctorAdd' D n t (t + n) (add_comm n t)).inv.app _) =
        F.map ((shiftFunctorAdd' D n t (t + n) (add_comm n t)).inv.app _) ≫
          F.map (f⟦t + n⟧')
      simpa only [Functor.map_comp, Functor.comp_map] using F.congr_map
        ((shiftFunctorAdd' D n t (t + n) (add_comm n t)).inv.naturality f))

theorem chain_eqToHom_app {X Y : Chain E} (h : X = Y) (t : ℤ) :
    (eqToHom h : X ⟶ Y).app t = eqToHom (congrArg (fun Z => Z.obj t) h) := by
  subst Y
  rfl

theorem orbitShiftIso_zero : orbitShiftIso E F δ 0 =
    Functor.CommShift.isoZero (orbitFunctor E F δ) ℤ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (evaluation E 0).map_injective
  simp [orbitShiftIso, chainIso, orbitShiftComponent, Functor.CommShift.isoZero,
    AutoequivalenceShift.evaluation, orbitFunctor, orbitMap,
    ShiftMkCore.shiftFunctorZero_eq, chainShiftCore, chain_eqToHom_app,
    shiftFunctorAdd', shiftFunctorAdd_zero_add_inv_app]

theorem orbitShiftIso_add (n m : ℤ) : orbitShiftIso E F δ (n + m) =
    Functor.CommShift.isoAdd (orbitShiftIso E F δ n) (orbitShiftIso E F δ m) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (evaluation E 0).map_injective
  simp only [Functor.CommShift.isoAdd_hom_app, Functor.map_comp]
  rw [ShiftMkCore.shiftFunctorAdd_eq (chainShiftCore E)]
  simp only [chainShiftCore, eqToIso.inv, eqToHom_app, eqToHom_map]
  dsimp only [AutoequivalenceShift.evaluation, orbitShiftIso, chainIso,
    orbitShiftComponent, orbitFunctor, orbitMap, reindex, reindexObj,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_inv, Iso.symm_hom]
  simp only [ShiftMkCore.shiftFunctor_eq (chainShiftCore E)]
  dsimp only [chainShiftCore, reindex, orbit]
  change @Eq (F.obj ((X⟦n + m⟧)⟦(0 : ℤ)⟧) ⟶ F.obj (X⟦0 + (n + m)⟧)) _ _
  simp only [shiftFunctorAdd', Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, Functor.map_comp, eqToHom_map, shiftFunctorAdd_add_zero_inv_app,
    Category.assoc, eqToHom_trans]
  rw [← F.map_comp_assoc]
  have hz := (shiftFunctorZero D ℤ).hom.naturality ((shiftFunctorAdd D n m).hom.app X)
  dsimp only [Functor.id_map] at hz
  erw [hz]
  rw [F.map_comp, Category.assoc]
  have he := eqToHom_naturality
    (fun i : ℤ => F.map ((shiftFunctorAdd D n i).inv.app X))
    (j := m) (j' := 0 + m) (zero_add m).symm
  rw [← reassoc_of% he]
  simp only [← F.map_comp_assoc, Iso.hom_inv_id_app, eqToHom_trans]
  erw [Category.comp_id]

instance orbitFunctor_commShift : (orbitFunctor E F δ).CommShift ℤ where
  commShiftIso := orbitShiftIso E F δ
  commShiftIso_zero := orbitShiftIso_zero E F δ
  commShiftIso_add := orbitShiftIso_add E F δ

/-- Evaluation of orbit chains commutes with the exact transported action
used by `AutoequivalenceShift.hasShift`. -/
@[instance_reducible]
def evaluationCommShift :
    letI := AutoequivalenceShift.hasShift E
    (AutoequivalenceShift.evaluation E 0).CommShift ℤ := by
  letI := AutoequivalenceShift.hasShift E
  exact Functor.CommShift.ofInduced (evaluationEquivalence E).functor ℤ
    (transportedFunctor (evaluationEquivalence E))
    (transportComparison (evaluationEquivalence E))

/-- Evaluation at zero recovers the original functor through the actual
source shift-zero isomorphism. -/
def orbitEvaluationIso : orbitFunctor E F δ ⋙ AutoequivalenceShift.evaluation E 0 ≅ F :=
  Functor.isoWhiskerRight (shiftFunctorZero D ℤ) F ≪≫ Functor.leftUnitor F

/-- A genuine generator comparison extends to coherent commutation with
every integer shift of the selected autoequivalence action. -/
@[instance_reducible]
def commutation :
    letI := AutoequivalenceShift.hasShift E
    F.CommShift ℤ := by
  let := AutoequivalenceShift.hasShift E
  let := evaluationCommShift E
  exact Functor.CommShift.ofIso (orbitEvaluationIso E F δ) ℤ

/-- The generator comparison for evaluation is the inverse adjacent step. -/
theorem evaluation_generator (X : Chain E) :
    letI := AutoequivalenceShift.hasShift E
    letI := evaluationCommShift E
    ((AutoequivalenceShift.evaluation E 0).commShiftIso (1 : ℤ)).hom.app X ≫
        (AutoequivalenceShift.shiftOneIso E).hom.app (X.obj 0) = (X.step 0).inv := by
  let := AutoequivalenceShift.hasShift E
  let := evaluationCommShift E
  change (transportComparison (evaluationEquivalence E) 1).inv.app X ≫
    (AutoequivalenceShift.shiftOneIso E).hom.app (X.obj 0) = _
  dsimp only [transportComparison, AutoequivalenceShift.shiftOneIso, id,
    Iso.trans_inv, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [NatTrans.id_app]
  repeat' erw [Category.id_comp]
  repeat' erw [Category.comp_id]
  simp only [ShiftMkCore.shiftFunctor_eq (chainShiftCore E)]
  dsimp only [chainShiftCore]
  change (AutoequivalenceShift.evaluation E 1).map
      ((evaluationEquivalence E).unitIso.hom.app X) ≫
      (evaluationStep E 0).inv.app ((evaluationEquivalence E).inverse.obj (X.obj 0)) ≫
      E.functor.map ((evaluationEquivalence E).counitIso.hom.app (X.obj 0)) = _
  erw [(evaluationStep E 0).inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [← E.functor.map_comp]
  change (X.step 0).inv ≫ E.functor.map
    ((evaluationEquivalence E).functor.map ((evaluationEquivalence E).unitIso.hom.app X) ≫
      (evaluationEquivalence E).counitIso.hom.app ((evaluationEquivalence E).functor.obj X)) = _
  rw [(evaluationEquivalence E).functor_unitIso_comp]
  erw [E.functor.map_id, Category.comp_id]

theorem commutation_generator :
    letI := AutoequivalenceShift.hasShift E
    letI := commutation E F δ
    F.commShiftIso (1 : ℤ) ≪≫
      Functor.isoWhiskerLeft F (AutoequivalenceShift.shiftOneIso E) = δ := by
  let := AutoequivalenceShift.hasShift E
  let := commutation E F δ
  apply Iso.ext
  apply NatTrans.ext
  funext X
  let := evaluationCommShift E
  change ((Functor.CommShift.ofIso (orbitEvaluationIso E F δ) ℤ).commShiftIso 1).hom.app X ≫
    (AutoequivalenceShift.shiftOneIso E).hom.app (F.obj X) = δ.hom.app X
  rw [Functor.CommShift.ofIso_commShiftIso_hom_app]
  rw [Functor.commShiftIso_comp_hom_app]
  simp only [Category.assoc]
  erw [(AutoequivalenceShift.shiftOneIso E).hom.naturality
    ((orbitEvaluationIso E F δ).hom.app X)]
  erw [reassoc_of% (evaluation_generator E ((orbitFunctor E F δ).obj X))]
  dsimp only [orbitEvaluationIso, Iso.trans_hom, Iso.trans_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.map_id, Category.comp_id,
    Category.id_comp, orbitFunctor_commShift, orbitShiftIso, chainIso,
    NatIso.ofComponents_hom_app, AutoequivalenceShift.evaluation,
    orbitShiftComponent, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    orbitFunctor, orbit, Functor.mapIso_inv]
  dsimp only [Iso.symm_inv, Functor.mapIso_hom, Iso.app_hom]
  repeat' erw [Category.id_comp]
  repeat' erw [Category.comp_id]
  change F.map ((shiftFunctorZero D ℤ).inv.app (X⟦(1 : ℤ)⟧)) ≫
    F.map ((shiftFunctorAdd' D 1 0 (0 + 1) (by omega)).inv.app X) ≫
      (F.map ((shiftFunctorAdd D 0 1).hom.app X) ≫ δ.hom.app (X⟦(0 : ℤ)⟧)) ≫
        E.functor.map (F.map ((shiftFunctorZero D ℤ).hom.app X)) = δ.hom.app X
  erw [shiftFunctorAdd'_add_zero_inv_app (C := D) (1 : ℤ) X]
  rw [← F.map_comp_assoc,
    Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  simp only [Category.assoc]
  have hδ := δ.hom.naturality ((shiftFunctorZero D ℤ).hom.app X)
  dsimp only [Functor.comp_map] at hδ
  rw [← hδ, shiftFunctorAdd_zero_add_hom_app]
  simp only [eqToHom_refl, Category.id_comp]
  rw [← F.map_comp_assoc, ← (shiftFunctor D (1 : ℤ)).map_comp,
    Iso.inv_hom_id_app]
  erw [(shiftFunctor D (1 : ℤ)).map_id, F.map_id, Category.id_comp]
  rfl

section Rescale

variable [HasShift C ℤ]

/-- Multiplication of integer shift degrees by a fixed integer. -/
def scale (m : ℤ) : ℤ →+ ℤ where
  toFun n := m * n
  map_zero' := mul_zero _
  map_add' := mul_add _

/-- The identity on the category carrying the rescaled original action. -/
def scaledInclusion (m : ℤ) : PullbackShift C (scale m) ⥤ C where
  obj X := X
  map f := f

def scaledInverse (m : ℤ) : C ⥤ PullbackShift C (scale m) where
  obj X := X
  map f := f

def scaledGeneratorIso (m : ℤ) :
    shiftFunctor (PullbackShift C (scale m)) (1 : ℤ) ⋙ scaledInclusion m ≅
      scaledInclusion m ⋙ (shiftEquiv C m).functor :=
  NatIso.ofComponents
    (fun X => (pullbackShiftIso C (scale m) 1 m (by simp [scale])).app X)
    (fun f => (pullbackShiftIso C (scale m) 1 m (by simp [scale])).hom.naturality f)

/-- The action generated from the original shift by `m` agrees, degree by
degree, with the original shift by `m * n`. -/
def generatedShiftIsoCanonical (m n : ℤ) :
    let canonical := shiftFunctor C (m * n)
    let E := shiftEquiv C m
    letI := AutoequivalenceShift.hasShift E
    shiftFunctor C n ≅ canonical := by
  let E := shiftEquiv C m
  let K := PullbackShift C (scale m)
  let G := scaledInverse (C := C) m
  let H := commutation E (scaledInclusion m) (scaledGeneratorIso m)
  letI := AutoequivalenceShift.hasShift E
  exact (Functor.isoWhiskerLeft G (H.commShiftIso n)).symm

end Rescale

end PretriangulatedV2.GeneratorCommShift
