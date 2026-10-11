import PretriangulatedV2.AcyclicMapLifting

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PretriangulatedV2.StableCategory.AcyclicMapLifting.Connecting

variable {C : Type u} [Category.{v} C] [Abelian C] [FrobeniusAbelian C]

theorem liftMap_cycles_zero (P R : CochainComplex C ℤ)
    (hP : P.Acyclic) (hR : R.Acyclic)
    (hPproj : ∀ n : ℤ, Projective (P.X n))
    (hRproj : ∀ n : ℤ, Projective (R.X n))
    (f : P.cycles 0 ⟶ R.cycles 0) :
    cyclesMap (liftMap P R hP hR hPproj hRproj f) 0 = f := by
  let eP := P.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := 0) (i' := (0 : ℤ)) (by simp)
  let eR := R.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
    (i := 0) (i' := (0 : ℤ)) (by simp)
  let cP := Lcycles0Iso P
  let cR := Lcycles0Iso R
  have hPi : cP.hom ≫ P.iCycles 0 = (L P).iCycles 0 ≫ eP.hom :=
    Lcycles0Iso_hom_iCycles P
  have hRi : cR.hom ≫ R.iCycles 0 = (L R).iCycles 0 ≫ eR.hom :=
    Lcycles0Iso_hom_iCycles R
  have hPi' : P.iCycles 0 ≫ eP.inv = cP.inv ≫ (L P).iCycles 0 := by
    have h := congrArg (fun t => cP.inv ≫ t ≫ eP.inv) hPi
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  let : ∀ n : ℕ, Projective ((L R).X n) := fun n => L_projective R hRproj n
  let : ∀ n : ℕ, Injective ((L R).X n) := fun n =>
    (FrobeniusAbelian.projective_iff_injective _).mp inferInstance
  have hp : (L P).iCycles 0 ≫ (positiveMap P R hP hRproj f).f 0 =
      (cP.hom ≫ f ≫ cR.inv) ≫ (L R).iCycles 0 := by
    have h := Nonnegative.map_cycles_zero (fun n => L_exactAt P hP n)
      (cP.hom ≫ f ≫ cR.inv)
    have h' := congrArg (fun t => t ≫ (L R).iCycles 0) h
    rw [cyclesMap_i] at h'
    exact h'
  apply (cancel_mono (R.iCycles 0)).mp
  rw [cyclesMap_i]
  change P.iCycles 0 ≫ eP.inv ≫ (positiveMap P R hP hRproj f).f 0 ≫ eR.hom =
    f ≫ R.iCycles 0
  rw [← Category.assoc (P.iCycles 0) eP.inv, hPi', Category.assoc,
    ← Category.assoc ((L P).iCycles 0), hp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← hRi]
  simp

theorem exists_cochainMap (P R : CochainComplex C ℤ)
    (hP : P.Acyclic) (hR : R.Acyclic)
    (hPproj : ∀ n : ℤ, Projective (P.X n))
    (hRproj : ∀ n : ℤ, Projective (R.X n))
    (f : P.cycles 0 ⟶ R.cycles 0) :
    ∃ g : P ⟶ R, cyclesMap g 0 = f :=
  ⟨liftMap P R hP hR hPproj hRproj f,
    liftMap_cycles_zero P R hP hR hPproj hRproj f⟩

end PretriangulatedV2.StableCategory.AcyclicMapLifting.Connecting
