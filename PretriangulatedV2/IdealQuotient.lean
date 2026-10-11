import Mathlib.CategoryTheory.Quotient.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.GroupTheory.QuotientGroup.Basic

universe v u

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2

namespace IdealQuotient

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- A morphism which factors through an object satisfying `B`. -/
def FactorsThrough (B : C → Prop) {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (Z : C), B Z ∧ ∃ (a : X ⟶ Z) (b : Z ⟶ Y), a ≫ b = f

/-- The object property `B` is closed under the chosen binary biproducts. -/
class ClosedUnderBinaryBiproducts (B : C → Prop) : Prop where
  biprod_mem {X Y : C} [HasBinaryBiproduct X Y] : B X → B Y → B (X ⊞ Y)

variable (B : C → Prop)

/-- Closure of an object property under retracts. -/
def retractClosure (B : C → Prop) : C → Prop :=
  fun X => ∃ (Y : C), B Y ∧ Nonempty (Retract X Y)

instance retractClosure_nonempty [Nonempty {X : C // B X}] :
    Nonempty {X : C // retractClosure B X} := by
  rcases ‹Nonempty {X : C // B X}› with ⟨⟨X, hX⟩⟩
  exact ⟨⟨X, X, hX, ⟨Retract.refl X⟩⟩⟩

noncomputable def retract_biprod {X₁ X₂ Y₁ Y₂ : C}
    (r₁ : Retract X₁ Y₁) (r₂ : Retract X₂ Y₂) :
    Retract (X₁ ⊞ X₂) (Y₁ ⊞ Y₂) where
  i := biprod.map r₁.i r₂.i
  r := biprod.map r₁.r r₂.r
  retract := by
    ext <;> simp

instance retractClosure_biproduct [ClosedUnderBinaryBiproducts B] :
    ClosedUnderBinaryBiproducts (retractClosure B) where
  biprod_mem hX hY := by
    rcases hX with ⟨X', hX', ⟨rX⟩⟩
    rcases hY with ⟨Y', hY', ⟨rY⟩⟩
    exact ⟨X' ⊞ Y', ClosedUnderBinaryBiproducts.biprod_mem hX' hY',
      ⟨retract_biprod rX rY⟩⟩

omit [HasBinaryBiproducts C] in
lemma factorsThrough_zero [Nonempty {X : C // B X}] {X Y : C} :
    FactorsThrough B (0 : X ⟶ Y) := by
  rcases ‹Nonempty {X : C // B X}› with ⟨⟨Z, hZ⟩⟩
  exact ⟨Z, hZ, 0, 0, by simp⟩

omit [HasBinaryBiproducts C] in
lemma factorsThrough_neg {X Y : C} {f : X ⟶ Y} (hf : FactorsThrough B f) :
    FactorsThrough B (-f) := by
  rcases hf with ⟨Z, hZ, a, b, hab⟩
  refine ⟨Z, hZ, a, -b, ?_⟩
  simp [hab]

lemma factorsThrough_add [ClosedUnderBinaryBiproducts B]
    {X Y : C} {f g : X ⟶ Y} (hf : FactorsThrough B f) (hg : FactorsThrough B g) :
    FactorsThrough B (f + g) := by
  rcases hf with ⟨P, hP, a, b, hab⟩
  rcases hg with ⟨Q, hQ, c, d, hcd⟩
  refine ⟨P ⊞ Q, ClosedUnderBinaryBiproducts.biprod_mem hP hQ,
    biprod.lift a c, biprod.desc b d, ?_⟩
  rw [biprod.lift_desc, hab, hcd]

/-- The additive ideal consisting of maps factoring through `B`. -/
def factorIdeal [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]
    (X Y : C) : AddSubgroup (X ⟶ Y) where
  carrier := {f | FactorsThrough B f}
  zero_mem' := factorsThrough_zero B
  add_mem' := factorsThrough_add B
  neg_mem' := factorsThrough_neg B

lemma mem_factorIdeal_iff [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]
    {X Y : C} {f : X ⟶ Y} : f ∈ factorIdeal B X Y ↔ FactorsThrough B f := Iff.rfl

lemma factorIdeal_postcomp [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]
    {X Y Z : C} {f : X ⟶ Y} (hf : f ∈ factorIdeal B X Y) (g : Y ⟶ Z) :
    f ≫ g ∈ factorIdeal B X Z := by
  rcases hf with ⟨P, hP, a, b, hab⟩
  exact ⟨P, hP, a, b ≫ g, by rw [← Category.assoc, hab]⟩

lemma factorIdeal_precomp [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]
    {X Y Z : C} {g : Y ⟶ Z} (hg : g ∈ factorIdeal B Y Z) (f : X ⟶ Y) :
    f ≫ g ∈ factorIdeal B X Z := by
  rcases hg with ⟨P, hP, a, b, hab⟩
  exact ⟨P, hP, f ≫ a, b, by simp [Category.assoc, hab]⟩

/-- The congruence induced by the ideal of maps factoring through `B`. -/
def factorRelation [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B] : HomRel C :=
  fun {X Y} f g => f - g ∈ factorIdeal B X Y

lemma factorRelation_add [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]
    {X Y : C} {f₁ f₂ g₁ g₂ : X ⟶ Y}
    (hf : factorRelation B f₁ f₂) (hg : factorRelation B g₁ g₂) :
    factorRelation B (f₁ + g₁) (f₂ + g₂) := by
  change (f₁ + g₁) - (f₂ + g₂) ∈ factorIdeal B X Y
  rw [show (f₁ + g₁) - (f₂ + g₂) = (f₁ - f₂) + (g₁ - g₂) by abel]
  exact (factorIdeal B X Y).add_mem hf hg

instance factorRelation_congruence [Nonempty {X : C // B X}]
    [ClosedUnderBinaryBiproducts B] : Congruence (factorRelation B) where
  equivalence := fun {X Y} =>
    { refl := by
        intro f
        change f - f ∈ factorIdeal B X Y
        simp
      symm := by
        intro f g hfg
        change g - f ∈ factorIdeal B X Y
        rw [show g - f = -(f - g) by abel]
        exact (factorIdeal B X Y).neg_mem hfg
      trans := by
        intro f g h hfg hgh
        change f - h ∈ factorIdeal B X Y
        rw [show f - h = (f - g) + (g - h) by abel]
        exact (factorIdeal B X Y).add_mem hfg hgh }
  comp_left := by
    intro X Y Z f g g' hgg'
    change f ≫ g - f ≫ g' ∈ factorIdeal B X Z
    rw [← Preadditive.comp_sub]
    exact factorIdeal_precomp B hgg' f
  comp_right := by
    intro X Y Z f f' g hff'
    change f ≫ g - f' ≫ g ∈ factorIdeal B X Z
    rw [← Preadditive.sub_comp]
    exact factorIdeal_postcomp B hff' g

/-- The preadditive quotient by morphisms factoring through `B`. -/
abbrev category [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B] :=
  CategoryTheory.Quotient (factorRelation B)

instance quotient_preadditive [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B] :
    Preadditive (category B) :=
  CategoryTheory.Quotient.preadditive (factorRelation B) (by
    intro X Y f₁ f₂ g₁ g₂ hf hg
    exact factorRelation_add B hf hg)

/-- The canonical functor into the ideal quotient. -/
abbrev functor [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B] :
    C ⥤ category B :=
  CategoryTheory.Quotient.functor (factorRelation B)

instance functor_additive [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B] :
    (functor B).Additive :=
  CategoryTheory.Quotient.functor_additive (factorRelation B) (by
    intro X Y f₁ f₂ g₁ g₂ hf hg
    exact factorRelation_add B hf hg)

lemma functor_map_eq_zero_iff [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]
    {X Y : C} (f : X ⟶ Y) : (functor B).map f = 0 ↔ f ∈ factorIdeal B X Y := by
  change (functor B).map f = (functor B).map 0 ↔ _
  rw [CategoryTheory.Quotient.functor_map_eq_iff]
  change f - 0 ∈ factorIdeal B X Y ↔ _
  simp

lemma object_killed_iff_retract [Nonempty {X : C // B X}] [ClosedUnderBinaryBiproducts B]
    (X : C) : (functor B).map (𝟙 X) = 0 ↔
      ∃ (Z : C), B Z ∧ Nonempty (Retract X Z) := by
  rw [functor_map_eq_zero_iff]
  constructor
  · rintro ⟨Z, hZ, i, r, hir⟩
    exact ⟨Z, hZ, ⟨{ i := i, r := r, retract := hir }⟩⟩
  · rintro ⟨Z, hZ, ⟨h⟩⟩
    exact ⟨Z, hZ, h.i, h.r, h.retract⟩

omit [HasBinaryBiproducts C] in
lemma factorsThrough_retractClosure_iff [Nonempty {X : C // B X}]
    [ClosedUnderBinaryBiproducts B]
    (hB : ∀ ⦃X Y : C⦄, B Y → Retract X Y → B X)
    {X Y : C} {f : X ⟶ Y} : FactorsThrough B f ↔
      FactorsThrough (fun Z => ∃ W, B W ∧ Nonempty (Retract Z W)) f := by
  constructor
  · rintro ⟨Z, hZ, a, b, hab⟩
    exact ⟨Z, ⟨Z, hZ, ⟨Retract.refl Z⟩⟩, a, b, hab⟩
  · rintro ⟨Z, ⟨W, hW, ⟨r⟩⟩, a, b, hab⟩
    exact ⟨Z, hB hW r, a, b, hab⟩

lemma factorIdeal_retractClosure_eq [Nonempty {X : C // B X}]
    [ClosedUnderBinaryBiproducts B]
    (hB : ∀ ⦃X Y : C⦄, B Y → Retract X Y → B X)
    (X Y : C) : factorIdeal B X Y = factorIdeal (retractClosure B) X Y := by
  ext f
  simp only [mem_factorIdeal_iff]
  exact factorsThrough_retractClosure_iff B hB

end IdealQuotient

end PretriangulatedV2
