import PretriangulatedV2.Gemstone
import PretriangulatedV2.HomDimensions

/-!
The dimension comparison in Lemma 5.5(1) of arXiv:2608.09777v2.
All exactness statements below come from mathlib's distinguished triangles.
The shift is explicitly assumed to be linear over the ground field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace PretriangulatedV2

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  {k : Type w} [Field k] [Linear k C]

/-- The triangle (5.3), with its factor of `Σα` retained explicitly.
Existence of these data is proved below from the gemstone axioms. -/
structure GemstoneCone {X : C} (G : Gemstone X) where
  s : X⟦(1 : ℤ)⟧ ⟶ G.middle
  factor : s ≫ G.second = G.alpha⟦(1 : ℤ)⟧'
  nonzero : s ≠ 0
  Y : C
  w : G.middle ⟶ Y
  z : Y ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧
  distinguished : Triangle.mk s w z ∈ distTriang C

omit [HasZeroObject C] [HasBinaryBiproducts C]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  [Preadditive C] [HasShift C ℤ] in
private theorem not_nonempty_retract_of_forall_not_isSplitMono {A B : C}
    (h : ∀ f : A ⟶ B, ¬ IsSplitMono f) : ¬ Nonempty (Retract A B) := by
  rintro ⟨r⟩
  exact h r.i ⟨⟨⟨r.r, r.retract⟩⟩⟩

namespace Gemstone

variable {X : C} (G : Gemstone X)

/-- Exactness at the shifted first vertex gives the preceding zero composite,
without choosing an inverse suspension or using a shift coherence formula. -/
theorem alpha_first_eq_zero : G.alpha ≫ G.first = 0 := by
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [Functor.map_comp, Functor.map_zero]
  exact comp_distTriang_mor_zero₃₁ G.triangle G.triangle_distinguished

/-- Rigidity kills the last term in `Hom(X, -)` of the gemstone triangle. -/
theorem rightComp_first_surjective :
    Function.Surjective (Linear.rightComp k X G.first) := by
  intro f
  obtain ⟨q, hq⟩ := G.triangle.coyoneda_exact₂ G.triangle_distinguished f
    (G.rigid (f ≫ G.second))
  exact ⟨q, hq.symm⟩

/-- The preceding image in the `Hom(X, -)` exact sequence is computed using only
the forward shift, its fullness, and its faithfulness. -/
theorem ker_rightComp_first :
    LinearMap.ker (Linear.rightComp k X G.first) =
      LinearMap.range (Linear.rightComp k X G.alpha) := by
  ext q
  constructor
  · intro hq
    have hzero : q ≫ G.first = 0 := hq
    have hshift : q⟦(1 : ℤ)⟧' ≫ G.first⟦(1 : ℤ)⟧' = 0 := by
      rw [← Functor.map_comp, hzero, Functor.map_zero]
    obtain ⟨b, hb⟩ := G.triangle.coyoneda_exact₁ G.triangle_distinguished
      (q⟦(1 : ℤ)⟧') hshift
    obtain ⟨t, ht⟩ := (shiftFunctor C (1 : ℤ)).map_surjective b
    apply LinearMap.mem_range.mpr
    refine ⟨t, ?_⟩
    apply (shiftFunctor C (1 : ℤ)).map_injective
    change (shiftFunctor C (1 : ℤ)).map (t ≫ G.alpha) =
      (shiftFunctor C (1 : ℤ)).map q
    rw [Functor.map_comp, ht]
    exact hb.symm
  · intro hq
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hq
    change (t ≫ G.alpha) ≫ G.first = 0
    rw [Category.assoc, G.alpha_first_eq_zero, comp_zero]

/-- Reverse rigidity kills the first term in `Hom(ΣX, -)`. -/
theorem rightComp_second_injective :
    Function.Injective (Linear.rightComp k (X⟦(1 : ℤ)⟧) G.second) := by
  intro f g hfg
  have hzero : (f - g) ≫ G.second = 0 := by
    simpa only [Linear.rightComp_apply, Preadditive.sub_comp] using
      sub_eq_zero.mpr hfg
  obtain ⟨q, hq⟩ : ∃ q : X⟦(1 : ℤ)⟧ ⟶ X, f - g = q ≫ G.first :=
    G.triangle.coyoneda_exact₂ G.triangle_distinguished (f - g) hzero
  rw [G.reverse_rigid q, zero_comp] at hq
  exact sub_eq_zero.mp hq

/-- Exactness at `End(ΣX)` identifies the image of `v` with the kernel of `Σα`. -/
theorem range_rightComp_second :
    LinearMap.range (Linear.rightComp k (X⟦(1 : ℤ)⟧) G.second) =
      LinearMap.ker (Linear.rightComp k (X⟦(1 : ℤ)⟧) (G.alpha⟦(1 : ℤ)⟧')) := by
  ext q
  constructor
  · intro hq
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hq
    change (t ≫ G.second) ≫ G.alpha⟦(1 : ℤ)⟧' = 0
    have hcomp : G.second ≫ G.alpha⟦(1 : ℤ)⟧' = 0 :=
      comp_distTriang_mor_zero₂₃ G.triangle G.triangle_distinguished
    rw [Category.assoc, hcomp, comp_zero]
  · intro hq
    obtain ⟨t, ht⟩ := G.triangle.coyoneda_exact₃ G.triangle_distinguished q hq
    exact LinearMap.mem_range.mpr ⟨t, ht.symm⟩

variable [∀ A B : C, FiniteDimensional k (A ⟶ B)]
  [Functor.Linear k (shiftFunctor C (1 : ℤ))]

/-- The linear shift identifies the two image spaces of `α` and `Σα`. -/
def ker_first_shiftedAlphaLinearEquiv :
    LinearMap.ker (Linear.rightComp k X G.first) ≃ₗ[k]
      LinearMap.range (Linear.rightComp k (X⟦(1 : ℤ)⟧) (G.alpha⟦(1 : ℤ)⟧')) := by
  let e := shiftHomLinearEquiv (k := k) X X
  let d := Linear.rightComp k X G.alpha
  let c := Linear.rightComp k (X⟦(1 : ℤ)⟧) (G.alpha⟦(1 : ℤ)⟧')
  have hcomm : e.toLinearMap.comp d = c.comp e.toLinearMap := by
    ext t
    exact (shiftFunctor C (1 : ℤ)).map_comp t G.alpha
  apply e.ofSubmodules
  rw [G.ker_rightComp_first (k := k)]
  change (LinearMap.range d).map e.toLinearMap = LinearMap.range c
  rw [← LinearMap.range_comp, hcomm]
  exact LinearMap.range_comp_of_range_eq_top c e.range

/-- Lemma 5.5(1): the two represented Hom spaces of the gemstone's middle
vertex have equal dimension. No dimension identity is assumed. -/
theorem finrank_hom_shift_middle_eq :
    Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle) =
      Module.finrank k (X ⟶ G.middle) := by
  symm
  exact finrank_eq_of_surjective_of_injective_of_ker_equiv
    (Linear.rightComp k X G.first) (G.rightComp_first_surjective (k := k))
    (Linear.rightComp k (X⟦(1 : ℤ)⟧) G.second) (G.rightComp_second_injective (k := k))
    (Linear.rightComp k (X⟦(1 : ℤ)⟧) (G.alpha⟦(1 : ℤ)⟧'))
    (shiftHomLinearEquiv (k := k) X X) (G.ker_first_shiftedAlphaLinearEquiv (k := k))
    (G.range_rightComp_second (k := k))

/-- The connecting morphism of the gemstone triangle is nonzero by faithfulness. -/
theorem shifted_alpha_ne_zero : G.alpha⟦(1 : ℤ)⟧' ≠ 0 := by
  intro hzero
  apply G.almostVanishing.nonzero
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simpa only [Functor.map_zero] using hzero

omit [Functor.Linear k (shiftFunctor C (1 : ℤ))] in
/-- The first strict inequality in Lemma 5.5(2). -/
theorem finrank_hom_shift_middle_lt_end_shift :
    Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle) <
      Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧) := by
  exact finrank_hom_obj₂_lt_end_obj₃_of_mor₃_ne_zero G.triangle_distinguished
    G.reverse_rigid G.shifted_alpha_ne_zero

/-- Lemma 5.5(3), transferred from the preceding inequality by the two
dimension identities that have already been proved. -/
theorem finrank_hom_middle_lt_end :
    Module.finrank k (X ⟶ G.middle) < Module.finrank k (X ⟶ X) := by
  calc
    Module.finrank k (X ⟶ G.middle) =
        Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle) :=
      (G.finrank_hom_shift_middle_eq (k := k)).symm
    _ < Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧) :=
      G.finrank_hom_shift_middle_lt_end_shift (k := k)
    _ = Module.finrank k (X ⟶ X) := (finrank_end_shift_eq (k := k) X).symm

include G in
/-- The rigidity hypothesis survives shifting both endpoints. -/
theorem shifted_rigid (f : X⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) : f = 0 := by
  obtain ⟨q, rfl⟩ := (shiftFunctor C (1 : ℤ)).map_surjective f
  rw [G.rigid q, Functor.map_zero]

omit [Functor.Linear k (shiftFunctor C (1 : ℤ))] in
include k in
/-- Equation (5.2) and completion to a distinguished triangle supply all the
data of `GemstoneCone`; no cone data are assumed to exist separately. -/
theorem nonempty_gemstoneCone : Nonempty (GemstoneCone G) := by
  obtain ⟨s, hs, hnonzero⟩ := G.exists_nonzero_factor (k := k)
  obtain ⟨Y, w, z, hT⟩ := distinguished_cocone_triangle s
  exact ⟨⟨s, hs, hnonzero, Y, w, z, hT⟩⟩

omit [Functor.Linear k (shiftFunctor C (1 : ℤ))] in
/-- A chosen triangle (5.3), constructed from the gemstone data. -/
def cone : GemstoneCone G := Classical.choice (G.nonempty_gemstoneCone (k := k))

variable (K : GemstoneCone G)

omit [Functor.Linear k (shiftFunctor C (1 : ℤ))] in
/-- The second strict inequality in Lemma 5.5(2), for every choice of triangle (5.3). -/
theorem finrank_hom_shift_cone_lt_middle :
    Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ K.Y) <
      Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle) := by
  exact finrank_hom_obj₃_lt_hom_obj₂_of_mor₁_ne_zero K.distinguished
    G.shifted_rigid K.nonzero

/-- Lemma 5.5(4): shifting both endpoints of `Hom(X,U)` preserves its dimension. -/
theorem finrank_hom_shift_cone_lt_shift_middle :
    Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ K.Y) <
      Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle⟦(1 : ℤ)⟧) := by
  calc
    Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ K.Y) <
        Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle) :=
      G.finrank_hom_shift_cone_lt_middle (k := k) K
    _ = Module.finrank k (X ⟶ G.middle) := G.finrank_hom_shift_middle_eq (k := k)
    _ = Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle⟦(1 : ℤ)⟧) :=
      finrank_hom_shift_eq (k := k) X G.middle

/-- All four parts of Lemma 5.5, in the order stated in the paper. -/
theorem lemma_5_5 :
    (Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle) = Module.finrank k (X ⟶ G.middle)) ∧
    (Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle) <
        Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧) ∧
      Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ K.Y) <
        Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle)) ∧
    (Module.finrank k (X ⟶ G.middle) < Module.finrank k (X ⟶ X)) ∧
    (Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ K.Y) <
      Module.finrank k (X⟦(1 : ℤ)⟧ ⟶ G.middle⟦(1 : ℤ)⟧)) :=
  ⟨G.finrank_hom_shift_middle_eq (k := k),
    ⟨G.finrank_hom_shift_middle_lt_end_shift (k := k),
      G.finrank_hom_shift_cone_lt_middle (k := k) K⟩,
    G.finrank_hom_middle_lt_end (k := k),
    G.finrank_hom_shift_cone_lt_shift_middle (k := k) K⟩

include k in
/-- A dimension drop rules out every section from `X` to `U`. -/
theorem not_isSplitMono_to_middle (f : X ⟶ G.middle) : ¬ IsSplitMono f :=
  not_isSplitMono_of_finrank_hom_lt (k := k) f (G.finrank_hom_middle_lt_end (k := k))

omit [Functor.Linear k (shiftFunctor C (1 : ℤ))] in
include k in
/-- A dimension drop rules out every section from `ΣX` to `U`. -/
theorem not_isSplitMono_shift_to_middle (f : X⟦(1 : ℤ)⟧ ⟶ G.middle) :
    ¬ IsSplitMono f :=
  not_isSplitMono_of_finrank_hom_lt (k := k) f
    (G.finrank_hom_shift_middle_lt_end_shift (k := k))

omit [Functor.Linear k (shiftFunctor C (1 : ℤ))] in
include k in
/-- The two strict inequalities in part (2) rule out sections from `ΣX` to `Y`. -/
theorem not_isSplitMono_shift_to_cone (f : X⟦(1 : ℤ)⟧ ⟶ K.Y) : ¬ IsSplitMono f :=
  not_isSplitMono_of_finrank_hom_lt (k := k) f
    (lt_trans (G.finrank_hom_shift_cone_lt_middle (k := k) K)
      (G.finrank_hom_shift_middle_lt_end_shift (k := k)))

include k in
/-- Part (4) rules out sections from `ΣU` to `Y`. -/
theorem not_isSplitMono_shift_middle_to_cone (f : G.middle⟦(1 : ℤ)⟧ ⟶ K.Y) :
    ¬ IsSplitMono f :=
  not_isSplitMono_of_finrank_hom_lt (k := k) f
    (G.finrank_hom_shift_cone_lt_shift_middle (k := k) K)

include k in
/-- The direct-summand consequences stated after Lemma 5.5, expressed by
mathlib's actual retract data. -/
theorem lemma_5_5_no_retracts :
    (¬ Nonempty (Retract X G.middle)) ∧
    (¬ Nonempty (Retract (X⟦(1 : ℤ)⟧) G.middle)) ∧
    (¬ Nonempty (Retract (X⟦(1 : ℤ)⟧) K.Y)) ∧
    (¬ Nonempty (Retract (G.middle⟦(1 : ℤ)⟧) K.Y)) :=
  ⟨not_nonempty_retract_of_forall_not_isSplitMono (G.not_isSplitMono_to_middle (k := k)),
    not_nonempty_retract_of_forall_not_isSplitMono (G.not_isSplitMono_shift_to_middle (k := k)),
    not_nonempty_retract_of_forall_not_isSplitMono (G.not_isSplitMono_shift_to_cone (k := k) K),
    not_nonempty_retract_of_forall_not_isSplitMono
      (G.not_isSplitMono_shift_middle_to_cone (k := k) K)⟩

end Gemstone

end PretriangulatedV2
