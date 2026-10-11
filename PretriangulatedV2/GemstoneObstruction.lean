import PretriangulatedV2.GemstoneDimensions
import PretriangulatedV2.IrreducibleObstruction

/-!
The gemstone obstruction lemmas of Section 5 of arXiv:2608.09777v2.
The almost-split and irreducibility inputs are derived from the gemstone
definition; they are not additional hypotheses.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive

namespace PretriangulatedV2

universe w v u

section IrreducibilityTransport

variable {C : Type u} [Category.{v} C] [Preadditive C]

private theorem isSplitMono_of_neg {A B : C} {f : A ⟶ B}
    (hf : IsSplitMono (-f)) : IsSplitMono f := by
  let := hf
  exact IsSplitMono.mk' ⟨-retraction (-f), by
    simpa only [comp_neg, neg_comp] using IsSplitMono.id (-f)⟩

private theorem isSplitEpi_of_neg {A B : C} {f : A ⟶ B}
    (hf : IsSplitEpi (-f)) : IsSplitEpi f := by
  let := hf
  exact IsSplitEpi.mk' ⟨-section_ (-f), by
    simpa only [comp_neg, neg_comp] using IsSplitEpi.id (-f)⟩

namespace IsIrreducibleMorphism

variable {A B : C} {f : A ⟶ B}

/-- Additive inverses preserve irreducibility. -/
theorem neg (hf : IsIrreducibleMorphism f) : IsIrreducibleMorphism (-f) := by
  refine ⟨fun h => hf.1 (isSplitMono_of_neg h),
    fun h => hf.2.1 (isSplitEpi_of_neg h), ?_⟩
  intro Z a b hab
  have hfact : f = a ≫ (-b) := by
    simpa only [neg_neg, comp_neg] using congrArg Neg.neg hab
  rcases hf.2.2 a (-b) hfact with ha | hb
  · exact Or.inl ha
  · exact Or.inr (isSplitEpi_of_neg hb)

omit [Preadditive C] in
/-- A fully faithful, essentially surjective functor preserves irreducibility;
factorizations through arbitrary objects are transported via essential surjectivity. -/
theorem map_of_fully_faithful_essSurj {D : Type*} [Category D]
    (F : C ⥤ D) [Functor.Full F] [Functor.Faithful F] [Functor.EssSurj F]
    (hf : IsIrreducibleMorphism f) : IsIrreducibleMorphism (F.map f) := by
  refine ⟨fun h => hf.1 ((Functor.isSplitMono_iff F f).mp h),
    fun h => hf.2.1 ((Functor.isSplitEpi_iff F f).mp h), ?_⟩
  intro Z l r hlr
  let Z' := F.objPreimage Z
  let e : F.obj Z' ≅ Z := F.objObjPreimageIso Z
  let a : A ⟶ Z' := F.preimage (l ≫ e.inv)
  let b : Z' ⟶ B := F.preimage (e.hom ≫ r)
  have hfact : f = a ≫ b := by
    apply F.map_injective
    simpa only [Functor.map_comp, a, b, Functor.map_preimage,
      Category.assoc, Iso.inv_hom_id_assoc] using hlr
  rcases hf.2.2 a b hfact with ha | hb
  · let := ha
    have hl : IsSplitMono ((F.map a) ≫ e.hom) := inferInstance
    exact Or.inl (by simpa only [a, Functor.map_preimage, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hl)
  · let := hb
    have hr : IsSplitEpi (e.inv ≫ F.map b) := inferInstance
    exact Or.inr (by simpa only [b, Functor.map_preimage, Iso.inv_hom_id_assoc] using hr)

variable [HasShift C ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]

omit [Preadditive C] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] in
/-- In particular, suspension preserves irreducibility. -/
theorem shift_one (hf : IsIrreducibleMorphism f) :
    IsIrreducibleMorphism (f⟦(1 : ℤ)⟧') :=
  hf.map_of_fully_faithful_essSurj (shiftFunctor C (1 : ℤ))

end IsIrreducibleMorphism

end IrreducibilityTransport

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  {k : Type w} [Field k] [Linear k C]
  [∀ A B : C, FiniteDimensional k (A ⟶ B)]

namespace Gemstone

variable {X : C} (G : Gemstone X)

include k in
/-- The right map of the gemstone triangle is right minimal, proved directly
from the connecting almost-vanishing map and the triangle five lemma. -/
theorem second_rightMinimal (a : G.middle ⟶ G.middle) (ha : a ≫ G.second = G.second) :
    IsIso a := by
  obtain ⟨p, hp₁, hp₃⟩ : ∃ p : X ⟶ X,
      G.first ≫ a = p ≫ G.first ∧
      G.alpha⟦(1 : ℤ)⟧' ≫ p⟦(1 : ℤ)⟧' = 𝟙 (X⟦(1 : ℤ)⟧) ≫ G.alpha⟦(1 : ℤ)⟧' :=
    complete_distinguished_triangle_morphism₁ G.triangle G.triangle
      G.triangle_distinguished G.triangle_distinguished a (𝟙 (X⟦(1 : ℤ)⟧))
      (by change G.second ≫ 𝟙 _ = a ≫ G.second; simpa only [Category.comp_id] using ha.symm)
  have hp : G.alpha ≫ p = G.alpha := by
    apply (shiftFunctor C (1 : ℤ)).map_injective
    simpa only [Functor.map_comp, Category.id_comp] using hp₃
  have : IsIso p := G.almostVanishing.isIso_of_postcomp_ne_zero (k := k)
    (by rw [hp]; exact G.almostVanishing.nonzero)
  let phi : G.triangle ⟶ G.triangle :=
    { hom₁ := p
      hom₂ := a
      hom₃ := 𝟙 (X⟦(1 : ℤ)⟧)
      comm₁ := hp₁
      comm₂ := by change G.second ≫ 𝟙 _ = a ≫ G.second; simpa only [Category.comp_id] using ha.symm
      comm₃ := hp₃ }
  exact isIso₂_of_isIso₁₃ phi G.triangle_distinguished G.triangle_distinguished
    (inferInstance : IsIso p) (inferInstance : IsIso (𝟙 (X⟦(1 : ℤ)⟧)))

/-- A nonzero connecting morphism prevents `v` from being a retraction. -/
theorem second_not_isSplitEpi : ¬ IsSplitEpi G.second := by
  intro h
  let := h
  exact G.shifted_alpha_ne_zero
    (G.triangle.mor₃_eq_zero_of_epi₂ G.triangle_distinguished
      (by change Epi G.second; infer_instance))

include k in
/-- A section `v` would make the square-zero, nonzero connecting morphism epic. -/
theorem second_not_isSplitMono : ¬ IsSplitMono G.second := by
  intro h
  let := h
  have hu : G.first = 0 :=
    G.triangle.mor₁_eq_zero_of_mono₂ G.triangle_distinguished
      (by change Mono G.second; infer_instance)
  have : Epi (G.alpha⟦(1 : ℤ)⟧') := G.triangle.epi₃ G.triangle_distinguished hu
  apply G.shifted_alpha_ne_zero
  apply (cancel_epi (G.alpha⟦(1 : ℤ)⟧')).mp
  simpa only [comp_zero] using G.shifted_alpha_sq_eq_zero (k := k)

include k in
/-- Irreducibility of `v`, derived from its right almost-split property and
right minimality instead of importing an external AR theorem. -/
theorem second_irreducible : IsIrreducibleMorphism G.second := by
  refine ⟨G.second_not_isSplitMono (k := k), G.second_not_isSplitEpi, ?_⟩
  intro Y l r hlr
  by_cases hr : IsSplitEpi r
  · exact Or.inr hr
  · obtain ⟨d, hd⟩ : ∃ d : Y ⟶ G.middle, r = d ≫ G.second :=
      G.almostSplit.2.2.2.2 r hr
    have hld : (l ≫ d) ≫ G.second = G.second := by
      rw [Category.assoc, ← hd, ← hlr]
    have : IsIso (l ≫ d) := G.second_rightMinimal (k := k) (l ≫ d) hld
    exact Or.inl (IsSplitMono.mk' ⟨d ≫ inv (l ≫ d), by simp only
      [← Category.assoc, IsIso.hom_inv_id]⟩)

/-- Remark 5.4(2): the gemstone's middle object is periodic under double
suspension, using compatibility and the triangle five lemma. -/
theorem nonempty_middlePeriodicity :
    Nonempty (G.middle ≅ G.middle⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) := by
  let D : Triangle C := Triangle.mk
    (G.first⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')
    (G.second⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')
    (G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')
  have hD : D ∈ distTriang C := by
    have hS := G.triangle.shift_distinguished G.triangle_distinguished (1 : ℤ)
    have hSS := Triangle.shift_distinguished _ hS (1 : ℤ)
    change (Triangle.shiftFunctor C (1 : ℤ)).obj
      ((Triangle.shiftFunctor C (1 : ℤ)).obj G.triangle) ∈ distTriang C at hSS
    dsimp only [Triangle.shiftFunctor, Gemstone.triangle, Triangle.mk] at hSS
    simpa only [D, Triangle.mk, Int.negOnePow_one, Units.neg_smul, one_smul, Functor.map_neg,
      shiftFunctorComm_eq_refl, Iso.refl_hom, NatTrans.id_app, Functor.comp_obj,
      Functor.map_comp, Functor.map_id, Category.comp_id, neg_neg] using hSS
  have hthird : G.alpha⟦(1 : ℤ)⟧' ≫ G.periodicity.hom⟦(1 : ℤ)⟧' =
      G.periodicity.hom⟦(1 : ℤ)⟧' ≫
        G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' := by
    simpa only [Functor.map_comp] using
      congrArg (shiftFunctor C (1 : ℤ)).map G.compatible
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b : G.middle ⟶ G.middle⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧,
      G.first ≫ b = G.periodicity.hom ≫ G.first⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ∧
      G.second ≫ G.periodicity.hom⟦(1 : ℤ)⟧' = b ≫ G.second⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' :=
    complete_distinguished_triangle_morphism₂ G.triangle D G.triangle_distinguished
      hD G.periodicity.hom (G.periodicity.hom⟦(1 : ℤ)⟧') hthird
  let phi : G.triangle ⟶ D :=
    { hom₁ := G.periodicity.hom
      hom₂ := b
      hom₃ := G.periodicity.hom⟦(1 : ℤ)⟧'
      comm₁ := hb₁
      comm₂ := hb₂
      comm₃ := hthird }
  have : IsIso b := isIso₂_of_isIso₁₃ phi G.triangle_distinguished hD
    (inferInstance : IsIso G.periodicity.hom)
    (inferInstance : IsIso (G.periodicity.hom⟦(1 : ℤ)⟧'))
  exact ⟨asIso b⟩

/-- A chosen double-suspension periodicity of the middle object, with its
existence proved above. -/
def middlePeriodicity : G.middle ≅ G.middle⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
  Classical.choice G.nonempty_middlePeriodicity

/-- The lower triangle in the diagram of Lemma 5.7, with the two negative
arrows of the shifted rotation removed by a vertex isomorphism. -/
def comparisonTriangle : Triangle C := Triangle.mk
  (G.second⟦(1 : ℤ)⟧') (G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')
  (G.first⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')

theorem comparisonTriangle_distinguished : G.comparisonTriangle ∈ distTriang C := by
  let R : Triangle C := Triangle.mk
    (-G.second⟦(1 : ℤ)⟧') (-G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')
    (G.first⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')
  have hR : R ∈ distTriang C := by
    have hS := G.triangle.shift_distinguished G.triangle_distinguished (1 : ℤ)
    have hR := rot_of_distTriang _ hS
    change ((Triangle.shiftFunctor C (1 : ℤ)).obj G.triangle).rotate ∈ distTriang C at hR
    dsimp only [Triangle.shiftFunctor, Gemstone.triangle, Triangle.rotate, Triangle.mk] at hR
    simpa only [R, Triangle.mk, Int.negOnePow_one, Units.neg_smul, one_smul,
      Functor.map_neg, shiftFunctorComm_eq_refl, Iso.refl_hom, NatTrans.id_app,
      Functor.comp_obj, Category.comp_id, neg_neg] using hR
  let minusId : X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ≅ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    { hom := -(𝟙 _)
      inv := -(𝟙 _)
      hom_inv_id := by simp
      inv_hom_id := by simp }
  let e : G.comparisonTriangle ≅ R := Triangle.isoMk _ _ (Iso.refl _) minusId (Iso.refl _)
    (by dsimp [comparisonTriangle, R, minusId, Triangle.mk]; simp)
    (by dsimp [comparisonTriangle, R, minusId, Triangle.mk]; simp)
    (by dsimp [comparisonTriangle, R, minusId, Triangle.mk]; simp)
  exact isomorphic_distinguished R hR G.comparisonTriangle e

/-- The ordinary shifted gemstone triangle, with all its signs explicit. -/
def shiftTriangle : Triangle C := Triangle.mk
  (-G.first⟦(1 : ℤ)⟧') (-G.second⟦(1 : ℤ)⟧')
  (-G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')

theorem shiftTriangle_distinguished : G.shiftTriangle ∈ distTriang C := by
  have hS := G.triangle.shift_distinguished G.triangle_distinguished (1 : ℤ)
  change (Triangle.shiftFunctor C (1 : ℤ)).obj G.triangle ∈ distTriang C at hS
  dsimp only [Triangle.shiftFunctor, Gemstone.triangle, Triangle.mk] at hS
  simpa only [shiftTriangle, Triangle.mk, Int.negOnePow_one, Units.neg_smul,
    one_smul, shiftFunctorComm_eq_refl, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_obj, Category.comp_id] using hS

include k in
/-- Finite-dimensional endomorphism spaces and double periodicity turn a
section `U → ΣU` into an isomorphism, contradicting (G3). -/
theorem not_isSplitMono_to_shift_middle (g : G.middle ⟶ G.middle⟦(1 : ℤ)⟧) :
    ¬ IsSplitMono g := by
  intro hg
  let := hg
  let h := g⟦(1 : ℤ)⟧' ≫ G.middlePeriodicity.inv
  let t := g ≫ h
  have : IsSplitMono h := by dsimp [h]; infer_instance
  have : IsSplitMono t := by dsimp [t]; infer_instance
  have : IsIso t := isIso_of_isSplitMono_endo (k := k) t
  have hright : (h ≫ inv t) ≫ g = 𝟙 (G.middle⟦(1 : ℤ)⟧) := by
    apply (cancel_mono h).mp
    calc
      ((h ≫ inv t) ≫ g) ≫ h = h ≫ (inv t ≫ t) := by simp only [t, Category.assoc]
      _ = h := by rw [IsIso.inv_hom_id, Category.comp_id]
      _ = (𝟙 _) ≫ h := (Category.id_comp h).symm
  have : IsSplitEpi g := IsSplitEpi.mk' ⟨h ≫ inv t, hright⟩
  have : IsIso g := isIso_of_mono_of_isSplitEpi g
  exact G.middle_not_periodic ⟨asIso g⟩

variable [Functor.Linear k (shiftFunctor C (1 : ℤ))] (K : GemstoneCone G)

include k in
/-- Lemma 5.6: every morphism `U → ΣU` kills the chosen nonzero factor `s`.
Its irreducibility and direct-summand inputs are consequences proved above. -/
theorem s_comp_to_shift_middle_eq_zero (g : G.middle ⟶ G.middle⟦(1 : ℤ)⟧) :
    K.s ≫ g = 0 := by
  obtain ⟨W, t, z, hT⟩ := distinguished_cocone_triangle₁ g
  let T : Triangle C := Triangle.mk t g z
  have hT' : T ∈ distTriang C := hT
  have htv : t ≫ G.second ≠ 0 := by
    intro hzero
    obtain ⟨q, hq⟩ : ∃ q : G.middle⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧,
        G.second = g ≫ q := T.yoneda_exact₂ hT' G.second hzero
    have hqepi : IsSplitEpi q := by
      rcases (G.second_irreducible (k := k)).2.2 g q hq with hg | hqepi
      · exact False.elim (G.not_isSplitMono_to_shift_middle (k := k) g hg)
      · exact hqepi
    obtain ⟨r, hr⟩ := (shiftFunctor C (1 : ℤ)).map_surjective q
    have : IsSplitEpi r := (Functor.isSplitEpi_iff (shiftFunctor C (1 : ℤ)) r).mp
      (by simpa only [hr] using hqepi)
    exact G.not_isSplitMono_to_middle (k := k) (section_ r) (inferInstance)
  obtain ⟨b, hb⟩ := G.almostVanishing.shift_one.factors_through_of_nonzero_to
    (t ≫ G.second) htv
  have hs : K.s = b ≫ t := G.rightComp_second_injective (k := k) (by
    change K.s ≫ G.second = (b ≫ t) ≫ G.second
    rw [Category.assoc, ← hb, K.factor])
  have htg : t ≫ g = 0 := comp_distTriang_mor_zero₁₂ T hT'
  rw [hs, Category.assoc, htg, comp_zero]

include k in
/-- The vanishing identity at the heart of Lemma 5.7. -/
theorem cone_map_comp_double_alpha_eq_zero
    (p : K.Y ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) :
    p ≫ G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' = 0 := by
  have hwp : ¬ IsSplitEpi (K.w ≫ p) := by
    intro hwp
    let := hwp
    have : IsSplitEpi ((K.w ≫ p) ≫ G.periodicity.inv) := inferInstance
    exact G.not_isSplitMono_to_middle (k := k)
      (section_ ((K.w ≫ p) ≫ G.periodicity.inv)) (inferInstance)
  have hwpa : (K.w ≫ p) ≫ G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' = 0 :=
    G.almostVanishing.shift_one.shift_one.precomp_eq_zero (K.w ≫ p) hwp
  obtain ⟨h, hhp⟩ : ∃ h : G.middle ⟶ G.middle⟦(1 : ℤ)⟧,
      K.w ≫ p = h ≫ G.second⟦(1 : ℤ)⟧' :=
    G.comparisonTriangle.coyoneda_exact₂ G.comparisonTriangle_distinguished (K.w ≫ p) hwpa
  let S : Triangle C := Triangle.mk K.s K.w K.z
  have hS : S ∈ distTriang C := K.distinguished
  obtain ⟨ell, hell₁, hell₂⟩ : ∃ ell : X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧,
      K.z ≫ ell = p ≫ G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ∧
      (-K.s⟦(1 : ℤ)⟧') ≫ h⟦(1 : ℤ)⟧' = ell ≫ G.first⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' :=
    complete_distinguished_triangle_morphism S.rotate G.comparisonTriangle
      (rot_of_distTriang S hS) G.comparisonTriangle_distinguished h p hhp
  have hellzero : ell ≫ G.first⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' = 0 := by
    rw [← hell₂, neg_comp, ← Functor.map_comp,
      G.s_comp_to_shift_middle_eq_zero (k := k) K h, Functor.map_zero, neg_zero]
  obtain ⟨j, hj⟩ : ∃ j : X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧,
      ell = j ≫ G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' :=
    G.comparisonTriangle.coyoneda_exact₃ G.comparisonTriangle_distinguished ell hellzero
  have hzj : ¬ IsSplitEpi (K.z ≫ j) := by
    intro hzj
    let := hzj
    have : IsSplitEpi j := IsSplitEpi.mk' ⟨section_ (K.z ≫ j) ≫ K.z, by
      rw [Category.assoc, IsSplitEpi.id]⟩
    have : IsIso j := isIso_of_isSplitEpi_endo (k := k) j
    have hz : IsSplitEpi K.z := by
      simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
        (inferInstance : IsSplitEpi ((K.z ≫ j) ≫ inv j))
    let := hz
    exact K.nonzero (S.mor₁_eq_zero_of_epi₃ hS (by change Epi K.z; infer_instance))
  calc
    p ≫ G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' = K.z ≫ ell := hell₁.symm
    _ = (K.z ≫ j) ≫ G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' := by rw [hj, Category.assoc]
    _ = 0 := G.almostVanishing.shift_one.shift_one.precomp_eq_zero (K.z ≫ j) hzj

include k in
/-- Every map `Y → Σ²X` is a non-retraction, as asserted in Lemma 5.7. -/
theorem not_isSplitEpi_cone_to_double_shift
    (p : K.Y ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) : ¬ IsSplitEpi p := by
  intro hp
  let := hp
  apply G.almostVanishing.shift_one.shift_one.nonzero
  apply (cancel_epi p).mp
  simpa only [comp_zero] using G.cone_map_comp_double_alpha_eq_zero (k := k) K p

include k in
/-- Lemma 5.7: `X` is not a direct summand of `Y`, expressed as a retract exclusion. -/
theorem lemma_5_7_no_retract : ¬ Nonempty (Retract X K.Y) := by
  rintro ⟨r⟩
  have : IsSplitEpi r.r := IsSplitEpi.mk' ⟨r.i, r.retract⟩
  exact G.not_isSplitEpi_cone_to_double_shift (k := k) K (r.r ≫ G.periodicity.hom)
    (inferInstance)

include k in
/-- Proposition 5.8: every nonzero endomorphism of `Σ²X` is excluded from the
lightning flashes on the rotated cone triangle. All dimension, AR, and
non-retraction inputs are the theorems proved from `G` above. -/
theorem proposition_5_8_not_lightning
    (f : X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) (hf : f ≠ 0) :
    ¬ IsLightningFlash (Triangle.mk K.s K.w K.z).rotate
      (Triangle.mk K.s K.w K.z).rotate f := by
  let R := (Triangle.mk K.s K.w K.z).rotate
  have hfactor : ∀ phi : G.middle⟦(1 : ℤ)⟧ ⟶ K.Y,
      ∃ eps : X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧,
        phi ≫ K.z = (-G.second⟦(1 : ℤ)⟧') ≫ eps := by
    intro phi
    exact G.shiftTriangle.yoneda_exact₂ G.shiftTriangle_distinguished (phi ≫ K.z)
      (G.shifted_rigid ((-G.first⟦(1 : ℤ)⟧') ≫ (phi ≫ K.z)))
  have hba : (-K.s⟦(1 : ℤ)⟧') ≫ (-G.second⟦(1 : ℤ)⟧') =
      G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' := by
    rw [neg_comp, comp_neg, neg_neg, ← Functor.map_comp, K.factor]
  exact not_lightning_of_irreducible_factorization (k := k) R
    (-G.second⟦(1 : ℤ)⟧') (G.alpha⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧')
    G.almostVanishing.shift_one.shift_one hba
    (G.second_irreducible (k := k)).shift_one.neg hfactor
    (G.not_isSplitMono_shift_middle_to_cone (k := k) K)
    (G.not_isSplitEpi_cone_to_double_shift (k := k) K) f hf

end Gemstone

end PretriangulatedV2
