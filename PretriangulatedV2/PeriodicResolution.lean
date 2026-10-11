import PretriangulatedV2.StableLinear
import PretriangulatedV2.FrobeniusTriangulation
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.IsField

/-!
The algebraic part of Proposition 7.1, Steps 1–2.  The alternating exact
sequence is specified in the ambient abelian category. Its cokernels,
short exact sequences, and stable periodicity are constructed, rather than
assumed. No almost-vanishing morphism or almost-split sequence is asserted.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive

namespace PretriangulatedV2.StableCategory.PeriodicResolution

universe v u w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The alternating exact sequence and the two annihilation conditions of
Proposition 7.1. Nonzeroness and indecomposability are not needed for the
algebraic conclusions established in this file. -/
structure Data (M L : C) where
  iota : L ⟶ M
  q : M ⟶ L
  iota_q : iota ≫ q = 0
  q_iota : q ≫ iota = 0
  exact_iota_q : (ShortComplex.mk iota q iota_q).Exact
  exact_q_iota : (ShortComplex.mk q iota q_iota).Exact
  annihilate_iota : ∀ f : M ⟶ L, f ≫ iota = 0
  annihilate_q : ∀ f : L ⟶ M, f ≫ q = 0

namespace Data

variable {M L : C} (D : Data M L)

abbrev X : C := cokernel D.iota
abbrev X' : C := cokernel D.q

/-- The first ambient cosyzygy embedding. -/
abbrev toL : D.X ⟶ L := cokernel.desc D.iota D.q D.iota_q

/-- The second ambient cosyzygy embedding. -/
abbrev toM : D.X' ⟶ M := cokernel.desc D.q D.iota D.q_iota

@[reassoc (attr := simp)]
theorem π_toL : cokernel.π D.iota ≫ D.toL = D.q := cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
theorem π_toM : cokernel.π D.q ≫ D.toM = D.iota := cokernel.π_desc _ _ _

instance toL_mono : Mono D.toL := D.exact_iota_q.mono_cokernelDesc
instance toM_mono : Mono D.toM := D.exact_q_iota.mono_cokernelDesc

@[reassoc (attr := simp)]
theorem toL_π : D.toL ≫ cokernel.π D.q = 0 := by
  apply (cancel_epi (cokernel.π D.iota)).mp
  simp

@[reassoc (attr := simp)]
theorem toM_π : D.toM ≫ cokernel.π D.iota = 0 := by
  apply (cancel_epi (cokernel.π D.q)).mp
  simp

abbrev firstSequence : ShortComplex C := ShortComplex.mk D.toL (cokernel.π D.q) D.toL_π
abbrev secondSequence : ShortComplex C := ShortComplex.mk D.toM (cokernel.π D.iota) D.toM_π

def firstIsCokernel : IsColimit (CokernelCofork.ofπ (cokernel.π D.q) D.toL_π) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun a ha => cokernel.desc D.q a (by rw [← D.π_toL, Category.assoc, ha, comp_zero]))
    (by intros; simp)
    (by intros; apply (cancel_epi (cokernel.π D.q)).mp; simpa)

def secondIsCokernel : IsColimit (CokernelCofork.ofπ (cokernel.π D.iota) D.toM_π) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun a ha => cokernel.desc D.iota a (by rw [← D.π_toM, Category.assoc, ha, comp_zero]))
    (by intros; simp)
    (by intros; apply (cancel_epi (cokernel.π D.iota)).mp; simpa)

theorem first_shortExact : D.firstSequence.ShortExact where
  exact := D.firstSequence.exact_of_g_is_cokernel D.firstIsCokernel

theorem second_shortExact : D.secondSequence.ShortExact where
  exact := D.secondSequence.exact_of_g_is_cokernel D.secondIsCokernel

variable [Projective M] [Projective L]

omit [Projective L] in
theorem hom_M_X'_zero (f : M ⟶ D.X') : f = 0 := by
  let a := Projective.factorThru f (cokernel.π D.q)
  have ha : a ≫ cokernel.π D.q = f := Projective.factorThru_comp _ _
  apply (cancel_mono D.toM).mp
  rw [← ha, Category.assoc, D.π_toM, D.annihilate_iota]
  simp

omit [Projective M] in
theorem hom_L_X_zero (f : L ⟶ D.X) : f = 0 := by
  let a := Projective.factorThru f (cokernel.π D.iota)
  have ha : a ≫ cokernel.π D.iota = f := Projective.factorThru_comp _ _
  apply (cancel_mono D.toL).mp
  rw [← ha, Category.assoc, D.π_toL, D.annihilate_q]
  simp

omit [Projective L] in
theorem hom_X_X'_zero (f : D.X ⟶ D.X') : f = 0 := by
  apply (cancel_epi (cokernel.π D.iota)).mp
  rw [D.hom_M_X'_zero (cokernel.π D.iota ≫ f)]
  simp

omit [Projective M] in
theorem hom_X'_X_zero (f : D.X' ⟶ D.X) : f = 0 := by
  apply (cancel_epi (cokernel.π D.q)).mp
  rw [D.hom_L_X_zero (cokernel.π D.q ≫ f)]
  simp

omit [Projective M] in
/-- Every ambient endomorphism of `M` preserves the kernel of its quotient
onto `X`: the obstruction factors through `X'`, whose Hom into `X` vanishes. -/
theorem iota_end_π_zero (a : End M) : D.iota ≫ (a ≫ cokernel.π D.iota) = 0 := by
  rw [← D.π_toM_assoc,
    D.hom_X'_X_zero (D.toM ≫ a ≫ cokernel.π D.iota), comp_zero]

/-- Descent of an actual endomorphism through the ambient cokernel. -/
abbrev endMap (a : End M) : End D.X :=
  cokernel.desc D.iota (a ≫ cokernel.π D.iota) (D.iota_end_π_zero a)

omit [Projective M] in
@[reassoc (attr := simp)]
theorem π_endMap (a : End M) :
    cokernel.π D.iota ≫ D.endMap a = a ≫ cokernel.π D.iota := cokernel.π_desc _ _ _

theorem endMap_injective : Function.Injective D.endMap := by
  intro a b hab
  have hz : (a - b) ≫ cokernel.π D.iota = 0 := by
    rw [sub_comp, ← D.π_endMap a, ← D.π_endMap b, hab, sub_self]
  obtain ⟨r, hr⟩ := KernelFork.IsLimit.lift' D.second_shortExact.fIsKernel (a - b) hz
  have he : a - b = 0 := by
    rw [← hr, D.hom_M_X'_zero r, zero_comp]
  exact sub_eq_zero.mp he

theorem endMap_surjective : Function.Surjective D.endMap := by
  intro b
  refine ⟨Projective.factorThru (cokernel.π D.iota ≫ b) (cokernel.π D.iota), ?_⟩
  apply (cancel_epi (cokernel.π D.iota)).mp
  rw [D.π_endMap, Projective.factorThru_comp]

variable {k : Type w} [Field k] [Linear k C]

/-- The ambient endomorphism algebra homomorphism, with all operations
verified by the actual cokernel projection. -/
def endAlgHom : End M →ₐ[k] End D.X where
  toFun := D.endMap
  map_one' := by
    apply (cancel_epi (cokernel.π D.iota)).mp
    simp
  map_mul' a b := by
    apply (cancel_epi (cokernel.π D.iota)).mp
    simp [End.mul_def, Category.assoc]
  map_zero' := by
    apply (cancel_epi (cokernel.π D.iota)).mp
    simp
  map_add' a b := by
    change D.endMap (a + b) = D.endMap a + D.endMap b
    apply (cancel_epi (cokernel.π D.iota)).mp
    rw [comp_add, D.π_endMap, D.π_endMap, D.π_endMap, add_comp]
  commutes' r := by
    apply (cancel_epi (cokernel.π D.iota)).mp
    rw [D.π_endMap]
    change ((algebraMap k (End M)) r) ≫ cokernel.π D.iota =
      cokernel.π D.iota ≫ ((algebraMap k (End D.X)) r)
    simp only [Algebra.algebraMap_eq_smul_one]
    change (r • 𝟙 M) ≫ cokernel.π D.iota = cokernel.π D.iota ≫ (r • 𝟙 D.X)
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

/-- The actual algebra isomorphism `End(M) ≃ End(X)` of Step 2. -/
def endAlgEquiv : End M ≃ₐ[k] End D.X :=
  AlgEquiv.ofBijective D.endAlgHom ⟨D.endMap_injective, D.endMap_surjective⟩

@[simp]
theorem endAlgEquiv_apply (a : End M) : D.endAlgEquiv (k := k) a = D.endMap a := rfl

variable [HasBinaryBiproducts C] [FrobeniusAbelian C]

/-- The cokernel of the first embedding is the other actual cokernel. -/
def firstCokernelIso : cokernel D.toL ≅ D.X' :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel D.toL) D.firstIsCokernel

/-- The cokernel of the second embedding is the original actual cokernel. -/
def secondCokernelIso : cokernel D.toM ≅ D.X :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel D.toM) D.secondIsCokernel

/-- Comparing the actual injective presentations identifies the first
chosen cosyzygy with the second cokernel in the stable quotient. -/
def firstCosyzygyIso :
    (Cosyzygy.functor (C := C)).obj ((projectiveStableQuotient (C := C)).obj D.X) ≅
      (projectiveStableQuotient (C := C)).obj D.X' := by
  let _ : Injective L := (FrobeniusAbelian.projective_iff_injective L).mp inferInstance
  exact Cosyzygy.stableCokernelIso (Injective.ι D.X) D.toL ≪≫
    (projectiveStableQuotient (C := C)).mapIso D.firstCokernelIso

def secondCosyzygyIso :
    (Cosyzygy.functor (C := C)).obj ((projectiveStableQuotient (C := C)).obj D.X') ≅
      (projectiveStableQuotient (C := C)).obj D.X := by
  let _ : Injective M := (FrobeniusAbelian.projective_iff_injective M).mp inferInstance
  exact Cosyzygy.stableCokernelIso (Injective.ι D.X') D.toM ≪≫
    (projectiveStableQuotient (C := C)).mapIso D.secondCokernelIso

/-- The genuine double cosyzygy isomorphism of Step 1. -/
def doubleCosyzygyIso :
    (Cosyzygy.functor (C := C)).obj
        ((Cosyzygy.functor (C := C)).obj ((projectiveStableQuotient (C := C)).obj D.X)) ≅
      (projectiveStableQuotient (C := C)).obj D.X :=
  (Cosyzygy.functor (C := C)).mapIso D.firstCosyzygyIso ≪≫ D.secondCosyzygyIso

omit [Projective M] [HasBinaryBiproducts C] in
/-- Factoring through an actual projective kills every endomorphism of `X`:
injectivity extends its first factor over `X → L`, and `Hom(L,X)=0`. -/
theorem projective_factor_end_zero (f : End D.X)
    (hf : PretriangulatedV2.IdealQuotient.FactorsThrough projectiveObjects f) : f = 0 := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  let _ : Projective P := hP
  let _ : Injective P := (FrobeniusAbelian.projective_iff_injective P).mp hP
  let a' := Injective.factorThru a D.toL
  have ha' : D.toL ≫ a' = a := Injective.comp_factorThru _ _
  rw [← hab, ← ha', Category.assoc, D.hom_L_X_zero (a' ≫ b), comp_zero]

omit [Projective M] in
theorem stable_endMap_injective :
    Function.Injective
      ((projectiveStableQuotient (C := C)).map : End D.X →
        End ((projectiveStableQuotient (C := C)).obj D.X)) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply D.projective_factor_end_zero
  change (a - b) ∈ PretriangulatedV2.IdealQuotient.factorIdeal projectiveObjects D.X D.X
  rw [← PretriangulatedV2.IdealQuotient.functor_map_eq_zero_iff]
  change (projectiveStableQuotient (C := C)).map (a - b) = 0
  rw [Functor.map_sub, hab, sub_self]

/-- The actual quotient map as an algebra homomorphism on endomorphisms. -/
def stableEndAlgHom : End D.X →ₐ[k]
    End ((projectiveStableQuotient (C := C)).obj D.X) where
  toFun := (projectiveStableQuotient (C := C)).map
  map_one' := CategoryTheory.Functor.map_id _ _
  map_mul' a b := Functor.map_comp _ b a
  map_zero' := CategoryTheory.Functor.map_zero _ _ _
  map_add' a b := CategoryTheory.Functor.map_add _
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change (projectiveStableQuotient (C := C)).map (r • 𝟙 D.X) =
      r • 𝟙 ((projectiveStableQuotient (C := C)).obj D.X)
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]

/-- The stable quotient introduces no further endomorphism identifications
at `X`; both injectivity and surjectivity are proved. -/
def stableEndAlgEquiv : End D.X ≃ₐ[k]
    End ((projectiveStableQuotient (C := C)).obj D.X) :=
  AlgEquiv.ofBijective D.stableEndAlgHom
    ⟨D.stable_endMap_injective, (projectiveStableQuotient (C := C)).map_surjective⟩

def projectiveStableEndAlgEquiv : End M ≃ₐ[k]
    End ((projectiveStableQuotient (C := C)).obj D.X) :=
  D.endAlgEquiv.trans D.stableEndAlgEquiv

end Data

section CentralRestriction

variable [HasBinaryBiproducts C] {M L : C}

def restrictM (c : End (M ⊞ L)) : End M := biprod.inl ≫ c ≫ biprod.fst
def restrictL (c : End (M ⊞ L)) : End L := biprod.inr ≫ c ≫ biprod.snd

/-- Centrality of an actual endomorphism of the biproduct forces its
restrictions to commute with every off-diagonal map. -/
theorem central_restrict_M_L (c : End (M ⊞ L))
    (hc : ∀ z : End (M ⊞ L), c * z = z * c) (f : M ⟶ L) :
    restrictM c ≫ f = f ≫ restrictL c := by
  have h := congrArg (fun z => biprod.inl ≫ z ≫ biprod.snd)
    (hc (biprod.fst ≫ f ≫ biprod.inr))
  simpa [restrictM, restrictL, End.mul_def, Category.assoc] using h.symm

theorem central_restrict_L_M (c : End (M ⊞ L))
    (hc : ∀ z : End (M ⊞ L), c * z = z * c) (f : L ⟶ M) :
    restrictL c ≫ f = f ≫ restrictM c := by
  have h := congrArg (fun z => biprod.inr ≫ z ≫ biprod.fst)
    (hc (biprod.snd ≫ f ≫ biprod.inl))
  simpa [restrictM, restrictL, End.mul_def, Category.assoc] using h.symm

end CentralRestriction

namespace Data

variable {M L : C} (D : Data M L) [Projective M] [Projective L]

/-- Reversing the two positions of the actual alternating resolution. -/
abbrev swap : Data L M where
  iota := D.q
  q := D.iota
  iota_q := D.q_iota
  q_iota := D.iota_q
  exact_iota_q := D.exact_q_iota
  exact_q_iota := D.exact_iota_q
  annihilate_iota := D.annihilate_q
  annihilate_q := D.annihilate_iota

omit [Projective M] in
theorem endMap_toL (a : End M) (b : End L) (h : a ≫ D.q = D.q ≫ b) :
    D.endMap a ≫ D.toL = D.toL ≫ b := by
  apply (cancel_epi (cokernel.π D.iota)).mp
  rw [← Category.assoc, D.π_endMap, Category.assoc, D.π_toL,
    ← Category.assoc, D.π_toL, h]

omit [Projective L] in
theorem endMap_toM (a : End M) (b : End L) (h : b ≫ D.iota = D.iota ≫ a) :
    D.swap.endMap b ≫ D.toM = D.toM ≫ a := D.swap.endMap_toL b a h

variable [HasBinaryBiproducts C] [FrobeniusAbelian C]

omit [Projective M] [Projective L] [FrobeniusAbelian C] [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem π_firstCokernelIso :
    cokernel.π D.toL ≫ D.firstCokernelIso.hom = cokernel.π D.q := by
  simpa [firstCokernelIso] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel D.toL) D.firstIsCokernel WalkingParallelPair.one

omit [Projective M] [Projective L] [FrobeniusAbelian C] [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem π_secondCokernelIso :
    cokernel.π D.toM ≫ D.secondCokernelIso.hom = cokernel.π D.iota := by
  simpa [secondCokernelIso] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel D.toM) D.secondIsCokernel WalkingParallelPair.one

/-- Naturality of the first chosen cosyzygy comparison for an actual pair
of endomorphisms commuting with the alternating differential. -/
theorem firstCosyzygyIso_naturality (a : End M) (b : End L)
    (hab : a ≫ D.q = D.q ≫ b) :
    (Cosyzygy.functor (C := C)).map
        ((projectiveStableQuotient (C := C)).map (D.endMap a)) ≫
        D.firstCosyzygyIso.hom =
      D.firstCosyzygyIso.hom ≫
        (projectiveStableQuotient (C := C)).map (D.swap.endMap b) := by
  let _ : Injective L := (FrobeniusAbelian.projective_iff_injective L).mp inferInstance
  have hn := Cosyzygy.comparison_naturality
    (Injective.ι D.X) (Injective.ι D.X) D.toL D.toL (D.endMap a)
    (Cosyzygy.extension (D.endMap a)) b (Cosyzygy.ι_extension _)
    (D.endMap_toL a b hab).symm
  have hm :
      cokernel.map D.toL D.toL (D.endMap a) b (D.endMap_toL a b hab).symm ≫
        D.firstCokernelIso.hom =
      D.firstCokernelIso.hom ≫ D.swap.endMap b := by
    apply (cancel_epi (cokernel.π D.toL)).mp
    simp [cokernel.map, Category.assoc]
  change (projectiveStableQuotient (C := C)).map (Cosyzygy.map (D.endMap a)) ≫
      ((projectiveStableQuotient (C := C)).map (Cosyzygy.comparison
        (Injective.ι D.X) D.toL) ≫
        (projectiveStableQuotient (C := C)).map D.firstCokernelIso.hom) = _
  change (projectiveStableQuotient (C := C)).map (Cosyzygy.map (D.endMap a)) ≫
      ((projectiveStableQuotient (C := C)).map (Cosyzygy.comparison
        (Injective.ι D.X) D.toL) ≫
        (projectiveStableQuotient (C := C)).map D.firstCokernelIso.hom) =
    ((projectiveStableQuotient (C := C)).map (Cosyzygy.comparison
        (Injective.ι D.X) D.toL) ≫
        (projectiveStableQuotient (C := C)).map D.firstCokernelIso.hom) ≫
      (projectiveStableQuotient (C := C)).map (D.swap.endMap b)
  rw [← Category.assoc]
  change ((projectiveStableQuotient (C := C)).map
      (cokernel.map (Injective.ι D.X) (Injective.ι D.X) (D.endMap a)
        (Cosyzygy.extension (D.endMap a)) (Cosyzygy.ι_extension _)) ≫ _) ≫ _ = _
  rw [hn, Category.assoc, ← CategoryTheory.Functor.map_comp, hm,
    CategoryTheory.Functor.map_comp, ← Category.assoc]

theorem secondCosyzygyIso_naturality (a : End M) (b : End L)
    (hba : b ≫ D.iota = D.iota ≫ a) :
    (Cosyzygy.functor (C := C)).map
        ((projectiveStableQuotient (C := C)).map (D.swap.endMap b)) ≫
        D.secondCosyzygyIso.hom =
      D.secondCosyzygyIso.hom ≫
        (projectiveStableQuotient (C := C)).map (D.endMap a) :=
  D.swap.firstCosyzygyIso_naturality b a hba

/-- A commuting endomorphism pair of the alternating resolution induces a
commuting square for the constructed double cosyzygy isomorphism. -/
theorem doubleCosyzygyIso_naturality (a : End M) (b : End L)
    (hab : a ≫ D.q = D.q ≫ b) (hba : b ≫ D.iota = D.iota ≫ a) :
    (Cosyzygy.functor (C := C)).map
        ((Cosyzygy.functor (C := C)).map
          ((projectiveStableQuotient (C := C)).map (D.endMap a))) ≫
        D.doubleCosyzygyIso.hom =
      D.doubleCosyzygyIso.hom ≫
        (projectiveStableQuotient (C := C)).map (D.endMap a) := by
  change _ ≫ ((Cosyzygy.functor (C := C)).map D.firstCosyzygyIso.hom ≫
    D.secondCosyzygyIso.hom) =
    ((Cosyzygy.functor (C := C)).map D.firstCosyzygyIso.hom ≫
      D.secondCosyzygyIso.hom) ≫ _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    D.firstCosyzygyIso_naturality a b hab, CategoryTheory.Functor.map_comp,
    Category.assoc, D.secondCosyzygyIso_naturality a b hba, ← Category.assoc]

/-- Proposition 7.1's central-extension hypothesis implies that the
constructed double cosyzygy acts trivially on every stable endomorphism.
The hypothesis asks only for actual central extensions on `M ⊞ L`; neither
the action conclusion nor a periodicity isomorphism is assumed. -/
theorem doubleCosyzygy_trivial_action
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧ restrictM c = a)
    (f : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (Cosyzygy.functor (C := C)).map ((Cosyzygy.functor (C := C)).map f) ≫
        D.doubleCosyzygyIso.hom = D.doubleCosyzygyIso.hom ≫ f := by
  obtain ⟨g, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
  obtain ⟨a, rfl⟩ := D.endMap_surjective g
  obtain ⟨c, hc, rfl⟩ := hcentral a
  exact D.doubleCosyzygyIso_naturality (restrictM c) (restrictL c)
    (central_restrict_M_L c hc D.q) (central_restrict_L_M c hc D.iota)

omit [Projective L] [FrobeniusAbelian C] in
/-- Hom vanishing also holds in the actual quotient. -/
theorem stable_hom_X_X'_zero
    (f : (projectiveStableQuotient (C := C)).obj D.X ⟶
      (projectiveStableQuotient (C := C)).obj D.X') : f = 0 := by
  obtain ⟨g, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
  rw [D.hom_X_X'_zero g]
  exact CategoryTheory.Functor.map_zero _ _ _

omit [Projective M] [FrobeniusAbelian C] in
theorem stable_hom_X'_X_zero
    (f : (projectiveStableQuotient (C := C)).obj D.X' ⟶
      (projectiveStableQuotient (C := C)).obj D.X) : f = 0 := by
  obtain ⟨g, rfl⟩ := (projectiveStableQuotient (C := C)).map_surjective f
  rw [D.hom_X'_X_zero g]
  exact CategoryTheory.Functor.map_zero _ _ _

/-- The double cosyzygy isomorphism expressed with the actual canonical
integer shift of the stable quotient. -/
def doubleShiftIso :
    (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).obj
        ((shiftFunctor (projectiveStableCategory C) (1 : ℤ)).obj
          ((projectiveStableQuotient (C := C)).obj D.X)) ≅
      (projectiveStableQuotient (C := C)).obj D.X :=
  (cosyzygyIsoShift (C := C)).symm.app _ ≪≫
    (Cosyzygy.functor (C := C)).mapIso ((cosyzygyIsoShift (C := C)).symm.app _) ≪≫
      D.doubleCosyzygyIso

/-- Central extensions also give the trivial action for the actual shift,
under the explicitly constructed periodicity isomorphism. -/
theorem doubleShift_trivial_action
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧ restrictM c = a)
    (f : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    (shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map
        ((shiftFunctor (projectiveStableCategory C) (1 : ℤ)).map f) ≫
        D.doubleShiftIso.hom = D.doubleShiftIso.hom ≫ f := by
  let e := (cosyzygyIsoShift (C := C)).symm
  change _ ≫ (e.hom.app _ ≫
    ((Cosyzygy.functor (C := C)).map (e.hom.app _) ≫ D.doubleCosyzygyIso.hom)) = _
  rw [← Category.assoc, e.hom.naturality, Category.assoc,
    ← Category.assoc ((Cosyzygy.functor (C := C)).map _),
    ← CategoryTheory.Functor.map_comp, e.hom.naturality,
    CategoryTheory.Functor.map_comp, Category.assoc,
    D.doubleCosyzygy_trivial_action hcentral f]
  simp only [doubleShiftIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Category.assoc]
  rfl

def firstShiftIso :
    ((projectiveStableQuotient (C := C)).obj D.X)⟦(1 : ℤ)⟧ ≅
      (projectiveStableQuotient (C := C)).obj D.X' :=
  (cosyzygyIsoShift (C := C)).symm.app _ ≪≫ D.firstCosyzygyIso

def shiftTwoIso :
    ((projectiveStableQuotient (C := C)).obj D.X)⟦(2 : ℤ)⟧ ≅
      (projectiveStableQuotient (C := C)).obj D.X :=
  (shiftFunctorAdd (projectiveStableCategory C) (1 : ℤ) 1).app _ ≪≫ D.doubleShiftIso

theorem stable_hom_X_shift_one_zero
    (f : (projectiveStableQuotient (C := C)).obj D.X ⟶
      ((projectiveStableQuotient (C := C)).obj D.X)⟦(1 : ℤ)⟧) : f = 0 := by
  apply (cancel_mono D.firstShiftIso.hom).mp
  rw [D.stable_hom_X_X'_zero (f ≫ D.firstShiftIso.hom), zero_comp]

omit [Projective M] in
theorem stable_hom_shift_one_X_zero
    (f : ((projectiveStableQuotient (C := C)).obj D.X)⟦(1 : ℤ)⟧ ⟶
      (projectiveStableQuotient (C := C)).obj D.X) : f = 0 := by
  apply (cancel_epi D.firstShiftIso.inv).mp
  rw [D.stable_hom_X'_X_zero (D.firstShiftIso.inv ≫ f), comp_zero]

/-- The direction used by the gemstone definition. -/
def periodicity : (projectiveStableQuotient (C := C)).obj D.X ≅
    ((projectiveStableQuotient (C := C)).obj D.X)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
  D.doubleShiftIso.symm

theorem periodicity_compatible
    (hcentral : ∀ a : End M, ∃ c : End (M ⊞ L),
      (∀ z : End (M ⊞ L), c * z = z * c) ∧ restrictM c = a)
    (f : End ((projectiveStableQuotient (C := C)).obj D.X)) :
    f ≫ D.periodicity.hom = D.periodicity.hom ≫ f⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' := by
  apply (cancel_mono D.doubleShiftIso.hom).mp
  simp only [periodicity, Iso.symm_hom, Category.assoc]
  rw [Iso.inv_hom_id, Category.comp_id, D.doubleShift_trivial_action hcentral f]
  simp

theorem stable_X_not_isZero (hiota : D.iota ≠ 0) :
    ¬ IsZero ((projectiveStableQuotient (C := C)).obj D.X) := by
  intro h
  have hmap : (projectiveStableQuotient (C := C)).map (𝟙 D.X) =
      (projectiveStableQuotient (C := C)).map (0 : End D.X) := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact h.eq_of_src _ _
  have hidX : (𝟙 D.X) = 0 := D.stable_endMap_injective hmap
  have hmapM : D.endMap (𝟙 M) = D.endMap (0 : End M) := by
    apply (cancel_epi (cokernel.π D.iota)).mp
    rw [D.π_endMap, D.π_endMap, zero_comp, Category.id_comp]
    have hp : cokernel.π D.iota = 0 := by
      rw [← Category.comp_id (cokernel.π D.iota), hidX, comp_zero]
    exact hp
  have hidM : (𝟙 M) = 0 := D.endMap_injective hmapM
  exact hiota (by rw [← Category.comp_id D.iota, hidM, comp_zero])

theorem X_not_projective (hiota : D.iota ≠ 0) : ¬ Projective D.X := by
  intro h
  let _ : Projective D.X := h
  exact D.stable_X_not_isZero hiota (isZero_projectiveStableQuotient_obj D.X)

variable {k : Type w} [Field k] [Linear k C]

include k

theorem stable_end_commutative (hcomm : ∀ a b : End M, a * b = b * a)
    (f g : End ((projectiveStableQuotient (C := C)).obj D.X)) : f * g = g * f := by
  obtain ⟨a, rfl⟩ := (D.projectiveStableEndAlgEquiv (k := k)).surjective f
  obtain ⟨b, rfl⟩ := (D.projectiveStableEndAlgEquiv (k := k)).surjective g
  rw [← map_mul, hcomm a b, map_mul]

/-- The nonfield property in Proposition 7.1 also passes through the proved
algebra isomorphism; it is not an additional stable-category assumption. -/
theorem stable_end_not_isField (hnot : ¬ IsField (End M)) :
    ¬ IsField (End ((projectiveStableQuotient (C := C)).obj D.X)) := by
  intro hf
  let e := D.projectiveStableEndAlgEquiv (k := k)
  apply hnot
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hf.exists_pair_ne
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective h)⟩
  · intro a b
    apply e.injective
    simpa only [map_mul] using hf.mul_comm (e a) (e b)
  · intro a ha
    have hea : e a ≠ 0 := by
      intro h
      exact ha (e.injective (by simpa using h))
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel hea
    refine ⟨e.symm b, e.injective ?_⟩
    simpa only [map_mul, AlgEquiv.apply_symm_apply, map_one] using hb

end Data

end PretriangulatedV2.StableCategory.PeriodicResolution
