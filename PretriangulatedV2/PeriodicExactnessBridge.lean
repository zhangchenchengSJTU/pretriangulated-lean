import PretriangulatedV2.ComplexInjectiveExtensions

/-!
Equivalence between the arbitrary-witness definition of a Heller-exact
truncation and the canonical cycles construction for an actual periodic complex.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PretriangulatedV2.StableCategory.InjectiveComparison
open PretriangulatedV2.StableCategory.ComplexInjectiveExtensions
open PretriangulatedV2.StableCategory.PeriodicComplexes

namespace PretriangulatedV2.StableCategory.PeriodicExactnessBridge

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C] (S : C ≌ C) [S.functor.Additive]

/-- An arbitrary actual exact-row witness for the specified periodic
truncation, retaining its ambient vertex identifications and squares. -/
structure RowWitness (P : SComplex S) where
  M : C
  E : Extension3 M (S.functor.obj M)
  e₀ : E.I₀ ≅ P.complex.X 0
  e₁ : E.I₁ ≅ P.complex.X 1
  e₂ : E.I₂ ≅ P.complex.X 2
  comm₀ : E.d₀ ≫ e₁.hom = e₀.hom ≫ P.complex.d 0 1
  comm₁ : E.d₁ ≫ e₂.hom = e₁.hom ≫ P.complex.d 1 2
  comm₂ : E.p₂ ≫ S.functor.map (E.i₀ ≫ e₀.hom) =
    e₂.hom ≫ (P.complex.d 2 3 ≫ (P.period 3).inv)

namespace RowWitness

variable {S} {P : SComplex S} (W : RowWitness S P)

def initialIso : W.M ≅ P.complex.cycles 0 :=
  initialCycleIso S P W.E W.e₀ W.e₁ W.comm₀

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive] in
theorem initialIso_hom_iCycles :
    W.initialIso.hom ≫ P.complex.iCycles 0 = W.E.i₀ ≫ W.e₀.hom :=
  initialCycleIso_hom_iCycles S P W.E W.e₀ W.e₁ W.comm₀

/-- The endpoint of any exact-row witness is the actual third cycles. -/
def endpointIso : S.functor.obj W.M ≅ P.complex.cycles 3 :=
  S.functor.mapIso W.initialIso ≪≫ P.periodicityCycleIso

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem endpointIso_hom_iCycles :
    W.endpointIso.hom ≫ P.complex.iCycles 3 =
      S.functor.map (W.E.i₀ ≫ W.e₀.hom) ≫ (P.period 3).hom := by
  rw [endpointIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    P.periodicityCycleIso_hom_iCycles, ← Category.assoc, ← S.functor.map_comp,
    W.initialIso_hom_iCycles]

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive] in
theorem right_boundary :
    W.E.p₂ ≫ (S.functor.map (W.E.i₀ ≫ W.e₀.hom) ≫ (P.period 3).hom) =
      W.e₂.hom ≫ P.complex.d 2 3 := by
  have h := congrArg (fun f => f ≫ (P.period 3).hom) W.comm₂
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

include W in
omit [HasBinaryBiproducts C] [FrobeniusAbelian C] [S.functor.Additive] in
theorem exactAt₁ : P.complex.ExactAt 1 := by
  have hU := splice_exact W.E.exact₁ W.E.p₀ W.E.i₂
  let U : ShortComplex C := ShortComplex.mk W.E.d₀ W.E.d₁ (by
    simp only [Extension3.d₀, Extension3.d₁, Category.assoc,
      ← Category.assoc W.E.i₁ W.E.p₁ W.E.i₂, W.E.zero₁, zero_comp, comp_zero])
  have hU' : U.Exact := hU
  let e : U ≅ P.complex.sc' 0 1 2 :=
    ShortComplex.isoMk W.e₀ W.e₁ W.e₂ W.comm₀.symm W.comm₁.symm
  apply (P.complex.exactAt_iff' 0 1 2 (by simp) (by simp)).mpr
  exact ShortComplex.exact_of_iso e hU'

include W in
omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem exactAt₂ : P.complex.ExactAt 2 := by
  let b := S.functor.map (W.E.i₀ ≫ W.e₀.hom) ≫ (P.period 3).hom
  have : Mono b := by dsimp [b]; infer_instance
  have hU := splice_exact W.E.exact₂ W.E.p₁ b
  let U : ShortComplex C := ShortComplex.mk W.E.d₁ (W.E.p₂ ≫ b) (by
    simp only [Extension3.d₁, Category.assoc, ← Category.assoc W.E.i₂ W.E.p₂ b,
      W.E.zero₂, zero_comp, comp_zero])
  have hU' : U.Exact := hU
  let e : U ≅ P.complex.sc' 1 2 3 :=
    ShortComplex.isoMk W.e₁ W.e₂ (Iso.refl _) W.comm₁.symm (by
      change W.e₂.hom ≫ P.complex.d 2 3 = (W.E.p₂ ≫ b) ≫ 𝟙 _
      simpa only [Category.comp_id, b] using W.right_boundary.symm)
  apply (P.complex.exactAt_iff' 1 2 3 (by simp) (by simp)).mpr
  exact ShortComplex.exact_of_iso e hU'

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem toCycles_endpoint :
    W.e₂.hom ≫ P.complex.toCycles 2 3 = W.E.p₂ ≫ W.endpointIso.hom := by
  apply (cancel_mono (P.complex.iCycles 3)).mp
  rw [Category.assoc, toCycles_i, Category.assoc, W.endpointIso_hom_iCycles]
  exact W.right_boundary.symm

include W in
omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem exactAt₃ : P.complex.ExactAt 3 := by
  have : Epi (W.e₂.hom ≫ P.complex.toCycles 2 3) := by
    rw [W.toCycles_endpoint]
    infer_instance
  have : Epi (P.complex.toCycles 2 3) := epi_of_epi W.e₂.hom _
  have : Epi ((P.complex.sc' 2 3 4).toCycles) := by
    have hep : Epi (P.complex.toCycles 2 3 ≫
        (P.complex.cyclesIsoSc' 2 3 4 (by simp) (by simp)).hom) := inferInstance
    rw [toCycles_cyclesIsoSc'_hom] at hep
    exact hep
  apply (P.complex.exactAt_iff' 2 3 4 (by simp) (by simp)).mpr
  exact (P.complex.sc' 2 3 4).exact_iff_epi_toCycles.mpr this

/-- The arbitrary exact-row witness maps to the actual canonical cycles row.
All intermediate morphisms are forced by actual cokernel universal properties. -/
def canonicalHom : W.E.Hom (periodicExtension S P W.exactAt₁ W.exactAt₂ W.exactAt₃) :=
  Extension3.Hom.ofSplicedMap W.initialIso.hom W.e₀.hom W.e₁.hom W.e₂.hom
    (S.functor.map W.initialIso.hom)
    W.initialIso_hom_iCycles.symm
    (by
      simpa only [periodicExtension, transportEndpoint, extensionLocal, Extension3.d₀,
        toCycles_i] using W.comm₀)
    (by
      simpa only [periodicExtension, transportEndpoint, extensionLocal, Extension3.d₁,
        toCycles_i] using W.comm₁)
    (by
      have h := congrArg (fun f => f ≫ P.periodicityCycleIso.inv) W.toCycles_endpoint
      simpa only [periodicExtension, transportEndpoint, extensionLocal, endpointIso,
        Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
        using h.symm)

/-- δ-exactness transfers to the canonical actual cycles row by the proved
three-step comparison and the naturality of the genuine Heller parameter. -/
theorem deltaExact_canonical (p : HellerExactness.Parameter S)
    (hE : HellerExactness.DeltaExact S p W.E) : DeltaExactPeriodic S p P := by
  refine ⟨W.exactAt₁, W.exactAt₂, W.exactAt₃, ?_⟩
  apply (HellerExactness.deltaExact_iff_stableComparison S p _).mpr
  apply (cancel_epi (Q.map (S.functor.map W.initialIso.hom))).mp
  calc
    Q.map (S.functor.map W.initialIso.hom) ≫
        (periodicExtension S P W.exactAt₁ W.exactAt₂ W.exactAt₃).stableComparison.hom =
      W.E.stableComparison.hom ≫ (cube F).map (Q.map W.initialIso.hom) :=
        W.canonicalHom.stableComparison_naturality
    _ = p.delta.hom.app (Q.obj W.M) ≫ (cube F).map (Q.map W.initialIso.hom) := by
      rw [(HellerExactness.deltaExact_iff_stableComparison S p W.E).mp hE]
    _ = Q.map (S.functor.map W.initialIso.hom) ≫
        p.delta.hom.app (Q.obj (P.complex.cycles 0)) :=
      (p.delta.hom.naturality (Q.map W.initialIso.hom)).symm

end RowWitness

theorem periodic_of_deltaExactTruncation (p : HellerExactness.Parameter S)
    (P : SComplex S)
    (hP : HellerExactness.DeltaExactTruncation S p (P.complex.d 0 1)
      (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv)) :
    DeltaExactPeriodic S p P := by
  obtain ⟨M, E, e₀, e₁, e₂, h₀, h₁, h₂, hE⟩ := hP
  let W : RowWitness S P := ⟨M, E, e₀, e₁, e₂, h₀, h₁, h₂⟩
  exact W.deltaExact_canonical p hE

/-- The canonical cycles predicate has exactly the arbitrary-witness
δ-exact truncation hypotheses of Section 3. -/
theorem deltaExactPeriodic_iff_truncation (p : HellerExactness.Parameter S)
    (P : SComplex S) :
    DeltaExactPeriodic S p P ↔
      HellerExactness.DeltaExactTruncation S p (P.complex.d 0 1)
        (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv) :=
  ⟨deltaExactTruncation_of_periodic S p P, periodic_of_deltaExactTruncation S p P⟩

/-- Lemma 4.1 for arbitrary actual δ-exact truncation witnesses and an actual
cochain map. The proof uses the actual periodicity operation, genuine kernels,
and the derived three-step stable comparison; no comparison identity is assumed. -/
theorem lemma_4_1 (p : HellerExactness.Parameter S) (u : TriangleCenterUnit F)
    (P R : SComplex S)
    (hP : HellerExactness.DeltaExactTruncation S p (P.complex.d 0 1)
      (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv))
    (hR : HellerExactness.DeltaExactTruncation S (p.twist u) (R.complex.d 0 1)
      (R.complex.d 1 2) (R.complex.d 2 3 ≫ (R.period 3).inv))
    (f : P.complex ⟶ R.complex) :
    Q.map (cyclesMap (P.twistMap R f) 0) =
      u.iso.hom.app (Q.obj (P.complex.cycles 0)) ≫ Q.map (cyclesMap f 0) :=
  ComplexInjectiveExtensions.lemma_4_1 S p u P R
    (periodic_of_deltaExactTruncation S p P hP)
    (periodic_of_deltaExactTruncation S (p.twist u) R hR) f

/-- The actual acyclic projective complex underlying a periodic complex. -/
def kacObject (P : SComplex S) (hP : P.complex.Acyclic) :
    StableCocycles.AcyclicProjectiveComplex C := ⟨P.complex, P.projective, hP⟩

/-- The genuine cochain-homotopy class, rather than an abstract map symbol. -/
def homotopyClass (P R : SComplex S) (hP : P.complex.Acyclic) (hR : R.complex.Acyclic)
    (f : P.complex ⟶ R.complex) :
    (CategoryTheory.Quotient.functor (StableCocycles.acyclicHomotopyRelation (C := C))).obj
        (kacObject S P hP) ⟶
      (CategoryTheory.Quotient.functor (StableCocycles.acyclicHomotopyRelation (C := C))).obj
        (kacObject S R hR) :=
  (CategoryTheory.Quotient.functor (StableCocycles.acyclicHomotopyRelation (C := C))).map ⟨f⟩

omit [FrobeniusAbelian C] [S.functor.Additive] in
/-- The descended zero-cycle functor agrees with the actual cochain cycle map. -/
theorem homotopyClass_zeroCycles (P R : SComplex S)
    (hP : P.complex.Acyclic) (hR : R.complex.Acyclic) (f : P.complex ⟶ R.complex) :
    (StableCocycles.acyclicStableCycles (C := C)).map (homotopyClass S P R hP hR f) =
      Q.map (cyclesMap f 0) := rfl

/-- The final assertion of Lemma 4.1, using an actual isomorphism in `K_ac(P)`
and the proved descent of zero cycles through genuine cochain homotopy. -/
theorem lemma_4_1_iso (p : HellerExactness.Parameter S) (u : TriangleCenterUnit F)
    (P R : SComplex S)
    (hP : HellerExactness.DeltaExactTruncation S p (P.complex.d 0 1)
      (P.complex.d 1 2) (P.complex.d 2 3 ≫ (P.period 3).inv))
    (hR : HellerExactness.DeltaExactTruncation S (p.twist u) (R.complex.d 0 1)
      (R.complex.d 1 2) (R.complex.d 2 3 ≫ (R.period 3).inv))
    (hPAc : P.complex.Acyclic) (hRAc : R.complex.Acyclic)
    (f : P.complex ⟶ R.complex)
    [IsIso (homotopyClass S P R hPAc hRAc f)] :
    u.iso.hom.app (Q.obj (P.complex.cycles 0)) =
      (StableCocycles.acyclicStableCycles (C := C)).map
        (homotopyClass S P R hPAc hRAc (P.twistMap R f) ≫
          inv (homotopyClass S P R hPAc hRAc f)) := by
  let Z := StableCocycles.acyclicStableCycles (C := C)
  have h := lemma_4_1 S p u P R hP hR f
  have h' : Z.map (homotopyClass S P R hPAc hRAc (P.twistMap R f)) =
      u.iso.hom.app (Q.obj (P.complex.cycles 0)) ≫
        Z.map (homotopyClass S P R hPAc hRAc f) := h
  symm
  rw [Z.map_comp, h', Category.assoc, ← Z.map_comp, IsIso.hom_inv_id, Z.map_id]
  erw [Category.comp_id]

end PretriangulatedV2.StableCategory.PeriodicExactnessBridge
