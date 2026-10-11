import PretriangulatedV2.FrobeniusTriangles
import PretriangulatedV2.FrobeniusCommutation

/-!
Actual three-step injective extensions and their stable comparison maps.
The endpoint commutation is derived from the ambient short exact diagrams.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.StableCategory.InjectiveComparison

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]

abbrev Q : C ⥤ projectiveStableCategory C := projectiveStableQuotient
abbrev F : projectiveStableCategory C ⥤ projectiveStableCategory C := Cosyzygy.functor

/-- The short exact row between consecutive actual kernels of an exact pair
of differentials. -/
def cyclesSequence {P₀ P₁ P₂ : C} (d₀ : P₀ ⟶ P₁) (d₁ : P₁ ⟶ P₂)
    (h : d₀ ≫ d₁ = 0) : ShortComplex C :=
  ShortComplex.mk (kernel.ι d₀) (kernel.lift d₁ d₀ h) (by
    apply (cancel_mono (kernel.ι d₁)).mp
    simp)

omit [HasBinaryBiproducts C] [FrobeniusAbelian C] in
theorem cyclesSequence_shortExact {P₀ P₁ P₂ : C}
    (d₀ : P₀ ⟶ P₁) (d₁ : P₁ ⟶ P₂) (h : d₀ ≫ d₁ = 0)
    (hex : (ShortComplex.mk d₀ d₁ h).Exact) : (cyclesSequence d₀ d₁ h).ShortExact := by
  let φ : cyclesSequence d₀ d₁ h ⟶ ShortComplex.kernelSequence d₀ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι d₁
      comm₁₂ := by simp [cyclesSequence, ShortComplex.kernelSequence]
      comm₂₃ := by simp [cyclesSequence, ShortComplex.kernelSequence] }
  have : Epi (kernel.lift d₁ d₀ h) := hex.epi_kernelLift
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
    have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
    have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
    apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    exact ShortComplex.kernelSequence_exact d₀
  · dsimp [cyclesSequence]; infer_instance
  · dsimp [cyclesSequence]; infer_instance

/-- The ordinary cokernel of the first map is the last object of a short
exact sequence, with the actual universal-property maps retained. -/
def shortExactCokernelIso {T : ShortComplex C} (hT : T.ShortExact) :
    cokernel T.f ≅ T.X₃ where
  hom := cokernel.desc T.f T.g T.zero
  inv := FrobeniusTriangles.desc hT (cokernel.π T.f) (cokernel.condition _)
  hom_inv_id := by
    apply (cancel_epi (cokernel.π T.f)).mp
    simp
  inv_hom_id := by
    have := hT.epi_g
    apply (cancel_epi T.g).mp
    simp

/-- An injective short exact presentation compares to the chosen cosyzygy
by an isomorphism in the genuine projective stable quotient. -/
def connectingIso {T : ShortComplex C} (hT : T.ShortExact) [Injective T.X₂] :
    Q.obj T.X₃ ≅ F.obj (Q.obj T.X₁) := by
  have := hT.mono_f
  exact Q.mapIso (shortExactCokernelIso hT).symm ≪≫
    Cosyzygy.stableCokernelIso T.f (Injective.ι T.X₁)

theorem connectingIso_hom {T : ShortComplex C} (hT : T.ShortExact)
    [Injective T.X₂] :
    (connectingIso hT).hom = Q.map (FrobeniusTriangles.connecting hT) := by
  have := hT.epi_g
  have := hT.mono_f
  change Q.map (shortExactCokernelIso hT).inv ≫
      Q.map (Cosyzygy.comparison T.f (Injective.ι T.X₁)) =
    Q.map (FrobeniusTriangles.connecting hT)
  rw [← Q.map_comp]
  congr 1
  apply (cancel_epi T.g).mp
  simp [shortExactCokernelIso, Cosyzygy.π_comparison,
    FrobeniusTriangles.connecting, FrobeniusTriangles.extension]

/-- Three actual short exact sequences, whose splice is the exact row
`0 → M → I₀ → I₁ → I₂ → N → 0`. -/
structure Extension3 (M N : C) where
  Z₁ : C
  Z₂ : C
  I₀ : C
  I₁ : C
  I₂ : C
  i₀ : M ⟶ I₀
  p₀ : I₀ ⟶ Z₁
  i₁ : Z₁ ⟶ I₁
  p₁ : I₁ ⟶ Z₂
  i₂ : Z₂ ⟶ I₂
  p₂ : I₂ ⟶ N
  zero₀ : i₀ ≫ p₀ = 0
  zero₁ : i₁ ≫ p₁ = 0
  zero₂ : i₂ ≫ p₂ = 0
  exact₀ : (ShortComplex.mk i₀ p₀ zero₀).ShortExact
  exact₁ : (ShortComplex.mk i₁ p₁ zero₁).ShortExact
  exact₂ : (ShortComplex.mk i₂ p₂ zero₂).ShortExact
  injective₀ : Injective I₀
  injective₁ : Injective I₁
  injective₂ : Injective I₂

namespace Extension3

variable {M N : C} (E : Extension3 M N)

abbrev row₀ : ShortComplex C := ShortComplex.mk E.i₀ E.p₀ E.zero₀
abbrev row₁ : ShortComplex C := ShortComplex.mk E.i₁ E.p₁ E.zero₁
abbrev row₂ : ShortComplex C := ShortComplex.mk E.i₂ E.p₂ E.zero₂

instance : Injective E.I₀ := E.injective₀
instance : Injective E.I₁ := E.injective₁
instance : Injective E.I₂ := E.injective₂

instance : Mono E.i₀ := E.exact₀.mono_f
instance : Mono E.i₁ := E.exact₁.mono_f
instance : Mono E.i₂ := E.exact₂.mono_f
instance : Epi E.p₀ := E.exact₀.epi_g
instance : Epi E.p₁ := E.exact₁.epi_g
instance : Epi E.p₂ := E.exact₂.epi_g

abbrev d₀ : E.I₀ ⟶ E.I₁ := E.p₀ ≫ E.i₁
abbrev d₁ : E.I₁ ⟶ E.I₂ := E.p₁ ≫ E.i₂

/-- The comparison of a genuine three-step injective extension with the
three iterated chosen cosyzygies. -/
def stableComparison : Q.obj N ≅ (cube F).obj (Q.obj M) :=
  connectingIso E.exact₂ ≪≫ F.mapIso (connectingIso E.exact₁) ≪≫
    F.mapIso (F.mapIso (connectingIso E.exact₀))

theorem stableComparison_hom :
    E.stableComparison.hom =
      Q.map (FrobeniusTriangles.connecting E.exact₂) ≫
      F.map (Q.map (FrobeniusTriangles.connecting E.exact₁)) ≫
      F.map (F.map (Q.map (FrobeniusTriangles.connecting E.exact₀))) := by
  simp only [stableComparison, Iso.trans_hom, Functor.mapIso_hom,
    connectingIso_hom]

/-- A strictly commutative morphism of the three actual short exact rows. -/
structure Hom {M' N' : C} (E' : Extension3 M' N') where
  f₀ : M ⟶ M'
  f₁ : E.Z₁ ⟶ E'.Z₁
  f₂ : E.Z₂ ⟶ E'.Z₂
  f₃ : N ⟶ N'
  a₀ : E.I₀ ⟶ E'.I₀
  a₁ : E.I₁ ⟶ E'.I₁
  a₂ : E.I₂ ⟶ E'.I₂
  comm_i₀ : E.i₀ ≫ a₀ = f₀ ≫ E'.i₀
  comm_p₀ : E.p₀ ≫ f₁ = a₀ ≫ E'.p₀
  comm_i₁ : E.i₁ ≫ a₁ = f₁ ≫ E'.i₁
  comm_p₁ : E.p₁ ≫ f₂ = a₁ ≫ E'.p₁
  comm_i₂ : E.i₂ ≫ a₂ = f₂ ≫ E'.i₂
  comm_p₂ : E.p₂ ≫ f₃ = a₂ ≫ E'.p₂

namespace Hom

variable {M' N' : C} {E : Extension3 M N} {E' : Extension3 M' N'}
  (φ : E.Hom E')

def row₀ : E.row₀ ⟶ E'.row₀ where
  τ₁ := φ.f₀
  τ₂ := φ.a₀
  τ₃ := φ.f₁
  comm₁₂ := φ.comm_i₀.symm
  comm₂₃ := φ.comm_p₀.symm

def row₁ : E.row₁ ⟶ E'.row₁ where
  τ₁ := φ.f₁
  τ₂ := φ.a₁
  τ₃ := φ.f₂
  comm₁₂ := φ.comm_i₁.symm
  comm₂₃ := φ.comm_p₁.symm

def row₂ : E.row₂ ⟶ E'.row₂ where
  τ₁ := φ.f₂
  τ₂ := φ.a₂
  τ₃ := φ.f₃
  comm₁₂ := φ.comm_i₂.symm
  comm₂₃ := φ.comm_p₂.symm

/-- The comparison lemma for three injective steps: this endpoint square is
proved from the three ambient short exact diagrams. -/
theorem stableComparison_naturality :
    Q.map φ.f₃ ≫ E'.stableComparison.hom =
      E.stableComparison.hom ≫ (cube F).map (Q.map φ.f₀) := by
  have h₀ := FrobeniusTriangles.connecting_naturality E.exact₀ E'.exact₀ φ.row₀
  have h₁ := FrobeniusTriangles.connecting_naturality E.exact₁ E'.exact₁ φ.row₁
  have h₂ := FrobeniusTriangles.connecting_naturality E.exact₂ E'.exact₂ φ.row₂
  change Q.map (FrobeniusTriangles.connecting E.exact₀) ≫ F.map (Q.map φ.f₀) =
    Q.map φ.f₁ ≫ Q.map (FrobeniusTriangles.connecting E'.exact₀) at h₀
  change Q.map (FrobeniusTriangles.connecting E.exact₁) ≫ F.map (Q.map φ.f₁) =
    Q.map φ.f₂ ≫ Q.map (FrobeniusTriangles.connecting E'.exact₁) at h₁
  change Q.map (FrobeniusTriangles.connecting E.exact₂) ≫ F.map (Q.map φ.f₂) =
    Q.map φ.f₃ ≫ Q.map (FrobeniusTriangles.connecting E'.exact₂) at h₂
  rw [stableComparison_hom, stableComparison_hom]
  simp only [cube, Functor.comp_map, Category.assoc]
  have h₀' := congrArg F.map (congrArg F.map h₀)
  simp only [F.map_comp] at h₀'
  have h₁' := congrArg F.map h₁
  simp only [F.map_comp] at h₁'
  erw [← Category.assoc (Q.map φ.f₃)
    (Q.map (FrobeniusTriangles.connecting E'.exact₂)), ← h₂]
  simp only [Category.assoc]
  erw [← Category.assoc (F.map (Q.map φ.f₂))
    (F.map (Q.map (FrobeniusTriangles.connecting E'.exact₁))), ← h₁']
  simp only [Category.assoc]
  erw [← h₀']

end Hom

namespace Hom

variable {M' N' : C} {E : Extension3 M N} {E' : Extension3 M' N'}

/-- A cochain map of the spliced exact rows induces a genuine map on each
intermediate cokernel; these maps are constructed rather than supplied. -/
def ofSplicedMap (f₀ : M ⟶ M') (a₀ : E.I₀ ⟶ E'.I₀)
    (a₁ : E.I₁ ⟶ E'.I₁) (a₂ : E.I₂ ⟶ E'.I₂) (f₃ : N ⟶ N')
    (h₀ : E.i₀ ≫ a₀ = f₀ ≫ E'.i₀)
    (h₁ : E.d₀ ≫ a₁ = a₀ ≫ E'.d₀)
    (h₂ : E.d₁ ≫ a₂ = a₁ ≫ E'.d₁)
    (h₃ : E.p₂ ≫ f₃ = a₂ ≫ E'.p₂) : E.Hom E' := by
  let f₁ : E.Z₁ ⟶ E'.Z₁ := FrobeniusTriangles.desc E.exact₀ (a₀ ≫ E'.p₀)
    (by rw [← Category.assoc, h₀, Category.assoc, E'.zero₀, comp_zero])
  have hp₀ : E.p₀ ≫ f₁ = a₀ ≫ E'.p₀ := FrobeniusTriangles.g_desc E.exact₀ _ _
  have hi₁ : E.i₁ ≫ a₁ = f₁ ≫ E'.i₁ := by
    apply (cancel_epi E.p₀).mp
    simpa only [d₀, Category.assoc, ← Category.assoc E.p₀ f₁ E'.i₁, hp₀] using h₁
  let f₂ : E.Z₂ ⟶ E'.Z₂ := FrobeniusTriangles.desc E.exact₁ (a₁ ≫ E'.p₁)
    (by rw [← Category.assoc, hi₁, Category.assoc, E'.zero₁, comp_zero])
  have hp₁ : E.p₁ ≫ f₂ = a₁ ≫ E'.p₁ := FrobeniusTriangles.g_desc E.exact₁ _ _
  have hi₂ : E.i₂ ≫ a₂ = f₂ ≫ E'.i₂ := by
    apply (cancel_epi E.p₁).mp
    simpa only [d₁, Category.assoc, ← Category.assoc E.p₁ f₂ E'.i₂, hp₁] using h₂
  exact ⟨f₀, f₁, f₂, f₃, a₀, a₁, a₂, h₀, hp₀, hi₁, hp₁, hi₂, h₃⟩

end Hom

/-- A comparison diagram to the three chosen injective presentations.  These
are the four ambient squares in the definition of a Heller-exact row. -/
structure Comparison where
  a₀ : E.I₀ ⟶ Injective.under M
  a₁ : E.I₁ ⟶ Injective.under (Cosyzygy.obj M)
  a₂ : E.I₂ ⟶ Injective.under (Cosyzygy.obj (Cosyzygy.obj M))
  c : N ⟶ Cosyzygy.obj (Cosyzygy.obj (Cosyzygy.obj M))
  comm₀ : E.i₀ ≫ a₀ = Injective.ι M
  comm₁ : E.d₀ ≫ a₁ = a₀ ≫ cokernel.π (Injective.ι M) ≫
    Injective.ι (Cosyzygy.obj M)
  comm₂ : E.d₁ ≫ a₂ = a₁ ≫ cokernel.π (Injective.ι (Cosyzygy.obj M)) ≫
    Injective.ι (Cosyzygy.obj (Cosyzygy.obj M))
  comm₃ : E.p₂ ≫ c = a₂ ≫ cokernel.π
    (Injective.ι (Cosyzygy.obj (Cosyzygy.obj M)))

end Extension3

/-- The actual chosen short exact sequence defining cosyzygy. -/
abbrev chosenSequence (M : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)

omit [HasBinaryBiproducts C] in
theorem chosenSequence_shortExact (M : C) : (chosenSequence M).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by dsimp [chosenSequence, ShortComplex.cokernelSequence]; infer_instance
  epi_g := by dsimp [chosenSequence, ShortComplex.cokernelSequence]; infer_instance

theorem chosenSequence_connecting (M : C) :
    Q.map (FrobeniusTriangles.connecting (chosenSequence_shortExact M)) =
      𝟙 (Q.obj (Cosyzygy.obj M)) := by
  have hc : FrobeniusTriangles.connecting (chosenSequence_shortExact M) =
      Cosyzygy.map (𝟙 M) := by
    apply (cancel_epi (cokernel.π (Injective.ι M))).mp
    change (chosenSequence M).g ≫ FrobeniusTriangles.connecting
      (chosenSequence_shortExact M) = _
    rw [FrobeniusTriangles.g_connecting]
    simp [chosenSequence, FrobeniusTriangles.extension, Cosyzygy.π_map, Cosyzygy.extension]
  rw [hc]
  exact Cosyzygy.stable_map_id M

/-- Splicing the three actual chosen injective presentations. -/
def chosenExtension (M : C) :
    Extension3 M (Cosyzygy.obj (Cosyzygy.obj (Cosyzygy.obj M))) where
  Z₁ := Cosyzygy.obj M
  Z₂ := Cosyzygy.obj (Cosyzygy.obj M)
  I₀ := Injective.under M
  I₁ := Injective.under (Cosyzygy.obj M)
  I₂ := Injective.under (Cosyzygy.obj (Cosyzygy.obj M))
  i₀ := Injective.ι M
  p₀ := cokernel.π (Injective.ι M)
  i₁ := Injective.ι (Cosyzygy.obj M)
  p₁ := cokernel.π (Injective.ι (Cosyzygy.obj M))
  i₂ := Injective.ι (Cosyzygy.obj (Cosyzygy.obj M))
  p₂ := cokernel.π (Injective.ι (Cosyzygy.obj (Cosyzygy.obj M)))
  zero₀ := cokernel.condition _
  zero₁ := cokernel.condition _
  zero₂ := cokernel.condition _
  exact₀ := chosenSequence_shortExact M
  exact₁ := chosenSequence_shortExact (Cosyzygy.obj M)
  exact₂ := chosenSequence_shortExact (Cosyzygy.obj (Cosyzygy.obj M))
  injective₀ := inferInstance
  injective₁ := inferInstance
  injective₂ := inferInstance

theorem chosenExtension_stableComparison (M : C) :
    (chosenExtension M).stableComparison.hom =
      𝟙 (Q.obj (Cosyzygy.obj (Cosyzygy.obj (Cosyzygy.obj M)))) := by
  rw [Extension3.stableComparison_hom]
  change Q.map (FrobeniusTriangles.connecting
      (chosenSequence_shortExact (Cosyzygy.obj (Cosyzygy.obj M)))) ≫
    F.map (Q.map (FrobeniusTriangles.connecting
      (chosenSequence_shortExact (Cosyzygy.obj M)))) ≫
    F.map (F.map (Q.map (FrobeniusTriangles.connecting (chosenSequence_shortExact M)))) = _
  rw [chosenSequence_connecting, chosenSequence_connecting, chosenSequence_connecting]
  change 𝟙 ((cube F).obj (Q.obj M)) ≫ F.map (𝟙 (F.obj (F.obj (Q.obj M)))) ≫
    F.map (F.map (𝟙 (F.obj (Q.obj M)))) = 𝟙 ((cube F).obj (Q.obj M))
  simp only [cube, Functor.comp_obj, CategoryTheory.Functor.map_id,
    Category.comp_id]

namespace Extension3.Comparison

variable {M N : C} {E : Extension3 M N} (K : E.Comparison)

/-- The intermediate map forced by the first short exact row. -/
def c₁ : E.Z₁ ⟶ Cosyzygy.obj M :=
  FrobeniusTriangles.desc E.exact₀ (K.a₀ ≫ cokernel.π (Injective.ι M))
    (by rw [← Category.assoc, K.comm₀]; simp)

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem p₀_c₁ : E.p₀ ≫ K.c₁ = K.a₀ ≫ cokernel.π (Injective.ι M) :=
  FrobeniusTriangles.g_desc E.exact₀ _ _

omit [HasBinaryBiproducts C] in
theorem i₁_a₁ : E.i₁ ≫ K.a₁ = K.c₁ ≫ Injective.ι (Cosyzygy.obj M) := by
  apply (cancel_epi E.p₀).mp
  simpa only [Category.assoc, p₀_c₁_assoc] using K.comm₁

/-- The intermediate map forced by the second short exact row. -/
def c₂ : E.Z₂ ⟶ Cosyzygy.obj (Cosyzygy.obj M) :=
  FrobeniusTriangles.desc E.exact₁
    (K.a₁ ≫ cokernel.π (Injective.ι (Cosyzygy.obj M)))
    (by rw [← Category.assoc, K.i₁_a₁, Category.assoc]; simp)

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem p₁_c₂ : E.p₁ ≫ K.c₂ =
    K.a₁ ≫ cokernel.π (Injective.ι (Cosyzygy.obj M)) :=
  FrobeniusTriangles.g_desc E.exact₁ _ _

omit [HasBinaryBiproducts C] in
theorem i₂_a₂ : E.i₂ ≫ K.a₂ =
    K.c₂ ≫ Injective.ι (Cosyzygy.obj (Cosyzygy.obj M)) := by
  apply (cancel_epi E.p₁).mp
  simpa only [Category.assoc, p₁_c₂_assoc] using K.comm₂

/-- The boundary diagram induces a genuine map of the three short exact rows. -/
def hom : E.Hom (chosenExtension M) where
  f₀ := 𝟙 M
  f₁ := K.c₁
  f₂ := K.c₂
  f₃ := K.c
  a₀ := K.a₀
  a₁ := K.a₁
  a₂ := K.a₂
  comm_i₀ := by simpa only [chosenExtension, Category.id_comp] using K.comm₀
  comm_p₀ := K.p₀_c₁
  comm_i₁ := K.i₁_a₁
  comm_p₁ := K.p₁_c₂
  comm_i₂ := K.i₂_a₂
  comm_p₂ := K.comm₃

/-- All choices of ambient comparison have the same endpoint stable class,
equal to the actual canonical three-step comparison. -/
theorem stable_endpoint : Q.map K.c = E.stableComparison.hom := by
  have h := K.hom.stableComparison_naturality
  simpa only [hom, chosenExtension_stableComparison, Category.comp_id,
    Q.map_id, (cube F).map_id] using h

end Extension3.Comparison


namespace Extension3

variable {M N : C} (E : Extension3 M N)

/-- The first comparison row exists by injectivity and the cokernel property. -/
def canonicalRow₀ : E.row₀ ⟶ chosenSequence M :=
  FrobeniusTriangles.completeStrictSquare E.exact₀ (𝟙 M)
    (Injective.factorThru (Injective.ι M) E.i₀) (by
      simpa only [chosenSequence, ShortComplex.cokernelSequence, Category.id_comp] using
        Injective.comp_factorThru (Injective.ι M) E.i₀)

/-- The second comparison row extends the actual first cokernel map. -/
def canonicalRow₁ : E.row₁ ⟶ chosenSequence (Cosyzygy.obj M) :=
  FrobeniusTriangles.completeStrictSquare E.exact₁ E.canonicalRow₀.τ₃
    (Injective.factorThru
      (E.canonicalRow₀.τ₃ ≫ Injective.ι (Cosyzygy.obj M)) E.i₁)
    (by
      simpa only [chosenSequence, ShortComplex.cokernelSequence] using
        Injective.comp_factorThru
          (E.canonicalRow₀.τ₃ ≫ Injective.ι (Cosyzygy.obj M)) E.i₁)

/-- The third comparison row extends the second actual cokernel map. -/
def canonicalRow₂ : E.row₂ ⟶ chosenSequence (Cosyzygy.obj (Cosyzygy.obj M)) :=
  FrobeniusTriangles.completeStrictSquare E.exact₂ E.canonicalRow₁.τ₃
    (Injective.factorThru
      (E.canonicalRow₁.τ₃ ≫ Injective.ι (Cosyzygy.obj (Cosyzygy.obj M))) E.i₂)
    (by
      simpa only [chosenSequence, ShortComplex.cokernelSequence] using
        Injective.comp_factorThru
          (E.canonicalRow₁.τ₃ ≫ Injective.ι (Cosyzygy.obj (Cosyzygy.obj M))) E.i₂)

/-- A genuine ambient comparison diagram always exists; no endpoint equality
is added as an assumption. -/
def canonicalComparison : E.Comparison where
  a₀ := E.canonicalRow₀.τ₂
  a₁ := E.canonicalRow₁.τ₂
  a₂ := E.canonicalRow₂.τ₂
  c := E.canonicalRow₂.τ₃
  comm₀ := by
    simpa only [canonicalRow₀, FrobeniusTriangles.completeStrictSquare,
      chosenSequence, ShortComplex.cokernelSequence, Category.id_comp] using
      E.canonicalRow₀.comm₁₂.symm
  comm₁ := by
    change (E.p₀ ≫ E.i₁) ≫ E.canonicalRow₁.τ₂ = _
    rw [Category.assoc]
    erw [← E.canonicalRow₁.comm₁₂]
    change E.p₀ ≫ E.canonicalRow₀.τ₃ ≫ Injective.ι (Cosyzygy.obj M) = _
    erw [← Category.assoc, ← E.canonicalRow₀.comm₂₃]
    simp only [chosenSequence, Category.assoc]
  comm₂ := by
    change (E.p₁ ≫ E.i₂) ≫ E.canonicalRow₂.τ₂ = _
    rw [Category.assoc]
    erw [← E.canonicalRow₂.comm₁₂]
    change E.p₁ ≫ E.canonicalRow₁.τ₃ ≫ Injective.ι (Cosyzygy.obj (Cosyzygy.obj M)) = _
    erw [← Category.assoc, ← E.canonicalRow₁.comm₂₃]
    simp only [chosenSequence, Category.assoc]
  comm₃ := E.canonicalRow₂.comm₂₃.symm

theorem canonicalComparison_stable_endpoint :
    Q.map E.canonicalComparison.c = E.stableComparison.hom :=
  E.canonicalComparison.stable_endpoint

end Extension3

end PretriangulatedV2.StableCategory.InjectiveComparison
