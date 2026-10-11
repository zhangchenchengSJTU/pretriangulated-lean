import PretriangulatedV2.GoodFillIns

/-!
# The good-fill-in criterion implies the octahedral axiom

The converse is obtained by two good fill-ins and explicit elimination of
contractible summands.  Cancellation of a distinguished summand is proved
using TR1, TR3 and the five lemma, without an idempotent-completeness assumption.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open ZeroObject

namespace PretriangulatedV2

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
  [PreservesBinaryBiproducts (shiftFunctor C (1 : ℤ))]
  [CategoryTheory.Pretriangulated C]

namespace GoodFillInsConverse

open GoodFillIns

variable {T S T' S' : Triangle C}

def biprodTriangleInl (T S : Triangle C) : T ⟶ biprodTriangle T S where
  hom₁ := biprod.inl
  hom₂ := biprod.inl
  hom₃ := biprod.inl
  comm₁ := by dsimp [biprodTriangle]; simp
  comm₂ := by dsimp [biprodTriangle]; simp
  comm₃ := by dsimp [biprodTriangle]; simp

def biprodTriangleInr (T S : Triangle C) : S ⟶ biprodTriangle T S where
  hom₁ := biprod.inr
  hom₂ := biprod.inr
  hom₃ := biprod.inr
  comm₁ := by dsimp [biprodTriangle]; simp
  comm₂ := by dsimp [biprodTriangle]; simp
  comm₃ := by dsimp [biprodTriangle]; simp

def biprodTriangleMap (p : T ⟶ T') (q : S ⟶ S') :
    biprodTriangle T S ⟶ biprodTriangle T' S' :=
  biprodTriangleFst T S ≫ p ≫ biprodTriangleInl T' S' +
    biprodTriangleSnd T S ≫ q ≫ biprodTriangleInr T' S'

omit [HasZeroObject C] [CategoryTheory.Pretriangulated C] in
@[simp]
lemma biprodTriangleMap_hom₁ (p : T ⟶ T') (q : S ⟶ S') :
    (biprodTriangleMap p q).hom₁ = biprod.map p.hom₁ q.hom₁ := by
  dsimp [biprodTriangleMap, biprodTriangleFst, biprodTriangleSnd,
    biprodTriangleInl, biprodTriangleInr, biprodTriangle]
  ext <;> simp

omit [HasZeroObject C] [CategoryTheory.Pretriangulated C] in
@[simp]
lemma biprodTriangleMap_hom₂ (p : T ⟶ T') (q : S ⟶ S') :
    (biprodTriangleMap p q).hom₂ = biprod.map p.hom₂ q.hom₂ := by
  dsimp [biprodTriangleMap, biprodTriangleFst, biprodTriangleSnd,
    biprodTriangleInl, biprodTriangleInr, biprodTriangle]
  ext <;> simp

omit [HasZeroObject C] [CategoryTheory.Pretriangulated C] in
@[simp]
lemma biprodTriangleMap_hom₃ (p : T ⟶ T') (q : S ⟶ S') :
    (biprodTriangleMap p q).hom₃ = biprod.map p.hom₃ q.hom₃ := by
  dsimp [biprodTriangleMap, biprodTriangleFst, biprodTriangleSnd,
    biprodTriangleInl, biprodTriangleInr, biprodTriangle]
  ext <;> simp

/-- A summand of a distinguished binary sum is distinguished whenever the
other summand is.  The proof constructs a block-diagonal five-lemma comparison. -/
lemma distinguished_of_biprodTriangle_distinguished
    (h : biprodTriangle T S ∈ distTriang C) (hS : S ∈ distTriang C) :
    T ∈ distTriang C := by
  obtain ⟨Z, g, w, hD⟩ := distinguished_cocone_triangle T.mor₁
  let D := Triangle.mk T.mor₁ g w
  have hDS : biprodTriangle D S ∈ distTriang C := biprodTriangle_distinguished hD hS
  let φ := completeDistinguishedTriangleMorphism _ _ hDS h (𝟙 _) (𝟙 _)
    (by simp [biprodTriangle, D])
  let p : D ⟶ T := biprodTriangleInl D S ≫ φ ≫ biprodTriangleFst T S
  have hp₁ : p.hom₁ = 𝟙 _ := by
    dsimp [p, φ, biprodTriangleInl, biprodTriangleFst,
      completeDistinguishedTriangleMorphism, D]
    simp
  have hp₂ : p.hom₂ = 𝟙 _ := by
    dsimp [p, φ, biprodTriangleInl, biprodTriangleFst,
      completeDistinguishedTriangleMorphism, D]
    simp
  let ψ := biprodTriangleMap p (𝟙 S)
  have hψ₁ : ψ.hom₁ = 𝟙 _ := by
    simp only [ψ, biprodTriangleMap_hom₁, hp₁, id_hom₁]
    dsimp [biprodTriangle, D]
    ext <;> simp
  have hψ₂ : ψ.hom₂ = 𝟙 _ := by
    simp only [ψ, biprodTriangleMap_hom₂, hp₂, id_hom₂]
    dsimp [biprodTriangle, D]
    ext <;> simp
  have hψ₃ : IsIso ψ.hom₃ := isIso₃_of_isIso₁₂ ψ hDS h
    (by rw [hψ₁]; infer_instance) (by rw [hψ₂]; infer_instance)
  have hmap : IsIso (biprod.map p.hom₃ (𝟙 S.obj₃)) := by
    simpa [ψ] using hψ₃
  have hp₃ : IsIso p.hom₃ := isIso_left_of_isIso_biprod_map p.hom₃ (𝟙 S.obj₃)
  have : IsIso p := Triangle.isIso_of_isIsos p
    (by rw [hp₁]; infer_instance) (by rw [hp₂]; infer_instance) hp₃
  exact isomorphic_distinguished _ hD _ (asIso p).symm

/-- Elementary upper triangular change of biproduct coordinates. -/
def upperShear {X Y : C} (b : Y ⟶ X) : X ⊞ Y ≅ X ⊞ Y where
  hom := 𝟙 _ + biprod.snd ≫ b ≫ biprod.inl
  inv := 𝟙 _ - biprod.snd ≫ b ≫ biprod.inl
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

section IdentityFirst

variable {X Y Z Y' Z' : C}
  {f : X ⟶ Y} {p : Y ⟶ Z} {q : Z ⟶ X⟦(1 : ℤ)⟧}
  {f' : X ⟶ Y'} {p' : Y' ⟶ Z'} {q' : Z' ⟶ X⟦(1 : ℤ)⟧}

/-- The noncontractible part of the cone when the first component is identity. -/
def reducedCone (m : Triangle.mk f p q ⟶ Triangle.mk f' p' q') : Triangle C :=
  Triangle.mk (biprod.lift (-p) m.hom₂) (biprod.desc m.hom₃ p')
    (q' ≫ f⟦(1 : ℤ)⟧')

def identityFirstConeIso (m : Triangle.mk f p q ⟶ Triangle.mk f' p' q')
    (h₁ : m.hom₁ = 𝟙 X) (hT : Triangle.mk f p q ∈ distTriang C)
    (hT' : Triangle.mk f' p' q' ∈ distTriang C) :
    biprodTriangle (reducedCone m) (Triangle.mk (0 : X ⟶ 0) 0 (𝟙 (X⟦(1 : ℤ)⟧))) ≅
      truncatedCone m := by
  have hcomm₁ : f ≫ m.hom₂ = f' := by simpa [h₁] using m.comm₁
  have hcomm₃ : m.hom₃ ≫ q' = q := by simpa [h₁] using m.comm₃.symm
  have hzero : f ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hzero' : p' ≫ q' = 0 := comp_distTriang_mor_zero₂₃ _ hT'
  refine Triangle.isoMk _ _ (upperShear (-f))
    (isoBiprodZero (isZero_zero C)).symm
    (lowerShear (-q') ≪≫ biprod.braiding _ _) ?_ ?_ ?_
  · dsimp [biprodTriangle, reducedCone, truncatedCone, truncatedConeMor₁, upperShear]
    ext <;> simp [hzero, hcomm₁]
  · dsimp [biprodTriangle, reducedCone, truncatedCone, truncatedConeMor₂, lowerShear]
    ext <;> simp [hcomm₃, hzero']
  · dsimp [biprodTriangle, reducedCone, truncatedCone, truncatedConeMor₃,
      truncatedConeMor₃Matrix, lowerShear, upperShear]
    apply (cancel_mono ((shiftFunctor C (1 : ℤ)).mapBiprod Y X).hom).mp
    simp only [Category.assoc]
    ext
    all_goals simp [h₁, Functor.map_add, Functor.map_neg, Functor.map_comp]
    all_goals simp [← Functor.map_comp]

/-- Contractible-block elimination for a good fill-in whose first component
is identity. -/
lemma reducedCone_distinguished (m : Triangle.mk f p q ⟶ Triangle.mk f' p' q')
    (h₁ : m.hom₁ = 𝟙 X) (hT : Triangle.mk f p q ∈ distTriang C)
    (hT' : Triangle.mk f' p' q' ∈ distTriang C)
    (hcone : truncatedCone m ∈ distTriang C) : reducedCone m ∈ distTriang C := by
  apply distinguished_of_biprodTriangle_distinguished
    (isomorphic_distinguished _ hcone _ (identityFirstConeIso m h₁ hT hT'))
    (contractible_distinguished₂ X)

end IdentityFirst

section UpperBlock

variable {A B D E : C} (c : A ⟶ B) (h : D ⟶ B)
  (m : B ⟶ E) (g : D ⟶ E) (l : E ⟶ A⟦(1 : ℤ)⟧)

def upperBlockTriangle : Triangle C :=
  Triangle.mk
    (biprod.fst ≫ c ≫ biprod.inl + biprod.snd ≫ h ≫ biprod.inl +
      biprod.snd ≫ biprod.inr)
    (biprod.desc m g) (l ≫ (biprod.inl : A ⟶ A ⊞ D)⟦(1 : ℤ)⟧')

def upperBlockTriangleIso (hc : h ≫ m + g = 0) :
    biprodTriangle (Triangle.mk c m l) (contractibleTriangle D) ≅
      upperBlockTriangle c h m g l := by
  refine Triangle.isoMk _ _ (Iso.refl _) (upperShear h)
    (isoBiprodZero (isZero_zero C)).symm ?_ ?_ ?_
  · dsimp [biprodTriangle, contractibleTriangle, upperBlockTriangle, upperShear]
    ext <;> simp
  · dsimp [biprodTriangle, contractibleTriangle, upperBlockTriangle, upperShear]
    ext <;> simp
    simpa only [add_comm] using hc.symm
  · dsimp [biprodTriangle, contractibleTriangle, upperBlockTriangle]
    ext; simp

lemma distinguished_of_upperBlockTriangle_distinguished (hc : h ≫ m + g = 0)
    (hblock : upperBlockTriangle c h m g l ∈ distTriang C) :
    Triangle.mk c m l ∈ distTriang C :=
  distinguished_of_biprodTriangle_distinguished
    (isomorphic_distinguished _ hblock _ (upperBlockTriangleIso c h m g l hc))
    (contractible_distinguished D)

end UpperBlock

section Octahedron

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧}
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧}
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧}

/-- Two good fill-ins construct every field of a genuine octahedron. -/
lemma nonempty_octahedron (hgood : HasGoodFillIns C) (comm : u₁₂ ≫ u₂₃ = u₁₃)
    (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
    (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
    (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C) :
    Nonempty (Triangulated.Octahedron comm h₁₂ h₂₃ h₁₃) := by
  let m₀ := completeDistinguishedTriangleMorphism _ _ h₁₂ h₁₃ (𝟙 X₁) u₂₃
    (by simpa using comm)
  obtain ⟨m, hm₁, hm₂, hcone⟩ := hgood h₁₂ h₁₃ m₀
  have hm₁' : m.hom₁ = 𝟙 X₁ := by simpa [m₀] using hm₁
  have hm₂' : m.hom₂ = u₂₃ := by simpa [m₀] using hm₂
  let R := Triangle.mk (biprod.lift (-v₁₂) u₂₃) (biprod.desc m.hom₃ v₁₃)
    (w₁₃ ≫ u₁₂⟦(1 : ℤ)⟧')
  have hR : R ∈ distTriang C := by
    simpa [R, reducedCone, hm₂'] using reducedCone_distinguished m hm₁' h₁₂ h₁₃ hcone
  let n₀ := completeDistinguishedTriangleMorphism R _ hR h₂₃ (𝟙 X₂)
    (biprod.snd : Z₁₂ ⊞ X₃ ⟶ X₃) (by simp [R])
  obtain ⟨n, hn₁, hn₂, hconen⟩ := hgood hR h₂₃ n₀
  have hn₁' : n.hom₁ = 𝟙 X₂ := by simpa [n₀] using hn₁
  have hn₂' : n.hom₂ = biprod.snd := by simpa [n₀] using hn₂
  have hncomm₂ : v₁₃ ≫ n.hom₃ = v₂₃ := by
    have h := congrArg (fun f => (biprod.inr : X₃ ⟶ Z₁₂ ⊞ X₃) ≫ f) n.comm₂
    simpa [R, hn₂'] using h
  have hncomm₃ : w₁₃ ≫ u₁₂⟦(1 : ℤ)⟧' = n.hom₃ ≫ w₂₃ := by
    simpa [R, hn₁'] using n.comm₃
  let c : Z₁₂ ⟶ Z₁₃ := m.hom₃
  let d : Z₁₃ ⟶ Z₂₃ := n.hom₃
  have hfirst : biprod.lift (-(biprod.desc c v₁₃))
      (biprod.snd : Z₁₂ ⊞ X₃ ⟶ X₃) =
        biprod.fst ≫ (-c) ≫ biprod.inl +
          biprod.snd ≫ (-v₁₃) ≫ biprod.inl + biprod.snd ≫ biprod.inr := by
    ext <;> simp
  have hz : w₂₃ ≫ u₂₃⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ h₂₃
  have hlast : w₂₃ ≫ (biprod.lift (-v₁₂) u₂₃)⟦(1 : ℤ)⟧' =
      (-(w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧')) ≫
        (biprod.inl : Z₁₂ ⟶ Z₁₂ ⊞ X₃)⟦(1 : ℤ)⟧' := by
    simp [biprod.lift_eq, Functor.map_add, Functor.map_comp, reassoc_of% hz]
  have hblock : upperBlockTriangle (-c) (-v₁₃) d v₂₃
      (-(w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧')) ∈ distTriang C := by
    have h := reducedCone_distinguished n hn₁' hR h₂₃ hconen
    change Triangle.mk (biprod.lift (-(biprod.desc c v₁₃)) n.hom₂)
      (biprod.desc d v₂₃) (w₂₃ ≫ (biprod.lift (-v₁₂) u₂₃)⟦(1 : ℤ)⟧') ∈ distTriang C at h
    rw [hn₂'] at h
    change Triangle.mk
      (biprod.lift (-(biprod.desc c v₁₃)) (biprod.snd : Z₁₂ ⊞ X₃ ⟶ X₃))
      (biprod.desc d v₂₃) (w₂₃ ≫ (biprod.lift (-v₁₂) u₂₃)⟦(1 : ℤ)⟧') ∈ distTriang C at h
    rw [hfirst, hlast] at h
    exact h
  have hneg : Triangle.mk (-c) d (-(w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧'))
      ∈ distTriang C :=
    distinguished_of_upperBlockTriangle_distinguished _ _ _ _ _
      (by simp [d, hncomm₂]) hblock
  have ho : Triangle.mk c d (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ∈ distTriang C := by
    refine isomorphic_distinguished _ hneg _ (Iso.symm ?_)
    exact Triangle.isoMk _ _ (negIso Z₁₂) (Iso.refl _) (Iso.refl _)
      (by simp [negIso]) (by simp) (by simp [negIso])
  refine ⟨{ m₁ := m.hom₃
            m₃ := n.hom₃
            comm₁ := ?_
            comm₂ := ?_
            comm₃ := hncomm₂
            comm₄ := hncomm₃
            mem := ho }⟩
  · simpa [hm₂'] using m.comm₂
  · simpa [hm₁'] using m.comm₃.symm

end Octahedron

end GoodFillInsConverse

/-- The reverse implication in Theorem 2.1, with every octahedral field
constructed from good fill-ins. -/
theorem isTriangulated_of_hasGoodFillIns (hgood : HasGoodFillIns C) :
    IsTriangulated C where
  octahedron_axiom := by
    intro X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
    exact GoodFillInsConverse.nonempty_octahedron hgood comm h₁₂ h₂₃ h₁₃

/-- The good-fill-in criterion of Theorem 2.1. -/
theorem isTriangulated_iff_hasGoodFillIns : IsTriangulated C ↔ HasGoodFillIns C := by
  constructor
  · intro h
    exact @hasGoodFillIns_of_isTriangulated C _ _ _ _ _ _ _ _ h
  · exact isTriangulated_of_hasGoodFillIns

end PretriangulatedV2
