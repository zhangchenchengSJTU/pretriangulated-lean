import PretriangulatedV2.TruncatedCone
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Good fill-ins from the octahedral axiom

The construction factors the first truncated-cone matrix through `Y ⊞ Y'`.
Its two factors have cones `Z'` and `Σ X`.  The octahedral connecting map
vanishes, and a suitable choice of splitting recovers the prescribed shift of
the first component of the square.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive

namespace PretriangulatedV2

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
  [PreservesBinaryBiproducts (shiftFunctor C (1 : ℤ))]
  [CategoryTheory.Pretriangulated C]

namespace GoodFillIns

variable {T T' : Triangle C}

/-- The objectwise binary biproduct of two triangles, with the canonical
comparison for the shift. -/
def biprodTriangle (T T' : Triangle C) : Triangle C :=
  Triangle.mk (biprod.map T.mor₁ T'.mor₁) (biprod.map T.mor₂ T'.mor₂)
    (biprod.map T.mor₃ T'.mor₃ ≫
      ((shiftFunctor C (1 : ℤ)).mapBiprod T.obj₁ T'.obj₁).inv)

def biprodTriangleFst (T T' : Triangle C) : biprodTriangle T T' ⟶ T where
  hom₁ := biprod.fst
  hom₂ := biprod.fst
  hom₃ := biprod.fst
  comm₁ := by dsimp [biprodTriangle]; ext <;> simp
  comm₂ := by dsimp [biprodTriangle]; ext <;> simp
  comm₃ := by
    dsimp [biprodTriangle]
    ext <;> simp [← Functor.map_comp]

def biprodTriangleSnd (T T' : Triangle C) : biprodTriangle T T' ⟶ T' where
  hom₁ := biprod.snd
  hom₂ := biprod.snd
  hom₃ := biprod.snd
  comm₁ := by dsimp [biprodTriangle]; ext <;> simp
  comm₂ := by dsimp [biprodTriangle]; ext <;> simp
  comm₃ := by
    dsimp [biprodTriangle]
    ext <;> simp [← Functor.map_comp]

/-- Canonical comparison from a binary biproduct to a product indexed by Bool. -/
def biprodIsoBoolProduct (F : Bool → C) : F false ⊞ F true ≅ ∏ᶜ F where
  hom := Pi.lift (fun b => match b with | false => biprod.fst | true => biprod.snd)
  inv := biprod.lift (Pi.π F false) (Pi.π F true)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext b; cases b <;> simp

lemma biprodTriangle_distinguished (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) : biprodTriangle T T' ∈ distTriang C := by
  let ts : Bool → Triangle C := fun b => cond b T' T
  let φ : ∀ b, biprodTriangle T T' ⟶ ts b :=
    fun b => match b with | false => biprodTriangleFst T T' | true => biprodTriangleSnd T T'
  let f := productTriangle.lift ts φ
  have hf₁ : f.hom₁ = (biprodIsoBoolProduct (fun b => (ts b).obj₁)).hom := by
    dsimp [f, productTriangle.lift, biprodIsoBoolProduct]
    apply Pi.hom_ext
    intro b
    cases b <;> simp [φ, ts, biprodTriangleFst, biprodTriangleSnd]
  have hf₂ : f.hom₂ = (biprodIsoBoolProduct (fun b => (ts b).obj₂)).hom := by
    dsimp [f, productTriangle.lift, biprodIsoBoolProduct]
    apply Pi.hom_ext
    intro b
    cases b <;> simp [φ, ts, biprodTriangleFst, biprodTriangleSnd]
  have hf₃ : f.hom₃ = (biprodIsoBoolProduct (fun b => (ts b).obj₃)).hom := by
    dsimp [f, productTriangle.lift, biprodIsoBoolProduct]
    apply Pi.hom_ext
    intro b
    cases b <;> simp [φ, ts, biprodTriangleFst, biprodTriangleSnd]
  have : IsIso f.hom₁ := by rw [hf₁]; infer_instance
  have : IsIso f.hom₂ := by rw [hf₂]; infer_instance
  have : IsIso f.hom₃ := by rw [hf₃]; infer_instance
  have : IsIso f := Triangle.isIso_of_isIsos f inferInstance inferInstance inferInstance
  exact isomorphic_distinguished _
    (productTriangle_distinguished ts (by intro b; cases b; exact hT; exact hT')) _ (asIso f)

/-- Elementary lower triangular change of biproduct coordinates. -/
def lowerShear {X Y : C} (b : X ⟶ Y) : X ⊞ Y ≅ X ⊞ Y where
  hom := 𝟙 _ + biprod.fst ≫ b ≫ biprod.inr
  inv := 𝟙 _ - biprod.fst ≫ b ≫ biprod.inr
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/-- First factor of the truncated-cone first matrix. -/
def factor₁ (m : T ⟶ T') : T.obj₂ ⊞ T'.obj₁ ⟶ T.obj₂ ⊞ T'.obj₂ :=
  biprod.lift biprod.fst (biprod.fst ≫ m.hom₂ + biprod.snd ≫ T'.mor₁)

/-- Second factor of the truncated-cone first matrix. -/
def factor₂ (T T' : Triangle C) : T.obj₂ ⊞ T'.obj₂ ⟶ T.obj₃ ⊞ T'.obj₂ :=
  biprod.map (-T.mor₂) (𝟙 _)

omit [HasZeroObject C] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
  [PreservesBinaryBiproducts (shiftFunctor C (1 : ℤ))] [CategoryTheory.Pretriangulated C] in
/-- The factorization is an equality of the actual first matrices. -/
lemma factor₁_comp_factor₂ (m : T ⟶ T') :
    factor₁ m ≫ factor₂ T T' = truncatedConeMor₁ m := by
  ext <;> simp [factor₁, factor₂, truncatedConeMor₁]

/-- The triangle completing the first factor; it is a shear of `T'`
with a contractible summand. -/
def factorTriangle₁ (m : T ⟶ T') : Triangle C :=
  Triangle.mk (factor₁ m)
    (biprod.desc (-(m.hom₂ ≫ T'.mor₂)) T'.mor₂)
    (T'.mor₃ ≫ (biprod.inr : T'.obj₁ ⟶ T.obj₂ ⊞ T'.obj₁)⟦(1 : ℤ)⟧')

/-- The triangle completing the second factor; it is a signed rotation
of `T` with a contractible summand. -/
def factorTriangle₂ (T T' : Triangle C) : Triangle C :=
  Triangle.mk (factor₂ T T') (biprod.desc (-T.mor₃) 0)
    (-(T.mor₁⟦(1 : ℤ)⟧') ≫
      (biprod.inl : T.obj₂ ⟶ T.obj₂ ⊞ T'.obj₂)⟦(1 : ℤ)⟧')

def factorTriangle₁Iso (m : T ⟶ T') :
    biprodTriangle (contractibleTriangle T.obj₂) T' ≅ factorTriangle₁ m := by
  refine Triangle.isoMk _ _ (Iso.refl _) (lowerShear m.hom₂)
    (isoZeroBiprod (isZero_zero C)).symm ?_ ?_ ?_
  · dsimp [biprodTriangle, contractibleTriangle, factorTriangle₁, factor₁, lowerShear]
    ext <;> simp
  · dsimp [biprodTriangle, contractibleTriangle, factorTriangle₁, lowerShear]
    ext <;> simp
  · dsimp [biprodTriangle, contractibleTriangle, factorTriangle₁]
    ext; simp

lemma factorTriangle₁_distinguished (m : T ⟶ T') (hT' : T' ∈ distTriang C) :
    factorTriangle₁ m ∈ distTriang C :=
  isomorphic_distinguished _
    (biprodTriangle_distinguished (contractible_distinguished T.obj₂) hT') _
    (factorTriangle₁Iso m).symm

/-- Multiplication by minus one, as an isomorphism in an additive category. -/
def negIso (X : C) : X ≅ X where
  hom := -𝟙 X
  inv := -𝟙 X
  hom_inv_id := by simp
  inv_hom_id := by simp

def factorTriangle₂Iso (T T' : Triangle C) :
    biprodTriangle T.rotate (contractibleTriangle T'.obj₂) ≅ factorTriangle₂ T T' := by
  refine Triangle.isoMk _ _ (biprod.mapIso (negIso T.obj₂) (Iso.refl _))
    (Iso.refl _) ((isoBiprodZero (isZero_zero C)).symm ≪≫ negIso _) ?_ ?_ ?_
  · dsimp [biprodTriangle, contractibleTriangle, factorTriangle₂, factor₂, negIso]
    ext <;> simp
  · dsimp [biprodTriangle, contractibleTriangle, factorTriangle₂, negIso]
    ext <;> simp
  · dsimp [biprodTriangle, contractibleTriangle, factorTriangle₂, negIso]
    ext; simp [← Functor.map_comp]

lemma factorTriangle₂_distinguished (hT : T ∈ distTriang C) (T' : Triangle C) :
    factorTriangle₂ T T' ∈ distTriang C :=
  isomorphic_distinguished _
    (biprodTriangle_distinguished (rot_of_distTriang _ hT)
      (contractible_distinguished T'.obj₂)) _ (factorTriangle₂Iso T T').symm

omit [PreservesBinaryBiproducts (shiftFunctor C (1 : ℤ))] in
/-- The connecting arrow of the octahedron for the two factors is zero.
This uses the given commutative square and exactness of `T'`. -/
lemma factor_connecting_zero (m : T ⟶ T') (hT' : T' ∈ distTriang C) :
    (factorTriangle₂ T T').mor₃ ≫
      ((factorTriangle₁ m).mor₂)⟦(1 : ℤ)⟧' = 0 := by
  change (-(T.mor₁⟦(1 : ℤ)⟧') ≫
    (biprod.inl : T.obj₂ ⟶ T.obj₂ ⊞ T'.obj₂)⟦(1 : ℤ)⟧') ≫
    (biprod.desc (-(m.hom₂ ≫ T'.mor₂)) T'.mor₂)⟦(1 : ℤ)⟧' = 0
  simp only [neg_comp, Category.assoc, ← Functor.map_comp, biprod.inl_desc]
  rw [comp_neg, ← Category.assoc, m.comm₁, Category.assoc,
    comp_distTriang_mor_zero₁₂ T' hT', comp_zero]
  simp

variable [IsTriangulated C]

/-- TR4 splits the cone of the first truncated-cone matrix, with the two
octahedral maps as the prescribed inclusion and projection. -/
lemma exists_split_cone (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    ∃ (V : C) (v : T.obj₃ ⊞ T'.obj₂ ⟶ V)
      (w : V ⟶ (T.obj₂ ⊞ T'.obj₁)⟦(1 : ℤ)⟧)
      (e : V ≅ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃),
      Triangle.mk (truncatedConeMor₁ m) v w ∈ distTriang C ∧
      v ≫ e.hom ≫ biprod.fst = biprod.desc (-T.mor₃) 0 ∧
      (biprod.inr : T'.obj₂ ⟶ T.obj₃ ⊞ T'.obj₂) ≫ v ≫ e.hom =
        T'.mor₂ ≫ biprod.inr ∧
      e.inv ≫ w ≫ (factor₁ m)⟦(1 : ℤ)⟧' =
        biprod.fst ≫ (factorTriangle₂ T T').mor₃ ∧
      (biprod.inr : T'.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃) ≫ e.inv ≫ w =
        (factorTriangle₁ m).mor₃ := by
  obtain ⟨V, v, w, hV⟩ := distinguished_cocone_triangle (truncatedConeMor₁ m)
  have hA : Triangle.mk (factor₁ m)
      (biprod.desc (-(m.hom₂ ≫ T'.mor₂)) T'.mor₂)
      (T'.mor₃ ≫ (biprod.inr : T'.obj₁ ⟶ T.obj₂ ⊞ T'.obj₁)⟦(1 : ℤ)⟧')
        ∈ distTriang C := factorTriangle₁_distinguished m hT'
  have hB : Triangle.mk (factor₂ T T') (biprod.desc (-T.mor₃) 0)
      (-(T.mor₁⟦(1 : ℤ)⟧') ≫
        (biprod.inl : T.obj₂ ⟶ T.obj₂ ⊞ T'.obj₂)⟦(1 : ℤ)⟧')
          ∈ distTriang C := factorTriangle₂_distinguished hT T'
  let o := Triangulated.someOctahedron (factor₁_comp_factor₂ m)
    hA hB hV
  have hz : o.triangle.mor₃ = 0 := factor_connecting_zero m hT'
  have hs : ∃ (e : V ≅ T'.obj₃ ⊞ T.obj₁⟦(1 : ℤ)⟧),
      o.m₁ ≫ e.hom = biprod.inl ∧ o.m₃ = e.hom ≫ biprod.snd :=
    exists_iso_binaryBiproduct_of_distTriang o.triangle o.mem hz
  obtain ⟨e, he₁, he₂⟩ := hs
  let e' : V ≅ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃ := e ≪≫ biprod.braiding _ _
  have hp : e'.inv ≫ o.m₃ = biprod.fst := by
    dsimp only [e', Iso.trans_inv]
    rw [he₂]
    simp
  have hi : (biprod.inr : T'.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃) ≫ e'.inv = o.m₁ := by
    apply (cancel_mono e.hom).mp
    dsimp only [e', Iso.trans_inv]
    simp only [Category.assoc, Iso.inv_hom_id, comp_id]
    rw [he₁]
    ext <;> simp
  refine ⟨V, v, w, e', hV, ?_, ?_, ?_, ?_⟩
  · calc
      v ≫ e'.hom ≫ biprod.fst = v ≫ e'.hom ≫ e'.inv ≫ o.m₃ := by rw [hp]
      _ = v ≫ o.m₃ := by simp
      _ = biprod.desc (-T.mor₃) 0 := o.comm₃
  · have h : T'.mor₂ ≫ o.m₁ = (biprod.inr : T'.obj₂ ⟶ T.obj₃ ⊞ T'.obj₂) ≫ v := by
      have h := congrArg (fun f => (biprod.inr : T'.obj₂ ⟶ T.obj₂ ⊞ T'.obj₂) ≫ f)
        o.comm₁
      simpa [factorTriangle₁, factor₂] using h
    rw [← Category.assoc, ← h]
    dsimp only [e', Iso.trans_hom]
    simp only [Category.assoc, reassoc_of% he₁]
    ext <;> simp
  · rw [o.comm₄, ← Category.assoc, hp]
    rfl
  · rw [← Category.assoc, hi]
    exact o.comm₂

/-- A choice of splitting of the octahedral extension can be corrected by
exactness so that its last matrix has exactly the prescribed shifted square. -/
lemma exists_normalized_split_cone (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    ∃ (V : C) (v : T.obj₃ ⊞ T'.obj₂ ⟶ V)
      (w : V ⟶ (T.obj₂ ⊞ T'.obj₁)⟦(1 : ℤ)⟧)
      (e : V ≅ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃),
      Triangle.mk (truncatedConeMor₁ m) v w ∈ distTriang C ∧
      v ≫ e.hom ≫ biprod.fst = biprod.desc (-T.mor₃) 0 ∧
      (biprod.inr : T'.obj₂ ⟶ T.obj₃ ⊞ T'.obj₂) ≫ v ≫ e.hom =
        T'.mor₂ ≫ biprod.inr ∧
      e.inv ≫ w = truncatedConeMor₃ m := by
  obtain ⟨V, v, w, e, hV, hvfst, hvinr, hwA, hwinr⟩ := exists_split_cone m hT hT'
  have hwfst : e.inv ≫ w ≫
      (biprod.fst : T.obj₂ ⊞ T'.obj₁ ⟶ T.obj₂)⟦(1 : ℤ)⟧' =
        biprod.fst ≫ (-(T.mor₁⟦(1 : ℤ)⟧')) := by
    have h := congrArg (fun f => f ≫
      (biprod.fst : T.obj₂ ⊞ T'.obj₂ ⟶ T.obj₂)⟦(1 : ℤ)⟧') hwA
    simpa [factor₁, factorTriangle₂, ← Functor.map_comp] using h
  let q := (biprod.inl : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃) ≫
    e.inv ≫ w ≫ (biprod.snd : T.obj₂ ⊞ T'.obj₁ ⟶ T'.obj₁)⟦(1 : ℤ)⟧'
  have hq : (q - m.hom₁⟦(1 : ℤ)⟧') ≫ T'.mor₁⟦(1 : ℤ)⟧' = 0 := by
    have hwA' : e.inv ≫ w ≫ (factor₁ m)⟦(1 : ℤ)⟧' =
        biprod.fst ≫ (-(T.mor₁⟦(1 : ℤ)⟧') ≫
          (biprod.inl : T.obj₂ ⟶ T.obj₂ ⊞ T'.obj₂)⟦(1 : ℤ)⟧') := hwA
    have hfactor : factor₁ m ≫ (biprod.snd : T.obj₂ ⊞ T'.obj₂ ⟶ T'.obj₂) =
        biprod.fst ≫ m.hom₂ + biprod.snd ≫ T'.mor₁ := by simp [factor₁]
    have h := congrArg (fun f =>
      (biprod.inl : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃) ≫ f ≫
        (biprod.snd : T.obj₂ ⊞ T'.obj₂ ⟶ T'.obj₂)⟦(1 : ℤ)⟧') hwA'
    simp only [Category.assoc, ← Functor.map_comp, hfactor] at h
    simp only [Functor.map_add, Functor.map_comp, comp_add, Category.assoc,
      reassoc_of% hwfst, biprod.inl_fst_assoc, neg_comp] at h
    simp only [← Functor.map_comp, biprod.inl_snd, Functor.map_zero, comp_zero] at h
    dsimp only [q]
    rw [sub_comp, ← Functor.map_comp, ← m.comm₁]
    simpa only [Category.assoc, sub_eq_add_neg, add_comm, Functor.map_comp, neg_zero] using h
  obtain ⟨k, hk⟩ := T'.coyoneda_exact₁ hT' (q - m.hom₁⟦(1 : ℤ)⟧') hq
  have hwinr' : (biprod.inr : T'.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃) ≫ e.inv ≫ w =
      T'.mor₃ ≫ (biprod.inr : T'.obj₁ ⟶ T.obj₂ ⊞ T'.obj₁)⟦(1 : ℤ)⟧' := hwinr
  have hwinrSnd : (biprod.inr : T'.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃) ≫
      e.inv ≫ w ≫ (biprod.snd : T.obj₂ ⊞ T'.obj₁ ⟶ T'.obj₁)⟦(1 : ℤ)⟧' = T'.mor₃ := by
    have h := congrArg (fun f =>
      f ≫ (biprod.snd : T.obj₂ ⊞ T'.obj₁ ⟶ T'.obj₁)⟦(1 : ℤ)⟧') hwinr'
    simp only [Category.assoc, ← Functor.map_comp, biprod.inr_snd] at h
    simpa using h
  have hq' : (biprod.inl : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃) ≫
      e.inv ≫ w ≫ (biprod.snd : T.obj₂ ⊞ T'.obj₁ ⟶ T'.obj₁)⟦(1 : ℤ)⟧' -
        k ≫ T'.mor₃ = m.hom₁⟦(1 : ℤ)⟧' := by
    change q - k ≫ T'.mor₃ = _
    rw [← hk]
    abel
  let e' := e ≪≫ lowerShear k
  refine ⟨V, v, w, e', hV, ?_, ?_, ?_⟩
  · dsimp only [e', Iso.trans_hom, lowerShear]
    simpa using hvfst
  · dsimp only [e', Iso.trans_hom, lowerShear]
    simp only [reassoc_of% hvinr]
    ext <;> simp
  · apply (cancel_mono ((shiftFunctor C (1 : ℤ)).mapBiprod T.obj₂ T'.obj₁).hom).mp
    simp only [truncatedConeMor₃, Category.assoc, Iso.inv_hom_id, comp_id]
    dsimp only [e', Iso.trans_inv, lowerShear]
    rw [Functor.mapBiprod_hom]
    ext
    all_goals simp [truncatedConeMor₃Matrix, hwfst, hwinrSnd, hq']

/-- The octahedral construction provides a good replacement of the third
component of any morphism of distinguished triangles. -/
lemma exists_good_fill_in (m : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    ∃ m' : T ⟶ T', m'.hom₁ = m.hom₁ ∧ m'.hom₂ = m.hom₂ ∧
      truncatedCone m' ∈ distTriang C := by
  obtain ⟨V, v, w, e, hV, hvfst, hvinr, hw⟩ := exists_normalized_split_cone m hT hT'
  let c := (biprod.inl : T.obj₃ ⟶ T.obj₃ ⊞ T'.obj₂) ≫ v ≫ e.hom ≫ biprod.snd
  have hv : v ≫ e.hom =
      biprod.fst ≫ (-T.mor₃) ≫ biprod.inl +
        biprod.fst ≫ c ≫ biprod.inr + biprod.snd ≫ T'.mor₂ ≫ biprod.inr := by
    ext
    all_goals simp [c, hvfst, hvinr]
  have hc₂ : T.mor₂ ≫ c = m.hom₂ ≫ T'.mor₂ := by
    have hz : truncatedConeMor₁ m ≫ (v ≫ e.hom) = 0 := by
      have h : truncatedConeMor₁ m ≫ v = 0 := comp_distTriang_mor_zero₁₂ _ hV
      rw [← Category.assoc, h, zero_comp]
    have h := congrArg (fun f =>
      (biprod.inl : T.obj₂ ⟶ T.obj₂ ⊞ T'.obj₁) ≫ f ≫
        (biprod.snd : T.obj₁⟦(1 : ℤ)⟧ ⊞ T'.obj₃ ⟶ T'.obj₃)) hz
    rw [hv] at h
    simp [truncatedConeMor₁] at h
    exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg, add_comm] using h)).symm
  have hc₃ : T.mor₃ ≫ m.hom₁⟦(1 : ℤ)⟧' = c ≫ T'.mor₃ := by
    have hz : (v ≫ e.hom) ≫ truncatedConeMor₃ m = 0 := by
      rw [← hw]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact comp_distTriang_mor_zero₂₃ _ hV
    have h := congrArg (fun f =>
      (biprod.inl : T.obj₃ ⟶ T.obj₃ ⊞ T'.obj₂) ≫ f ≫
        ((shiftFunctor C (1 : ℤ)).mapBiprod T.obj₂ T'.obj₁).hom ≫ biprod.snd) hz
    rw [hv] at h
    simp [truncatedConeMor₃, truncatedConeMor₃Matrix, ← Functor.map_comp] at h
    exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg, add_comm] using h)).symm
  let m' : T ⟶ T' :=
    { hom₁ := m.hom₁
      hom₂ := m.hom₂
      hom₃ := c
      comm₁ := m.comm₁
      comm₂ := hc₂
      comm₃ := hc₃ }
  refine ⟨m', rfl, rfl, isomorphic_distinguished _ hV _ ?_⟩
  refine (Triangle.isoMk (Triangle.mk (truncatedConeMor₁ m) v w) (truncatedCone m')
    (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_).symm
  · simp [truncatedCone, truncatedConeMor₁, m']
  · simpa [truncatedCone, truncatedConeMor₂, m'] using hv
  · change w ≫ (𝟙 (T.obj₂ ⊞ T'.obj₁))⟦(1 : ℤ)⟧' = e.hom ≫ truncatedConeMor₃ m
    have h := congrArg (fun f => e.hom ≫ f) hw
    simpa using h

end GoodFillIns

/-- The forward implication of the good-fill-in criterion (Theorem 2.1).
It is proved from the actual octahedral axiom of mathlib. -/
theorem hasGoodFillIns_of_isTriangulated [IsTriangulated C] : HasGoodFillIns C := by
  intro T T' hT hT' m
  exact GoodFillIns.exists_good_fill_in m hT hT'

end PretriangulatedV2
