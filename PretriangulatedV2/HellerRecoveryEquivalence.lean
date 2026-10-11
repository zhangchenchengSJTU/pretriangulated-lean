import PretriangulatedV2.HellerRecovery

/-!
# Recovery of the original distinguished class

The original pretriangulation and the reconstructed Heller pretriangulation
have the same distinguished triangles. This supplies the actual baseline TR4
needed after transporting the original category through additive Yoneda.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace PretriangulatedV2.HellerRecoveryEquivalence

open HellerClassification HellerRecovery
open StableCategory StableCategory.InjectiveComparison

universe v u

/-- A pretriangulation is determined by its distinguished class, since all
remaining structure fields are propositions. -/
theorem pretriangulated_ext
    {P : Type u} [Category.{v} P] [Preadditive P] [HasZeroObject P] [HasShift P ℤ]
    [∀ n : ℤ, (shiftFunctor P n).Additive]
    (p q : Pretriangulated P)
    (h : p.distinguishedTriangles = q.distinguishedTriangles) : p = q := by
  cases p
  cases q
  dsimp at h
  cases h
  rfl

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]
  [FrobeniusAbelian C]
  [HasShift (Projectives (C := C)) ℤ]
  [∀ n : ℤ, (shiftFunctor (Projectives (C := C)) n).Additive]
  [Pretriangulated (Projectives (C := C))]

variable (S : C ≌ C) [S.functor.Additive]
  (e : shiftFunctor (Projectives (C := C)) (1 : ℤ) ≅
    (projectiveEquivalence S).functor)

/-- Every triangle distinguished for the original pretriangulation is
δ-exact for a recovered parameter with the recovered δ. -/
theorem original_mem_recovered
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)
    (hp : p.delta = recoveredDelta S e)
    (T : Triangle (Projectives (C := C)))
    (hT : T ∈ (Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C))))) :
    T ∈ HellerClassification.distinguishedTriangles S p e := by
  have hp' : p = recoveredParameter S e := by
    cases p
    simpa only [recoveredParameter, HellerParameter.mk.injEq] using hp
  subst p
  exact original_distinguished_deltaExact S e T hT

/-- The recovered δ-exact distinguished class is contained in the original
one. The third vertex map is invertible by the five lemma inside the positive
pretriangulation constructed from `p`. -/
theorem recovered_mem_original
    (p : StableCategory.FrobeniusCommutation.StableHellerParameter S)
    (hp : p.delta = recoveredDelta S e)
    (T : Triangle (Projectives (C := C)))
    (hT : T ∈ HellerClassification.distinguishedTriangles S p e) :
    T ∈ (Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C)))) := by
  obtain ⟨Z, g, h, hT₀⟩ :=
    CategoryTheory.Pretriangulated.distinguished_cocone_triangle T.mor₁
  let T₀ := Triangle.mk T.mor₁ g h
  have hT₀orig : T₀ ∈ (Pretriangulated.distinguishedTriangles :
      Set (Triangle (Projectives (C := C)))) := hT₀
  have hT₀rec : T₀ ∈ HellerClassification.distinguishedTriangles S p e :=
    original_mem_recovered S e p hp T₀ hT₀orig
  obtain ⟨c, hc₁, hc₂⟩ :=
    HellerClassification.complete_distinguished_triangle_morphism
      S p e T₀ T hT₀rec hT (𝟙 _) (𝟙 _) (by simp [T₀])
  let φ : T₀ ⟶ T := Triangle.homMk T₀ T (𝟙 _) (𝟙 _) c
    (by simp [T₀]) hc₁ hc₂
  have hφ₁ : IsIso φ.hom₁ := by
    change IsIso (𝟙 T₀.obj₁)
    infer_instance
  have hφ₂ : IsIso φ.hom₂ := by
    change IsIso (𝟙 T₀.obj₂)
    infer_instance
  have hc : IsIso c := by
    have hφ₃ : IsIso φ.hom₃ := by
      let _ : Pretriangulated (Projectives (C := C)) :=
        HellerClassification.pretriangulated S p e
      exact Pretriangulated.isIso₃_of_isIso₁₂ φ hT₀rec hT hφ₁ hφ₂
    exact hφ₃
  have : IsIso c := hc
  let i : T₀ ≅ T := Triangle.isoMk T₀ T (Iso.refl _) (Iso.refl _) (asIso c)
    (by simp [T₀]) hc₁ hc₂
  exact Pretriangulated.isomorphic_distinguished T₀ hT₀orig T i.symm


/-- The actual recovered distinguished class is exactly the original class. -/
theorem recovered_distinguished_iff_original
    (T : Triangle (Projectives (C := C))) :
    T ∈ HellerClassification.distinguishedTriangles S (recoveredParameter S e) e ↔
      T ∈ (Pretriangulated.distinguishedTriangles :
        Set (Triangle (Projectives (C := C)))) :=
  ⟨recovered_mem_original S e _ rfl T, original_distinguished_deltaExact S e T⟩

/-- The reconstructed positive pretriangulation is the original structure,
including all its TR1--TR3 proof fields. -/
theorem recovered_pretriangulated_eq_original :
    HellerClassification.pretriangulated S (recoveredParameter S e) e =
      (inferInstance : Pretriangulated (Projectives (C := C))) := by
  apply pretriangulated_ext
  ext T
  exact recovered_distinguished_iff_original S e T

/-- Any actual original octahedra are retained by the recovered parameter. -/
theorem recovered_isTriangulated [IsTriangulated (Projectives (C := C))] :
    letI := HellerClassification.pretriangulated S (recoveredParameter S e) e
    IsTriangulated (Projectives (C := C)) := by
  rw [recovered_pretriangulated_eq_original S e]
  infer_instance


section CoherentBaseline

variable (D : Type u) [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsIdempotentComplete D]

local instance coherentProjectiveShift :
    HasShift (Projectives (C := CoherentFunctors.Mod D)) ℤ :=
  YonedaHellerTransport.yonedaHasShift D

local instance coherentProjectiveShiftAdditive (n : ℤ) :
    (shiftFunctor (Projectives (C := CoherentFunctors.Mod D)) n).Additive :=
  YonedaHellerTransport.shifted_additive D n

local instance coherentOriginalPretriangulated :
    Pretriangulated (Projectives (C := CoherentFunctors.Mod D)) :=
  YonedaHellerTransport.originalPretriangulated D

/-- The genuine positive Heller construction for the recovered coherent
baseline parameter, using the Yoneda-transported integer shift. -/
@[instance_reducible]
def coherentBaselinePretriangulated :
    Pretriangulated (Projectives (C := CoherentFunctors.Mod D)) :=
  HellerClassification.pretriangulated (CoherentFunctors.suspension (C := D))
    (coherentBaselineParameter D) (YonedaHellerTransport.transportedShiftOneIso D)

/-- Recovery retains exactly the original distinguished coherent triangles. -/
theorem coherentBaselinePretriangulated_eq_original :
    coherentBaselinePretriangulated D = YonedaHellerTransport.originalPretriangulated D :=
  recovered_pretriangulated_eq_original _ _

/-- Original TR4 proves actual TR4 for the constructed baseline Heller
parameter; no triangulatedness or classification is supplied as a field. -/
theorem coherentBaselineIsTriangulated [IsTriangulated D] :
    letI := coherentBaselinePretriangulated D
    IsTriangulated (Projectives (C := CoherentFunctors.Mod D)) := by
  rw [coherentBaselinePretriangulated_eq_original D]
  exact YonedaHellerTransport.originalIsTriangulated D

local instance : (YonedaHellerTransport.yonedaEquivalence D).functor.CommShift ℤ :=
  YonedaHellerTransport.yonedaCommShift D

local instance : (YonedaHellerTransport.yonedaEquivalence D).inverse.CommShift ℤ :=
  (YonedaHellerTransport.yonedaEquivalence D).commShiftInverse ℤ

local instance : (YonedaHellerTransport.yonedaEquivalence D).CommShift ℤ :=
  (YonedaHellerTransport.yonedaEquivalence D).commShift_of_functor ℤ

/-- The actual Yoneda equivalence is triangulated for the recovered baseline
class, so the original category and baseline projectives agree as triangulated
categories whenever the original category satisfies TR4. -/
theorem coherentBaselineYonedaTriangulated :
    letI := coherentBaselinePretriangulated D
    (YonedaHellerTransport.yonedaEquivalence D).IsTriangulated := by
  rw [coherentBaselinePretriangulated_eq_original D]
  exact YonedaHellerTransport.originalYonedaTriangulated D

end CoherentBaseline

end PretriangulatedV2.HellerRecoveryEquivalence
