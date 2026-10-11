import PretriangulatedV2.PeriodicComplexes
import PretriangulatedV2.AutoequivalenceShift
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!
Construction of genuine integer-indexed S-periodic complexes from three
projective objects and three cyclically composable differentials. The
bi-infinite orbit construction provides the negative as well as positive
degrees; no periodic complex is supplied as an existence hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace PretriangulatedV2.StableCategory.PeriodicTriangleConstruction

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] (S : C ≌ C)
  [S.functor.Additive]

open AutoequivalenceShift

/-- The actual ambient three-arrow data, before extending it to all degrees. -/
structure ThreeTerm where
  X₀ : C
  X₁ : C
  X₂ : C
  projective₀ : Projective X₀
  projective₁ : Projective X₁
  projective₂ : Projective X₂
  f : X₀ ⟶ X₁
  g : X₁ ⟶ X₂
  h : X₂ ⟶ S.functor.obj X₀
  fg : f ≫ g = 0
  gh : g ≫ h = 0
  hSf : h ≫ S.functor.map f = 0

namespace ThreeTerm

variable {S} (D : ThreeTerm S)

abbrev chain₀ : Chain S := orbit S D.X₀
abbrev chain₁ : Chain S := orbit S D.X₁
abbrev chain₂ : Chain S := orbit S D.X₂

def fChain : D.chain₀ ⟶ D.chain₁ := (evaluation S 0).preimage D.f
def gChain : D.chain₁ ⟶ D.chain₂ := (evaluation S 0).preimage D.g
def hChain : D.chain₂ ⟶ (reindex S 1).obj D.chain₀ :=
  (evaluation S 0).preimage D.h

omit [S.functor.Additive] in
@[simp] theorem fChain_zero : D.fChain.app 0 = D.f :=
  (evaluation S 0).map_preimage (X := D.chain₀) (Y := D.chain₁) D.f
omit [S.functor.Additive] in
@[simp] theorem gChain_zero : D.gChain.app 0 = D.g :=
  (evaluation S 0).map_preimage (X := D.chain₁) (Y := D.chain₂) D.g
omit [S.functor.Additive] in
@[simp] theorem hChain_zero : D.hChain.app 0 = D.h :=
  (evaluation S 0).map_preimage (X := D.chain₂) (Y := (reindex S 1).obj D.chain₀) D.h

omit [S.functor.Additive] in
theorem fChain_one : D.fChain.app 1 = S.functor.map D.f := by
  have h := D.fChain.comm 0
  change S.functor.map (D.fChain.app 0) ≫ 𝟙 _ = 𝟙 _ ≫ D.fChain.app 1 at h
  simpa using h.symm

theorem fChain_gChain : D.fChain ≫ D.gChain = 0 := by
  apply (evaluation S 0).map_injective
  change D.fChain.app 0 ≫ D.gChain.app 0 = 0
  simp [D.fg]

theorem gChain_hChain : D.gChain ≫ D.hChain = 0 := by
  apply (evaluation S 0).map_injective
  change D.gChain.app 0 ≫ D.hChain.app 0 = 0
  simp [D.gh]

theorem hChain_reindex_fChain : D.hChain ≫ (reindex S 1).map D.fChain = 0 := by
  apply (evaluation S 0).map_injective
  change D.hChain.app 0 ≫ D.fChain.app 1 = 0
  rw [hChain_zero, fChain_one]
  exact D.hSf

theorem fChain_gChain_app (q : ℤ) : D.fChain.app q ≫ D.gChain.app q = 0 :=
  congrArg (fun a => a.app q) D.fChain_gChain

theorem gChain_hChain_app (q : ℤ) : D.gChain.app q ≫ D.hChain.app q = 0 :=
  congrArg (fun a => a.app q) D.gChain_hChain

theorem hChain_fChain_app (q : ℤ) :
    D.hChain.app q ≫ D.fChain.app (q + 1) = 0 :=
  congrArg (fun a => a.app q) D.hChain_reindex_fChain

/-- The third arrow with its orbit index exposed in the codomain. -/
def hApp (q : ℤ) : D.chain₂.obj q ⟶ D.chain₀.obj (q + 1) := D.hChain.app q

theorem hApp_fChain (q : ℤ) : D.hApp q ≫ D.fChain.app (q + 1) = 0 :=
  D.hChain_fChain_app q

/-- Interleave the three genuine bi-infinite orbits. -/
abbrev X (n : ℤ) : C :=
  if n % 3 = 0 then D.chain₀.obj (n / 3)
  else if n % 3 = 1 then D.chain₁.obj (n / 3)
  else D.chain₂.obj (n / 3)

omit [S.functor.Additive] in
theorem X_zero_residue {n : ℤ} (hn : n % 3 = 0) :
    D.X n = D.chain₀.obj (n / 3) := by simp [X, hn]

omit [S.functor.Additive] in
theorem X_one_residue {n : ℤ} (hn : n % 3 = 1) :
    D.X n = D.chain₁.obj (n / 3) := by simp [X, hn]

omit [S.functor.Additive] in
theorem X_two_residue {n : ℤ} (hn : n % 3 = 2) :
    D.X n = D.chain₂.obj (n / 3) := by simp [X, hn]

theorem next_zero {n : ℤ} (hn : n % 3 = 0) :
    (n + 1) % 3 = 1 ∧ (n + 1) / 3 = n / 3 := by omega

theorem next_one {n : ℤ} (hn : n % 3 = 1) :
    (n + 1) % 3 = 2 ∧ (n + 1) / 3 = n / 3 := by omega

theorem next_two {n : ℤ} (hn : n % 3 = 2) :
    (n + 1) % 3 = 0 ∧ (n + 1) / 3 = n / 3 + 1 := by omega

/-- The true differential between adjacent integer degrees. -/
def dNext (n : ℤ) : D.X n ⟶ D.X (n + 1) :=
  if hn : n % 3 = 0 then
    eqToHom (D.X_zero_residue hn) ≫ D.fChain.app (n / 3) ≫
      eqToHom (by rw [D.X_one_residue (next_zero hn).1, (next_zero hn).2])
  else if hn' : n % 3 = 1 then
    eqToHom (D.X_one_residue hn') ≫ D.gChain.app (n / 3) ≫
      eqToHom (by rw [D.X_two_residue (next_one hn').1, (next_one hn').2])
  else
    let h₂ : n % 3 = 2 := by omega
    eqToHom (D.X_two_residue h₂) ≫ D.hApp (n / 3) ≫
      eqToHom (by
        rw [D.X_zero_residue (next_two h₂).1, (next_two h₂).2])

theorem dNext_sq (n : ℤ) : D.dNext n ≫ D.dNext (n + 1) = 0 := by
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with h₀ | h₁ | h₂
  · have he : n = 3 * (n / 3) := by omega
    generalize n / 3 = q at he
    subst n
    simp [dNext, X, Int.add_emod, show (3 * q) / 3 = q by omega,
      show (3 * q + 1) / 3 = q by omega,
      Category.assoc]
    rw [← Category.assoc, D.fChain_gChain_app, zero_comp]
  · have he : n = 3 * (n / 3) + 1 := by omega
    generalize n / 3 = q at he
    subst n
    simp [dNext, X, Int.add_emod, show (3 * q + 1) / 3 = q by omega,
      show (3 * q + 1 + 1) / 3 = q by omega,
      Category.assoc]
    rw [← Category.assoc, show ∀ q, D.gChain.app q ≫ D.hApp q = 0 from D.gChain_hChain_app, zero_comp]
  · have he : n = 3 * (n / 3) + 2 := by omega
    generalize n / 3 = q at he
    subst n
    simp [dNext, X, Int.add_emod, Category.assoc]
    have hp : (3 * q + 2) / 3 + 1 = (3 * q + 2 + 1) / 3 := by omega
    change D.hApp ((3 * q + 2) / 3) ≫
      eqToHom (congrArg D.chain₀.obj hp) ≫
      D.fChain.app ((3 * q + 2 + 1) / 3) ≫ eqToHom _ = 0
    rw [← Category.assoc (eqToHom (congrArg D.chain₀.obj hp))]
    rw [← eqToHom_naturality D.fChain.app hp]
    simp only [← Category.assoc]
    rw [D.hApp_fChain]
    simp

/-- The genuinely unbounded cochain complex generated by the three arrows. -/
def complex : CochainComplex C ℤ := CochainComplex.of D.X D.dNext D.dNext_sq

omit [Abelian C] [S.functor.Additive] in
theorem orbit_projective (A : C) (hA : Projective A) (q : ℤ) :
    Projective ((orbit S A).obj q) := by
  have hp : ∀ n, Projective (positiveObj S A n) := by
    intro n
    induction n with
    | zero => exact hA
    | succ n hn => exact S.functor.projective_obj_of_projective hn
  have hn : ∀ n, Projective (negativeObj S A n) := by
    intro n
    induction n with
    | zero => exact hA
    | succ n hn => exact S.inverse.projective_obj_of_projective hn
  cases q with
  | ofNat n => exact hp n
  | negSucc n => exact hn (n + 1)

omit [S.functor.Additive] in
theorem projective_X (n : ℤ) : Projective (D.X n) := by
  dsimp only [X]
  split_ifs
  · exact orbit_projective D.X₀ D.projective₀ _
  · exact orbit_projective D.X₁ D.projective₁ _
  · exact orbit_projective D.X₂ D.projective₂ _

/-- The genuine period isomorphism comes from the adjacent orbit steps. -/
def stepIso (n : ℤ) : S.functor.obj (D.X n) ≅ D.X (n + 3) := by
  have hr : (n + 3) % 3 = n % 3 := by omega
  have hq : (n + 3) / 3 = n / 3 + 1 := by omega
  by_cases h₀ : n % 3 = 0
  · exact S.functor.mapIso (eqToIso (D.X_zero_residue h₀)) ≪≫
      D.chain₀.step (n / 3) ≪≫ eqToIso (by rw [D.X_zero_residue (hr.trans h₀), hq])
  by_cases h₁ : n % 3 = 1
  · exact S.functor.mapIso (eqToIso (D.X_one_residue h₁)) ≪≫
      D.chain₁.step (n / 3) ≪≫ eqToIso (by rw [D.X_one_residue (hr.trans h₁), hq])
  have h₂ : n % 3 = 2 := by omega
  exact S.functor.mapIso (eqToIso (D.X_two_residue h₂)) ≪≫
    D.chain₂.step (n / 3) ≪≫ eqToIso (by rw [D.X_two_residue (hr.trans h₂), hq])

def period (n : ℤ) : S.functor.obj (D.complex.X (n - 3)) ≅ D.complex.X n :=
  D.stepIso (n - 3) ≪≫ eqToIso (congrArg D.X (by omega))

omit [Abelian C] [S.functor.Additive] in
theorem chain_comm_cast (A B : Chain S) (f : A ⟶ B)
    (i j k : ℤ) (hj : j = i) (hk : k = i + 1) :
    S.functor.map (f.app i) ≫
      eqToHom (congrArg (fun q => S.functor.obj (B.obj q)) hj.symm) ≫
      (B.step j).hom ≫ eqToHom (congrArg B.obj (by omega : j + 1 = k)) =
      (A.step i).hom ≫ eqToHom (congrArg A.obj hk.symm) ≫ f.app k := by
  subst j
  subst k
  simpa using f.comm i

omit [S.functor.Additive] in
theorem hApp_comm (i : ℤ) :
    S.functor.map (D.hApp i) ≫ (D.chain₀.step (i + 1)).hom =
      (D.chain₂.step i).hom ≫ D.hApp (i + 1) := by
  simpa only [hApp, reindex, reindexObj, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id] using D.hChain.comm i

omit [S.functor.Additive] in
theorem hApp_comm_cast (i j k : ℤ) (hj : j = i + 1) (hk : k = i + 1) :
    S.functor.map (D.hApp i) ≫
      eqToHom (congrArg (fun q => S.functor.obj (D.chain₀.obj q)) hj.symm) ≫
      (D.chain₀.step j).hom ≫ eqToHom (congrArg D.chain₀.obj (by omega : j + 1 = k + 1)) =
      (D.chain₂.step i).hom ≫ eqToHom (congrArg D.chain₂.obj hk.symm) ≫ D.hApp k := by
  subst j
  subst k
  simpa using D.hApp_comm i

omit [S.functor.Additive] in
theorem stepIso_dNext (n : ℤ) :
    S.functor.map (D.dNext n) ≫ (D.stepIso (n + 1)).hom =
      (D.stepIso n).hom ≫ D.dNext (n + 3) ≫
        eqToHom (congrArg D.X (by omega)) := by
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with h₀ | h₁ | h₂
  · simp [stepIso, dNext, X, h₀, Category.assoc, eqToHom_map,
      show (n + 1) % 3 = 1 by omega, show (n + 3) % 3 = 0 by omega,
      show (n + 1 + 3) % 3 = 1 by omega, show (n + 3 + 1) % 3 = 1 by omega]
    have hj : (n + 1) / 3 = n / 3 := by omega
    have hk : (n + 3) / 3 = n / 3 + 1 := by omega
    have hp : D.chain₁.obj ((n + 3) / 3) = D.X (n + 1 + 3) := by
      rw [D.X_one_residue (by omega)]
      exact congrArg D.chain₁.obj (by omega)
    change eqToHom _ ≫ (S.functor.map (D.fChain.app (n / 3)) ≫
      eqToHom (congrArg (fun q => S.functor.obj (D.chain₁.obj q)) hj.symm) ≫
      (D.chain₁.step ((n + 1) / 3)).hom ≫ eqToHom _) =
      eqToHom _ ≫ ((D.chain₀.step (n / 3)).hom ≫
        eqToHom (congrArg D.chain₀.obj hk.symm) ≫ D.fChain.app ((n + 3) / 3) ≫ eqToHom _)
    have hh := chain_comm_cast D.chain₀ D.chain₁ D.fChain (n / 3) ((n + 1) / 3)
      ((n + 3) / 3) hj hk
    have hh' := congrArg (fun a => a ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans] using congrArg (fun a => eqToHom
      (congrArg S.functor.obj (D.X_zero_residue h₀)) ≫ a) hh'
  · simp [stepIso, dNext, X, h₁, Category.assoc, eqToHom_map,
      show (n + 1) % 3 = 2 by omega, show (n + 3) % 3 = 1 by omega,
      show (n + 1 + 3) % 3 = 2 by omega, show (n + 3 + 1) % 3 = 2 by omega]
    have hj : (n + 1) / 3 = n / 3 := by omega
    have hk : (n + 3) / 3 = n / 3 + 1 := by omega
    have hp : D.chain₂.obj ((n + 3) / 3) = D.X (n + 1 + 3) := by
      rw [D.X_two_residue (by omega)]
      exact congrArg D.chain₂.obj (by omega)
    change eqToHom _ ≫ (S.functor.map (D.gChain.app (n / 3)) ≫
      eqToHom (congrArg (fun q => S.functor.obj (D.chain₂.obj q)) hj.symm) ≫
      (D.chain₂.step ((n + 1) / 3)).hom ≫ eqToHom _) =
      eqToHom _ ≫ ((D.chain₁.step (n / 3)).hom ≫
        eqToHom (congrArg D.chain₁.obj hk.symm) ≫ D.gChain.app ((n + 3) / 3) ≫ eqToHom _)
    have hh := chain_comm_cast D.chain₁ D.chain₂ D.gChain (n / 3) ((n + 1) / 3)
      ((n + 3) / 3) hj hk
    have hh' := congrArg (fun a => a ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans] using congrArg (fun a => eqToHom
      (congrArg S.functor.obj (D.X_one_residue h₁)) ≫ a) hh'
  · simp [stepIso, dNext, X, h₂, Category.assoc, eqToHom_map,
      show (n + 1) % 3 = 0 by omega, show (n + 3) % 3 = 2 by omega,
      show (n + 1 + 3) % 3 = 0 by omega, show (n + 3 + 1) % 3 = 0 by omega]

    have hj : (n + 1) / 3 = n / 3 + 1 := by omega
    have hk : (n + 3) / 3 = n / 3 + 1 := by omega
    have hp : D.chain₀.obj ((n + 3) / 3 + 1) = D.X (n + 1 + 3) := by
      rw [D.X_zero_residue (by omega)]
      exact congrArg D.chain₀.obj (by omega)
    change eqToHom _ ≫ (S.functor.map (D.hApp (n / 3)) ≫
      eqToHom (congrArg (fun q => S.functor.obj (D.chain₀.obj q)) hj.symm) ≫
      (D.chain₀.step ((n + 1) / 3)).hom ≫ eqToHom _) =
      eqToHom _ ≫ ((D.chain₂.step (n / 3)).hom ≫
        eqToHom (congrArg D.chain₂.obj hk.symm) ≫ D.hApp ((n + 3) / 3) ≫ eqToHom _)
    have hh := D.hApp_comm_cast (n / 3) ((n + 1) / 3) ((n + 3) / 3) hj hk
    have hh' := congrArg (fun a => a ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans] using congrArg (fun a => eqToHom
      (congrArg S.functor.obj (D.X_two_residue h₂)) ≫ a) hh'

theorem period_dNext (n : ℤ) :
    S.functor.map (D.dNext (n - 3)) ≫
      eqToHom (congrArg (fun q => S.functor.obj (D.X q)) (by omega : n - 3 + 1 = n + 1 - 3)) ≫
      (D.period (n + 1)).hom = (D.period n).hom ≫ D.dNext n := by
  have hp : n - 3 + 1 = n + 1 - 3 := by omega
  have hq : n - 3 + 3 = n := by omega
  have hh := D.stepIso_dNext (n - 3)
  have hh' := congrArg (fun a => a ≫ eqToHom (congrArg D.X (by omega : n - 3 + 1 + 3 = n + 1))) hh
  dsimp only [period, Iso.trans_hom, eqToIso.hom]
  change S.functor.map (D.dNext (n - 3)) ≫
      eqToHom (congrArg (fun q => S.functor.obj (D.X q)) hp) ≫
      (D.stepIso (n + 1 - 3)).hom ≫ eqToHom _ =
      ((D.stepIso (n - 3)).hom ≫ eqToHom (congrArg D.X hq)) ≫ D.dNext n
  rw [← Category.assoc (eqToHom (congrArg (fun q => S.functor.obj (D.X q)) hp))]
  rw [← eqToHom_naturality (fun q => (D.stepIso q).hom) hp]
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    eqToHom_naturality D.dNext hq] using hh'

theorem period_comm (n m : ℤ) :
    S.functor.map (D.complex.d (n - 3) (m - 3)) ≫ (D.period m).hom =
      (D.period n).hom ≫ D.complex.d n m := by
  by_cases hm : n + 1 = m
  · subst m
    dsimp only [complex, CochainComplex.of, CochainComplex.of.d]
    simp only [show n - 3 + 1 = n + 1 - 3 by omega, dif_pos, Category.assoc,
      Functor.map_comp, eqToHom_map, eqToHom_refl, Category.comp_id]
    exact D.period_dNext n
  · have hm' : n - 3 + 1 ≠ m - 3 := by omega
    simp only [complex, CochainComplex.of_d_ne _ _ hm, CochainComplex.of_d_ne _ _ hm',
      Functor.map_zero, zero_comp, comp_zero]

/-- The actual periodic projective complex generated by the three arrows. -/
def sComplex : PeriodicComplexes.SComplex S where
  complex := D.complex
  projective := D.projective_X
  period := D.period
  period_comm := D.period_comm

theorem complex_X₀ : D.complex.X 0 = D.X₀ := rfl
theorem complex_X₁ : D.complex.X 1 = D.X₁ := rfl
theorem complex_X₂ : D.complex.X 2 = D.X₂ := rfl
theorem complex_X₃ : D.complex.X 3 = S.functor.obj D.X₀ := rfl

@[simp] theorem complex_d₀₁ : D.complex.d 0 1 = D.f := by
  change CochainComplex.of.d D.X D.dNext 0 (0 + 1) = D.f
  rw [CochainComplex.of_d]
  simp [dNext, X]

@[simp] theorem complex_d₁₂ : D.complex.d 1 2 = D.g := by
  change CochainComplex.of.d D.X D.dNext 1 (1 + 1) = D.g
  rw [CochainComplex.of_d]
  simp [dNext, X]

@[simp] theorem complex_d₂₃ : D.complex.d 2 3 = D.h := by
  change CochainComplex.of.d D.X D.dNext 2 (2 + 1) = D.h
  rw [CochainComplex.of_d]
  simp [dNext, X, hApp]

@[simp] theorem period_three : (D.period 3).hom = 𝟙 (S.functor.obj D.X₀) := by
  simp [period, stepIso, X]
  rfl

/-- A genuine three-component map with all three commuting squares. -/
structure Map (R : ThreeTerm S) where
  a₀ : D.X₀ ⟶ R.X₀
  a₁ : D.X₁ ⟶ R.X₁
  a₂ : D.X₂ ⟶ R.X₂
  comm₀ : a₀ ≫ R.f = D.f ≫ a₁
  comm₁ : a₁ ≫ R.g = D.g ≫ a₂
  comm₂ : a₂ ≫ R.h = D.h ≫ S.functor.map a₀

namespace Map

variable {D R : ThreeTerm S} (a : D.Map R)

def chain₀ : D.chain₀ ⟶ R.chain₀ := (evaluation S 0).preimage a.a₀
def chain₁ : D.chain₁ ⟶ R.chain₁ := (evaluation S 0).preimage a.a₁
def chain₂ : D.chain₂ ⟶ R.chain₂ := (evaluation S 0).preimage a.a₂

omit [S.functor.Additive] in
@[simp] theorem chain₀_zero : a.chain₀.app 0 = a.a₀ :=
  (evaluation S 0).map_preimage _
omit [S.functor.Additive] in
@[simp] theorem chain₁_zero : a.chain₁.app 0 = a.a₁ :=
  (evaluation S 0).map_preimage _
omit [S.functor.Additive] in
@[simp] theorem chain₂_zero : a.chain₂.app 0 = a.a₂ :=
  (evaluation S 0).map_preimage _

omit [S.functor.Additive] in
theorem chain₀_one : a.chain₀.app 1 = S.functor.map a.a₀ := by
  have h := a.chain₀.comm 0
  change S.functor.map (a.chain₀.app 0) ≫ 𝟙 _ = 𝟙 _ ≫ a.chain₀.app 1 at h
  simpa using h.symm

omit [S.functor.Additive] in
theorem comm_chain₀ : a.chain₀ ≫ R.fChain = D.fChain ≫ a.chain₁ := by
  apply (evaluation S 0).map_injective
  change a.chain₀.app 0 ≫ R.fChain.app 0 = D.fChain.app 0 ≫ a.chain₁.app 0
  simpa using a.comm₀

omit [S.functor.Additive] in
theorem comm_chain₁ : a.chain₁ ≫ R.gChain = D.gChain ≫ a.chain₂ := by
  apply (evaluation S 0).map_injective
  change a.chain₁.app 0 ≫ R.gChain.app 0 = D.gChain.app 0 ≫ a.chain₂.app 0
  simpa using a.comm₁

omit [S.functor.Additive] in
theorem comm_chain₂ : a.chain₂ ≫ R.hChain = D.hChain ≫ (reindex S 1).map a.chain₀ := by
  apply (evaluation S 0).map_injective
  change a.chain₂.app 0 ≫ R.hChain.app 0 = D.hChain.app 0 ≫ a.chain₀.app 1
  simpa [a.chain₀_one] using a.comm₂

omit [S.functor.Additive] in
theorem comm_app₀ (q : ℤ) : a.chain₀.app q ≫ R.fChain.app q = D.fChain.app q ≫ a.chain₁.app q :=
  congrArg (fun t => t.app q) a.comm_chain₀

omit [S.functor.Additive] in
theorem comm_app₁ (q : ℤ) : a.chain₁.app q ≫ R.gChain.app q = D.gChain.app q ≫ a.chain₂.app q :=
  congrArg (fun t => t.app q) a.comm_chain₁

omit [S.functor.Additive] in
theorem comm_app₂ (q : ℤ) : a.chain₂.app q ≫ R.hApp q = D.hApp q ≫ a.chain₀.app (q + 1) :=
  congrArg (fun t => t.app q) a.comm_chain₂

/-- Actual integer-degree components, obtained from all three orbit maps. -/
def app (n : ℤ) : D.X n ⟶ R.X n :=
  if hn : n % 3 = 0 then
    eqToHom (D.X_zero_residue hn) ≫ a.chain₀.app (n / 3) ≫ eqToHom (R.X_zero_residue hn).symm
  else if hn' : n % 3 = 1 then
    eqToHom (D.X_one_residue hn') ≫ a.chain₁.app (n / 3) ≫ eqToHom (R.X_one_residue hn').symm
  else
    let h₂ : n % 3 = 2 := by omega
    eqToHom (D.X_two_residue h₂) ≫ a.chain₂.app (n / 3) ≫ eqToHom (R.X_two_residue h₂).symm

omit [S.functor.Additive] in
@[simp] theorem app_zero : a.app 0 = a.a₀ := by simp [app, X]
omit [S.functor.Additive] in
@[simp] theorem app_one : a.app 1 = a.a₁ := by simp [app, X]
omit [S.functor.Additive] in
@[simp] theorem app_two : a.app 2 = a.a₂ := by simp [app, X]

omit [Abelian C] [S.functor.Additive] in
theorem square_cast {A B A' B' : ℤ → C} (t : ℤ → ℤ)
    (f : ∀ q, A q ⟶ B (t q)) (g : ∀ q, A' q ⟶ B' (t q))
    (a : ∀ q, A q ⟶ A' q) (b : ∀ q, B q ⟶ B' q)
    (h : ∀ q, a q ≫ g q = f q ≫ b (t q)) (i j : ℤ) (hj : j = t i) :
    a i ≫ g i ≫ eqToHom (congrArg B' hj.symm) =
      f i ≫ eqToHom (congrArg B hj.symm) ≫ b j := by
  subst j
  simpa using h i

omit [S.functor.Additive] in
theorem app_dNext (n : ℤ) : a.app n ≫ R.dNext n = D.dNext n ≫ a.app (n + 1) := by
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with h₀ | h₁ | h₂
  · simp [app, dNext, X, h₀, show (n + 1) % 3 = 1 by omega, Category.assoc]
    have hj : (n + 1) / 3 = n / 3 := by omega
    have hp : R.chain₁.obj ((n + 1) / 3) = R.X (n + 1) :=
      (R.X_one_residue (by omega)).symm
    have hh := square_cast (fun q => q) D.fChain.app R.fChain.app
      a.chain₀.app a.chain₁.app a.comm_app₀
      (n / 3) ((n + 1) / 3) hj
    have hh' := congrArg (fun b => b ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans] using congrArg (fun b =>
      eqToHom (D.X_zero_residue h₀) ≫ b) hh'
  · simp [app, dNext, X, h₁, show (n + 1) % 3 = 2 by omega, Category.assoc]
    have hj : (n + 1) / 3 = n / 3 := by omega
    have hp : R.chain₂.obj ((n + 1) / 3) = R.X (n + 1) :=
      (R.X_two_residue (by omega)).symm
    have hh := square_cast (fun q => q) D.gChain.app R.gChain.app
      a.chain₁.app a.chain₂.app a.comm_app₁
      (n / 3) ((n + 1) / 3) hj
    have hh' := congrArg (fun b => b ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans] using congrArg (fun b =>
      eqToHom (D.X_one_residue h₁) ≫ b) hh'
  · simp [app, dNext, X, h₂, show (n + 1) % 3 = 0 by omega, Category.assoc]
    have hj : (n + 1) / 3 = n / 3 + 1 := by omega
    have hp : R.chain₀.obj ((n + 1) / 3) = R.X (n + 1) :=
      (R.X_zero_residue (by omega)).symm
    have hh := square_cast (fun q => q + 1) D.hApp R.hApp
      a.chain₂.app a.chain₀.app a.comm_app₂
      (n / 3) ((n + 1) / 3) hj
    have hh' := congrArg (fun b => b ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans] using congrArg (fun b =>
      eqToHom (D.X_two_residue h₂) ≫ b) hh'

/-- The genuine unbounded cochain map extending the three original components. -/
def cochainMap : D.complex ⟶ R.complex :=
  CochainComplex.ofHom a.app (by
    intro n
    change a.app n ≫ CochainComplex.of.d R.X R.dNext n (n + 1) =
      CochainComplex.of.d D.X D.dNext n (n + 1) ≫ a.app (n + 1)
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact a.app_dNext n)

@[simp] theorem cochainMap_zero : a.cochainMap.f 0 = a.a₀ := a.app_zero
@[simp] theorem cochainMap_one : a.cochainMap.f 1 = a.a₁ := a.app_one
@[simp] theorem cochainMap_two : a.cochainMap.f 2 = a.a₂ := a.app_two

omit [S.functor.Additive] in
theorem app_step (n : ℤ) :
    S.functor.map (a.app n) ≫ (R.stepIso n).hom =
      (D.stepIso n).hom ≫ a.app (n + 3) := by
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with h₀ | h₁ | h₂
  · simp [app, stepIso, X, h₀, show (n + 3) % 3 = 0 by omega,
      Functor.map_comp, eqToHom_map, Category.assoc]
    have hk : (n + 3) / 3 = n / 3 + 1 := by omega
    have hp : R.chain₀.obj ((n + 3) / 3) = R.X (n + 3) :=
      (R.X_zero_residue (by omega)).symm
    have hh := chain_comm_cast D.chain₀ R.chain₀ a.chain₀
      (n / 3) (n / 3) ((n + 3) / 3) rfl hk
    have hh' := congrArg (fun b => b ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp] using
      congrArg (fun b => eqToHom (congrArg S.functor.obj (D.X_zero_residue h₀)) ≫ b) hh'
  · simp [app, stepIso, X, h₁, show (n + 3) % 3 = 1 by omega,
      Functor.map_comp, eqToHom_map, Category.assoc]
    have hk : (n + 3) / 3 = n / 3 + 1 := by omega
    have hp : R.chain₁.obj ((n + 3) / 3) = R.X (n + 3) :=
      (R.X_one_residue (by omega)).symm
    have hh := chain_comm_cast D.chain₁ R.chain₁ a.chain₁
      (n / 3) (n / 3) ((n + 3) / 3) rfl hk
    have hh' := congrArg (fun b => b ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp] using
      congrArg (fun b => eqToHom (congrArg S.functor.obj (D.X_one_residue h₁)) ≫ b) hh'
  · simp [app, stepIso, X, h₂, show (n + 3) % 3 = 2 by omega,
      Functor.map_comp, eqToHom_map, Category.assoc]
    have hk : (n + 3) / 3 = n / 3 + 1 := by omega
    have hp : R.chain₂.obj ((n + 3) / 3) = R.X (n + 3) :=
      (R.X_two_residue (by omega)).symm
    have hh := chain_comm_cast D.chain₂ R.chain₂ a.chain₂
      (n / 3) (n / 3) ((n + 3) / 3) rfl hk
    have hh' := congrArg (fun b => b ≫ eqToHom hp) hh
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp] using
      congrArg (fun b => eqToHom (congrArg S.functor.obj (D.X_two_residue h₂)) ≫ b) hh'

theorem app_period (n : ℤ) :
    S.functor.map (a.app (n - 3)) ≫ (R.period n).hom =
      (D.period n).hom ≫ a.app n := by
  have hp : n - 3 + 3 = n := by omega
  have hh := congrArg (fun b => b ≫ eqToHom (congrArg R.X hp)) (a.app_step (n - 3))
  dsimp only [period, Iso.trans_hom, eqToIso.hom]
  simpa only [Category.assoc, eqToHom_naturality a.app hp] using hh

/-- The constructed cochain map is genuinely fixed by periodic twisting. -/
theorem twistMap_cochainMap :
    D.sComplex.twistMap R.sComplex a.cochainMap = a.cochainMap := by
  ext n
  change (D.period n).inv ≫ S.functor.map (a.app (n - 3)) ≫ (R.period n).hom = a.app n
  rw [a.app_period]
  simp

end Map

end ThreeTerm

end PretriangulatedV2.StableCategory.PeriodicTriangleConstruction
