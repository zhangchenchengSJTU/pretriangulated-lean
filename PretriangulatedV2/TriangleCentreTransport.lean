import PretriangulatedV2.Heller

/-! Triangle-centre units commute with naturally isomorphic suspensions. -/

open CategoryTheory

namespace PretriangulatedV2.TriangleCenterUnit

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {F G : C ⥤ C}

/-- Transport the proved suspension commutation through a natural isomorphism. -/
def ofNatIso (e : F ≅ G) (u : TriangleCenterUnit G) : TriangleCenterUnit F where
  iso := u.iso
  commutes X := by
    apply (cancel_mono (e.hom.app X)).mp
    calc
      F.map (u.iso.hom.app X) ≫ e.hom.app X =
          e.hom.app X ≫ G.map (u.iso.hom.app X) := e.hom.naturality _
      _ = e.hom.app X ≫ u.iso.hom.app (G.obj X) := by rw [u.commutes]
      _ = u.iso.hom.app (F.obj X) ≫ e.hom.app X := by
        simpa only [Functor.id_map] using u.iso.hom.naturality (e.hom.app X)

omit [Preadditive C] in
@[simp]
theorem ofNatIso_iso (e : F ≅ G) (u : TriangleCenterUnit G) :
    (ofNatIso e u).iso = u.iso := rfl

end PretriangulatedV2.TriangleCenterUnit
