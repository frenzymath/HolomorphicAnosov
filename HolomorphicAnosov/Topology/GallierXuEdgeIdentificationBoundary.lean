import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- Every prescribed edge point lies on the unit-circle boundary of its face disk. -/
lemma sidePoint_norm {P : Presentation} (f : Fin P.length)
    (i : Fin (P.get f).length) (t : ℝ) :
    ‖sidePoint P f i t‖ = 1 := by
  dsimp [sidePoint]
  rw [Complex.norm_exp]
  simp

/-- An elementary edge identification can only relate points on the two face boundaries. -/
lemma edgeIdentification_boundary {P : Presentation} {x y : FaceDisks P}
    (hxy : edgeIdentification P x y) :
    ‖(x.2 : ℂ)‖ = 1 ∧ ‖(y.2 : ℂ)‖ = 1 := by
  rcases hxy with ⟨i, j, t, ht, hlabel, hx, hy⟩
  exact ⟨hx ▸ sidePoint_norm x.1 i t, hy ▸ sidePoint_norm y.1 j t⟩

end HolomorphicAnosov.Topology.GallierXu
