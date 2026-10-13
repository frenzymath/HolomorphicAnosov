import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- The literal paired-edge relation is symmetric: reversing the two face disks
retains the same edge label, interval parameter, and side-point witnesses. -/
lemma edgeIdentification_symm {P : Presentation} {x y : FaceDisks P} :
    edgeIdentification P x y → edgeIdentification P y x := by
  rintro ⟨i, j, t, ht, hlabel, hx, hy⟩
  exact ⟨j, i, t, ht, hlabel.symm, hy, hx⟩

end HolomorphicAnosov.Topology.GallierXu
