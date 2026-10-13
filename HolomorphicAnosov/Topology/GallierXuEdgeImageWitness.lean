import HolomorphicAnosov.Topology.GallierXuProjectEdgeEquality

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- A side-point equality packages a face-disk representative into the matching
labeled edge image at the same normalized parameter. -/
lemma project_mem_edgeImage_of_sidePoint {P : Presentation}
    (x : FaceDisks P) (i : Fin (P.get x.1).length) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hx : (x.2 : ℂ) = sidePoint P x.1 i t) :
    project P x ∈ edgeImage P ((P.get x.1).get i).1 := by
  exact ⟨x, i, t, ht, rfl, hx, rfl⟩

/-- An edge-identification witness puts both quotient endpoints on one common
labeled edge image. -/
lemma edgeIdentification_common_edgeImage {P : Presentation}
    {x y : FaceDisks P} (hxy : edgeIdentification P x y) :
    ∃ a : ℕ, project P x ∈ edgeImage P a ∧ project P y ∈ edgeImage P a := by
  rcases hxy with ⟨i, j, t, ht, hl, hx, hy⟩
  refine ⟨((P.get x.1).get i).1, ?_, ?_⟩
  · exact project_mem_edgeImage_of_sidePoint x i t ht hx
  · exact ⟨y, j, t, ht, hl.symm, hy, rfl⟩

end HolomorphicAnosov.Topology.GallierXu
