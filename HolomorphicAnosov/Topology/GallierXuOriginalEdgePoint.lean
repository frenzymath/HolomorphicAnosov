import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- The native original-edge parameter point lies on the exact barycentric
segment joining the two endpoint singleton vertices. -/
lemma originalEdgePoint_mem_segment {N : ℕ} {u v : Fin N} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    originalEdgePoint u v t ∈
      segment ℝ (Pi.single (min u v) 1) (Pi.single (max u v) 1) := by
  rw [segment_eq_image]
  exact ⟨t, ht, rfl⟩

end HolomorphicAnosov.Topology.GallierXu
