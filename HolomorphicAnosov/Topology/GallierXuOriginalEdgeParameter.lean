import HolomorphicAnosov.Topology.GallierXuOriginalEdgePointCarrier

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- The unoriented original edge label is invariant under swapping endpoints. -/
lemma edgeLabel_comm {N : ℕ} (u v : Fin N) :
    edgeLabel u v = edgeLabel v u := by
  simp [edgeLabel, min_comm, max_comm]

/-- Native original-edge points use the same unoriented parameter after swapping endpoints. -/
lemma originalEdgePoint_comm {N : ℕ} (u v : Fin N) (t : ℝ) :
    originalEdgePoint u v t = originalEdgePoint v u t := by
  simp [originalEdgePoint, min_comm, max_comm]

/-- A cycle-edge witness and its normalized native point determine a point of the
carrier-side cycle contour. -/
lemma originalEdgePoint_mem_cycleCarrier {N : ℕ}
    {K : AbstractSimplicialComplex (Fin N)} {l : List (Fin N)}
    {u v : Fin N} (hcycle : cycleEdge l u v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hedge : ({u, v} : Finset (Fin N)) ∈ K.faces) :
    (⟨originalEdgePoint u v t, originalEdgePoint_mem_carrier K hedge ht⟩ :
      ↥(carrier K)) ∈ cycleCarrier l := by
  refine ⟨u, v, hcycle, ?_⟩
  rcases le_total u v with huv | hvu
  · simpa [min_eq_left huv, max_eq_right huv] using
      (originalEdgePoint_mem_segment (u := u) (v := v) ht)
  · rw [segment_symm]
    simpa [min_eq_right hvu, max_eq_left hvu] using
      (originalEdgePoint_mem_segment (u := u) (v := v) ht)

end HolomorphicAnosov.Topology.GallierXu
