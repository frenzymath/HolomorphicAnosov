import HolomorphicAnosov.Topology.StdSimplexOneBoundaryEndpoints
import HolomorphicAnosov.Topology.CWComplex.CellInLowerSkeletonBoundary

open Convexity
universe u
namespace HolomorphicAnosov.Topology

/-- A characteristic simplex edge meets the zero-skeleton only at its two
endpoint parameters. Source: Hatcher, Algebraic Topology, Appendix pp.519–520
and Theorem 2A.1 proof p.167. A characteristic disk point in the lower
skeleton lies on its boundary sphere. Interior preservation of the supplied
simplex/disk homeomorphism therefore excludes positive barycentric weights,
and the standard interval boundary consists exactly of its two vertices.
This allows the two endpoint images to coincide and requires no regular CW
structure or injectivity of the characteristic map on its boundary. -/
theorem cw_simplexEdge_vertex_endpoints
    {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [_root_.Topology.CWComplex (Set.univ : Set Z)]
    (i : _root_.Topology.RelCWComplex.cell (Set.univ : Set Z) 1)
    (disk : StdSimplex ℝ (Fin 2) ≃ₜ Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (hdisk : ∀ t, (disk t).val ∈ Metric.ball (0 : Fin 1 → ℝ) 1 ↔
      ∀ j, 0 < t.weights j)
    (e : C(StdSimplex ℝ (Fin 2), Z))
    (he : ∀ t, e t = _root_.Topology.RelCWComplex.map 1 i (disk t).val)
    (t : StdSimplex ℝ (Fin 2))
    (ht : e t ∈ (_root_.Topology.RelCWComplex.skeleton
      (Set.univ : Set Z) 0 : Set Z)) :
    t = StdSimplex.single 0 ∨ t = StdSimplex.single 1 := by
  apply stdSimplexOne_boundary_endpoints t
  intro hpos
  have hball := (hdisk t).mpr hpos
  have hnorm : ‖(disk t).val‖ = 1 :=
    HolomorphicAnosov.cw_cell_in_lower_skeleton_is_boundary 1 i (disk t) (by
      simpa only [he t, _root_.Topology.RelCWComplex.skeleton, zero_add, Nat.cast_one] using ht)
  have hlt : ‖(disk t).val‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hball
  exact (ne_of_lt hlt) hnorm

end HolomorphicAnosov.Topology
