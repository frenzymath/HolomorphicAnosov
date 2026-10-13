import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWPointVertexPrismBoundaryFacesProviderG12

/-!
# Boundary faces of the native prism disk

Source: Fritsch–Piccinini, *Cellular Structures in Topology* (1990),
Theorem 2.2.2(ii), p.58, and the prism boundary calculation used in
Theorem 2.3.1, pp.62–63.  In the maximum norm, a prism disk boundary is
either an endpoint face or a lateral face over the source sphere.
-/

open _root_.Topology
universe u

namespace HolomorphicAnosov

/-- A boundary point of a native `(d+1)`-disk lies on an endpoint face or on
the lateral face over the `d`-disk sphere.  This is the coordinate interface
used when checking the mapping-cone prism attaching map. -/
theorem cw_point_vertex_prism_boundary_faces
    (d : ℕ) (w : Fin (d + 1) → ℝ)
    (hw : w ∈ Metric.sphere (0 : Fin (d + 1) → ℝ) 1) :
    w (Fin.last d) = -1 ∨ w (Fin.last d) = 1 ∨
      ∃ j : Fin d, ‖w j.castSucc‖ = 1 := by
  exact cw_point_vertex_prism_boundary_faces_provider d w hw

end HolomorphicAnosov

