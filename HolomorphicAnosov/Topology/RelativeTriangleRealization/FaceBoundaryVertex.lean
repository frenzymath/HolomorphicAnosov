import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic
import HolomorphicAnosov.Topology.StdSimplexOneBoundaryEndpoints

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-!
# Boundary points of ordered triangle faces

Source: Hatcher, *Algebraic Topology*, pp.103--104 and p.167. The closed
ordered edge is attached along its two endpoint vertices; this is the
coordinate statement needed for the lower-boundary part of the finite CW
assembly.
-/

/-- A non-interior parameter of an ordered triangle face is a vertex.

Proof: the standard interval has nonnegative barycentric coordinates summing
to one. If the parameter is outside the strictly positive interior, one of
its two coordinates vanishes, so the endpoint theorem identifies it with an
ordered endpoint. The order-preserving face map sends each endpoint to the
corresponding singleton vertex of the triangle. -/
theorem face_boundary_vertex {j : Fin 3} {t : Simplex 1}
    (ht : ¬ t ∈ interior 1) :
    ∃ v : Fin 3, face j t = Convexity.StdSimplex.single v := by
  obtain ht | ht := Topology.stdSimplexOne_boundary_endpoints t ht
  · refine ⟨j.succAbove 0, ?_⟩
    rw [ht]
    exact Convexity.StdSimplex.map_single 0 j.succAbove
  · refine ⟨j.succAbove 1, ?_⟩
    rw [ht]
    exact Convexity.StdSimplex.map_single 1 j.succAbove


end HolomorphicAnosov.RelativeTriangleRealization
