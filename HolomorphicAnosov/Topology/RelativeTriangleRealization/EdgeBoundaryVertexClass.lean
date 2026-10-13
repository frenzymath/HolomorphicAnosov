import HolomorphicAnosov.Topology.RelativeTriangleRealization.FaceBoundaryVertex

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-!
# Boundary of an ordered edge lies in the quotient vertex classes

Source: Hatcher, *Algebraic Topology*, pp.103--104 and p.167. The endpoints
of every ordered edge are triangle vertices, and the paired-triangle quotient
sends triangle vertices to the finite vertex-class set.
-/

/-- A non-interior point of an ordered edge has quotient image in the vertex
class set. -/
theorem edge_boundary_mem_vertexClass {m : ℕ}
    (pair : Occurrence m → Occurrence m)
    (o : Occurrence m) (t : Simplex 1) (ht : ¬ t ∈ interior 1) :
    edge pair o t ∈ VertexClass pair := by
  obtain ⟨v, hv⟩ := face_boundary_vertex ht
  refine ⟨(o.1, v), ?_⟩
  change Quotient.mk _ (o.1, Convexity.StdSimplex.single v) =
    Quotient.mk _ (o.1, face o.2 t)
  rw [hv]


end HolomorphicAnosov.RelativeTriangleRealization
