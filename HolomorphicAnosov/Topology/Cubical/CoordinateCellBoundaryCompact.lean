import HolomorphicAnosov.Topology.Cubical.ClosedCoordinateCell
import Mathlib.Topology.Order.Compact

open Set
namespace HolomorphicAnosov.Cubical

/-- The coordinate boundary of every closed coordinate cell is compact, including
cells of dimension zero, whose coordinate boundary is empty.

Source: Hatcher, Algebraic Topology, Appendix A.2–A.4, pp.521–522, and the compact
boundary used in Bredon, Topology and Geometry, I.16.3–16.4, pp.56–57. This explicit
coordinate verification fills the compactness step in the product-collar proof.
Each active-coordinate endpoint condition is closed by continuity of coordinate
evaluation. Their finite union is closed. Intersecting it with the compact product
of the closed coordinate intervals gives the literal coordinate boundary. -/
theorem coordinate_cell_boundary_compact{N : ℕ} (c : ClosedCoordinateCell N) :
    IsCompact {x : Fin N → ℝ | x ∈ c.carrier ∧ ∃ i : Fin N,
      c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)} := by
  have hfaces : IsClosed {x : Fin N → ℝ | ∃ i : Fin N,
      c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)} := by
    have heq : {x : Fin N → ℝ | ∃ i : Fin N,
        c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)} =
        ⋃ i : Fin N, ⋃ (_ : c.lower i < c.upper i),
          {x : Fin N → ℝ | x i = c.lower i ∨ x i = c.upper i} := by
      ext x
      simp
    rw [heq]
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro _
    exact (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)
  exact (isCompact_Icc : IsCompact (Icc c.lower c.upper)).inter_right hfaces

end HolomorphicAnosov.Cubical
