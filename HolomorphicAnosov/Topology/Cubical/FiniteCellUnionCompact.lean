import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision
import Mathlib.Topology.Order.Compact

/-!
# Compact unions of original cubical cells

Source: Hatcher, *Algebraic Topology*, Appendix A.2, p.521, the finite closed-cell
compactness argument. This is its coordinate-cell specialization for the original
finite subdivision, including degenerate faces and the empty selection.
DAG: `topo.cubical_finite_cell_union_compact_g2`.
-/

namespace HolomorphicAnosov.Cubical
open Set

/-- Every union of selected cells in a finite rectilinear subdivision is compact.

Agent-written coordinate specialization of Hatcher Appendix A.2, p.521.
Each carrier is a finite product of compact real closed intervals; intervals of
zero length are allowed. The selected cells form a finite subset of `K.cells`.
Their union is compact by finite-union compactness. If the selection is empty,
the union is empty and remains compact. All carriers retain the ambient topology. -/
theorem finiteCellUnion_compact {N : ℕ} (K : FiniteRectilinearSubdivision N)
    (E : Set (ClosedCoordinateCell N)) (hE : E ⊆ K.cells) :
    IsCompact (⋃ c ∈ E, c.carrier) := by
  apply (K.finite_cells.subset hE).isCompact_biUnion
  intro c hc
  change IsCompact (Icc c.lower c.upper)
  rw [← pi_univ_Icc]
  exact isCompact_univ_pi fun i ↦
    ConditionallyCompleteLinearOrder.isCompact_Icc (c.lower i) (c.upper i)

end HolomorphicAnosov.Cubical

