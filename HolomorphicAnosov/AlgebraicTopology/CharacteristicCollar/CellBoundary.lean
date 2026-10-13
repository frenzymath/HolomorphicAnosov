import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellDisk

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The boundary of the characteristic m-disk is its subset of points of maximum norm one; it is empty in degree zero.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def cellBoundary (m : ℕ) : Set (CellDisk.{u} m) :=
  {z | z.down.1 ∈ Metric.sphere (0 : Fin m → ℝ) 1}

end HolomorphicAnosov.CharacteristicCellComparison
