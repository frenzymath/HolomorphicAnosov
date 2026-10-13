import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The collar chart space is the topological disjoint union of the lower skeleton and one disk collar for each cell.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
abbrev CollarCharts (m : ℕ) := ↥(lowerSkeleton X m) ⊕
  (Σ _i : RelCWComplex.cell (univ : Set X) m, DiskCollar.{u} m)

end HolomorphicAnosov.CharacteristicCellComparison
