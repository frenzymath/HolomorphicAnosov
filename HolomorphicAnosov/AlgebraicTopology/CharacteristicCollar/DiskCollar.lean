import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellDisk

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The outer collar of the characteristic m-disk is the subtype of points whose maximum norm exceeds one half.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
abbrev DiskCollar (m : ℕ) := {z : CellDisk.{u} m // (1 / 2 : ℝ) < ‖z.down.1‖}

end HolomorphicAnosov.CharacteristicCellComparison
