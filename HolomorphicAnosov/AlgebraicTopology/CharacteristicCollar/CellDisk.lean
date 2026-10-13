import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The characteristic m-disk is the universe-lifted closed unit ball of the real m-coordinate maximum-norm space, with its original subtype topology.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
abbrev CellDisk (m : ℕ) := ULift.{u} ↥(Metric.closedBall (0 : Fin m → ℝ) 1)

end HolomorphicAnosov.CharacteristicCellComparison
