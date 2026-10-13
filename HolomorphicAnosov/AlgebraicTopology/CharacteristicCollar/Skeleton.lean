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

/-- For a Hausdorff CW space X, its degree-m skeleton has the original subtype topology on the native skeleton of cells of dimension less than m+1.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
abbrev Skeleton (m : ℕ) := ↥(CWComplex.skeletonLT (univ : Set X) (m + 1) : Set X)

end HolomorphicAnosov.CharacteristicCellComparison
