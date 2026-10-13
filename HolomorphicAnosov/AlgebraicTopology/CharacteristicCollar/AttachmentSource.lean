import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellDisk
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For a Hausdorff CW space and degree m, the attachment source is the topological disjoint union of the lower skeleton and one characteristic m-disk per m-cell.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
abbrev AttachmentSource (m : ℕ) :=
  ↥(lowerSkeleton X m) ⊕ (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m)

end HolomorphicAnosov.CharacteristicCellComparison
