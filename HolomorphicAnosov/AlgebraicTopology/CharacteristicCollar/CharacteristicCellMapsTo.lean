import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For each m-cell of a Hausdorff CW space, its characteristic map sends the boundary of its closed disk into the lower skeleton.

Proof: A boundary point lies in the cell frontier. The native CW frontier containment places its characteristic image in the preceding skeleton.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem characteristicCell_mapsTo (m : ℕ) (i : RelCWComplex.cell (univ : Set X) m) :
    MapsTo (characteristicCell X m i) (cellBoundary m) (lowerSkeleton X m) := by
  intro z hz
  exact CWComplex.cellFrontier_subset_skeletonLT m i ⟨z.down.1, hz, rfl⟩

end HolomorphicAnosov.CharacteristicCellComparison
