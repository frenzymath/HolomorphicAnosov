import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellMapsTo
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformationOneBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformation

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- At time one the skeleton-collar deformation sends every collar point into the lower skeleton.

Proof: On the lower skeleton this is immediate. Otherwise choose its representative; the disk-collar time-one endpoint is on the disk boundary, whose characteristic image lies in the lower skeleton.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem skeletonCollarDeformation_one (m : ℕ) (x : ↥(skeletonCollar X m)) :
    skeletonCollarDeformation X m 1 x ∈ lowerSkeleton X m := by
  classical
  unfold skeletonCollarDeformation
  split_ifs with h
  · exact h
  · let z := Classical.choose (x.2.resolve_left h)
    exact characteristicCell_mapsTo X m z.1 (collarDeformation_one_boundary m z.2)

end HolomorphicAnosov.CharacteristicCellComparison
