import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DescendedCollar

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The skeleton-collar deformation is the identity on the lower skeleton and the descended radial formula on the other collar points.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def skeletonCollarDeformation (m : ℕ) (t : unitInterval)
    (x : ↥(skeletonCollar X m)) : Skeleton X m := by
  classical
  exact if h : x.1 ∈ lowerSkeleton X m then x.1
    else descendedCollar X m t ⟨x.1, x.2.resolve_left h⟩

end HolomorphicAnosov.CharacteristicCellComparison
