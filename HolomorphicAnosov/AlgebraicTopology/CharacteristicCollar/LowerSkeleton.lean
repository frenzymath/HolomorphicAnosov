import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- Inside the degree-m skeleton of a Hausdorff CW space, the lower skeleton is the subset belonging to the native cells of dimension less than m.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def lowerSkeleton (m : ℕ) : Set (Skeleton X m) :=
  {z | z.1 ∈ (CWComplex.skeletonLT (univ : Set X) m : Set X)}

end HolomorphicAnosov.CharacteristicCellComparison
