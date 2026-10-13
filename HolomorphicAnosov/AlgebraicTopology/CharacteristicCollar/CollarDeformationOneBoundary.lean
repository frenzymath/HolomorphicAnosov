import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadialOneSphere
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The continuous disk-collar deformation sends every point to the disk boundary at time one.

Proof: The underlying radial vector has norm one at time one; this is exactly the defining boundary condition.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarDeformation_one_boundary (m : ℕ) (z : DiskCollar.{u} m) :
    (collarDeformation m (1, z)).1 ∈ cellBoundary m :=
  collarRadial_one_sphere m z

end HolomorphicAnosov.CharacteristicCellComparison
