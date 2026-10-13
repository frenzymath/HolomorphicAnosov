import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadialZero
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The continuous disk-collar deformation is the identity at time zero.

Proof: Apply subtype extensionality and the vector identity at time zero.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarDeformation_zero (m : ℕ) (z : DiskCollar.{u} m) :
    collarDeformation m (0, z) = z := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  exact collarRadial_zero m z

end HolomorphicAnosov.CharacteristicCellComparison
