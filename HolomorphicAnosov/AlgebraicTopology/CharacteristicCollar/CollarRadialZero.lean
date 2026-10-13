import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadial

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- At time zero the radial collar formula is the original vector.

Proof: Substitute t=0 in the radial formula; its scalar factor is one.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarRadial_zero (m : ℕ) (z : DiskCollar.{u} m) :
    collarRadial m 0 z = z.1.down.1 := by simp [collarRadial]

end HolomorphicAnosov.CharacteristicCellComparison
