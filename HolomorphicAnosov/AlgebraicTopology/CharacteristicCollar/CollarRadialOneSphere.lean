import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadial
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadialNorm

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- At time one the radial collar formula lies on the unit sphere.

Proof: Substitute t=1 in the norm formula to get norm one, which is the sphere membership condition.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarRadial_one_sphere (m : ℕ) (z : DiskCollar.{u} m) :
    collarRadial m 1 z ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
  simp only [Metric.mem_sphere, dist_zero_right, collarRadial_norm]
  norm_num

end HolomorphicAnosov.CharacteristicCellComparison
