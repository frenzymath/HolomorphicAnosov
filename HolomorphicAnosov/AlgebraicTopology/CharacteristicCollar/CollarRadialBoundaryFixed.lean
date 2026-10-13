import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadial

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- At every time the radial collar formula fixes each point of norm one.

Proof: For a boundary point the norm is one. Substitute that value into the scalar factor, which simplifies to one for every time.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarRadial_boundary_fixed (m : ℕ) (t : unitInterval) (z : DiskCollar.{u} m)
    (hz : z.1 ∈ cellBoundary m) : collarRadial m t z = z.1.down.1 := by
  have hn : ‖z.1.down.1‖ = 1 := by
    simpa only [cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using hz
  simp [collarRadial, hn]

end HolomorphicAnosov.CharacteristicCellComparison
