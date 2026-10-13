import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- At time t in the closed unit interval, the radial collar formula sends a vector z of norm r greater than one half to (1−t+t/r)z.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def collarRadial (m : ℕ) (t : unitInterval) (z : DiskCollar.{u} m) : Fin m → ℝ :=
  (1 - (t : ℝ) + (t : ℝ) / ‖z.1.down.1‖) • z.1.down.1

end HolomorphicAnosov.CharacteristicCellComparison
