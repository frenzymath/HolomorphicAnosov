import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadial
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadialMem
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.ContinuousCollarRadial

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The radial formula, with its disk and collar membership proofs, defines a continuous map from time times the disk collar to the disk collar.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def collarDeformation (m : ℕ) : C(unitInterval × DiskCollar.{u} m, DiskCollar.{u} m) where
  toFun tz := ⟨ULift.up ⟨collarRadial m tz.1 tz.2, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (collarRadial_mem m tz.1 tz.2).1⟩, (collarRadial_mem m tz.1 tz.2).2⟩
  continuous_toFun :=
    (continuous_uliftUp.comp ((continuous_collarRadial m).subtype_mk _)).subtype_mk _

end HolomorphicAnosov.CharacteristicCellComparison
