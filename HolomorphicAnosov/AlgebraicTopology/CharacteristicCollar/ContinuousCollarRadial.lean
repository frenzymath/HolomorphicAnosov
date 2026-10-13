import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadial

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The radial collar formula is jointly continuous in time and in the disk-collar point.

Proof: The collar radius is a continuous norm of the vector projection and never zero because it exceeds one half. Division by it is continuous. Sums, products and scalar multiplication preserve continuity, yielding the joint formula.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem continuous_collarRadial (m : ℕ) :
    Continuous (fun tz : unitInterval × DiskCollar.{u} m ↦ collarRadial m tz.1 tz.2) := by
  have ht : Continuous (fun tz : unitInterval × DiskCollar.{u} m ↦ (tz.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun tz : unitInterval × DiskCollar.{u} m ↦ tz.2.1.down.1) :=
    continuous_subtype_val.comp
      (continuous_uliftDown.comp (continuous_subtype_val.comp continuous_snd))
  have hn := hx.norm
  have hne (tz : unitInterval × DiskCollar.{u} m) : ‖tz.2.1.down.1‖ ≠ 0 := by
    have hp : 0 < ‖tz.2.1.down.1‖ := lt_trans (by norm_num) tz.2.2
    exact ne_of_gt hp
  exact ((continuous_const.sub ht).add (ht.div hn hne)).smul hx

end HolomorphicAnosov.CharacteristicCellComparison
