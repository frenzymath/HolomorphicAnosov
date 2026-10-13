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

/-- Every radial collar vector stays in the closed unit disk and has norm greater than one half throughout the closed unit time interval.

Proof: The norm formula is a convex interpolation between the initial radius r and one. Since one half is strictly below r and r is at most one, the interpolation is greater than one half and at most one. These inequalities prove the collar and disk conditions.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarRadial_mem (m : ℕ) (t : unitInterval) (z : DiskCollar.{u} m) :
    ‖collarRadial m t z‖ ≤ 1 ∧ (1 / 2 : ℝ) < ‖collarRadial m t z‖ := by
  have hr : ‖z.1.down.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.1.down.2
  have ht0 := t.2.1
  have ht1 := t.2.2
  have h0 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hr)
  have h1 := mul_nonneg ht0 (sub_nonneg.mpr hr)
  rw [collarRadial_norm]
  constructor <;> nlinarith [z.2]

end HolomorphicAnosov.CharacteristicCellComparison
