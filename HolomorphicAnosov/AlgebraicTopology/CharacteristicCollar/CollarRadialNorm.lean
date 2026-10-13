import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadial

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The norm of the radial collar vector at time t is (1−t) times the initial norm plus t.

Proof: The initial norm r exceeds one half and t lies between zero and one. Hence the factor 1−t+t/r is nonnegative. The norm of its scalar multiple is this factor times r; multiplication by r cancels the denominator and gives (1−t)r+t.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarRadial_norm (m : ℕ) (t : unitInterval) (z : DiskCollar.{u} m) :
    ‖collarRadial m t z‖ = (1 - (t : ℝ)) * ‖z.1.down.1‖ + (t : ℝ) := by
  have hp : 0 < ‖z.1.down.1‖ := lt_trans (by norm_num) z.2
  have hc : 0 ≤ 1 - (t : ℝ) + (t : ℝ) / ‖z.1.down.1‖ :=
    add_nonneg (sub_nonneg.mpr t.2.2) (div_nonneg t.2.1 (le_of_lt hp))
  rw [collarRadial, norm_smul_of_nonneg hc, add_mul, div_mul_cancel₀ _ (ne_of_gt hp)]

end HolomorphicAnosov.CharacteristicCellComparison
