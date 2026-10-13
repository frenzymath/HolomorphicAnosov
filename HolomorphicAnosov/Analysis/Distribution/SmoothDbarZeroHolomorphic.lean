import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Distribution.SmoothDbarZeroCoordinateSlices

open MeasureTheory TopologicalSpace

namespace HolomorphicAnosov

open Set
open scoped ContDiff Topology _root_.Topology

/-- Demailly I §3.B and §3.E: a smooth scalar representative with every
coordinate antiholomorphic derivative zero is holomorphic on the same open
set. The polydisc remains inside that set; no global representative or
extension across its boundary is used. -/
theorem smooth_dbar_zero_holomorphic {n : ℕ} (hn : 1 ≤ n)
    (V : Opens (Fin n → ℂ)) (g : (Fin n → ℂ) → ℂ)
    (hg : ContDiffOn ℝ ∞ g (V : Set _))
    (hbar : ∀ j x, x ∈ V → Analysis.antiholomorphicPartial g j x = 0) :
    DifferentiableOn ℂ g (V : Set _) := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (V.isOpen.mem_nhds hx)
  let R : Fin n → ℝ := fun _ ↦ ε / 2
  have hR : ∀ j, 0 < R j := fun _ ↦ half_pos hε
  have hclosed : PolydiscBoundaryCauchySeries.closedPolydisc x R ⊆ (V : Set _) := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖z - x‖ ≤ ε / 2 :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr hz
    exact hnorm.trans_lt (half_lt_self hε)
  have han : AnalyticAt ℂ g x :=
    (PolydiscCauchy.polydisc_cauchy_power_series hn (V : Set _) V.isOpen g
      hg.continuousOn (smooth_dbar_zero_coordinate_slices V g hg hbar) x R hR
      hclosed).2.2.2.2
  exact han.differentiableWithinAt


end HolomorphicAnosov
