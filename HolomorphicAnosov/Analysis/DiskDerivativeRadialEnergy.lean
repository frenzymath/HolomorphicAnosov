import HolomorphicAnosov.Analysis.TranslatedPolarEnergy
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Set Filter MeasureTheory
open scoped Topology _root_.Topology ENNReal

namespace HolomorphicAnosov.Analysis

/-- Tao, 246C Notes 2, Theorem 20 proof, local text lines 255–265.
The complex derivative is continuous in the open disk. Its squared norm has a
measurable zero extension; the translated polar identity identifies its weighted
radial integral with the given finite disk energy. -/
theorem disk_derivative_radial_energy_finite (f : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (henergy : (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖deriv f z‖ ^ 2) ∂volume) < ⊤)
    (ζ : ℂ) :
    let F := (Metric.ball (0 : ℂ) 1).indicator
      (fun z ↦ ENNReal.ofReal (‖deriv f z‖ ^ 2))
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r •
      (∫⁻ t in Ioo (-Real.pi) Real.pi,
        F (ζ + Complex.polarCoord.symm (r, t)) ∂volume) ∂volume) < ⊤ := by
  classical
  let F := (Metric.ball (0 : ℂ) 1).indicator
    (fun z ↦ ENNReal.ofReal (‖deriv f z‖ ^ 2))
  have hc : ContinuousOn (fun z ↦ ENNReal.ofReal (‖deriv f z‖ ^ 2))
      (Metric.ball (0 : ℂ) 1) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (((hhol.deriv Metric.isOpen_ball).continuousOn.norm).pow 2)
  have hF : Measurable F := by
    exact hc.measurable_piecewise continuousOn_const Metric.isOpen_ball.measurableSet
  have h := translated_polar_energy F hF ζ
  change (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r •
    (∫⁻ t in Ioo (-Real.pi) Real.pi,
      F (ζ + Complex.polarCoord.symm (r, t)) ∂volume) ∂volume) < ⊤
  rw [← h]
  simpa [F, lintegral_indicator Metric.isOpen_ball.measurableSet] using henergy


end HolomorphicAnosov.Analysis
