import HolomorphicAnosov.Analysis.DiskDerivativeRadialEnergy
import HolomorphicAnosov.Analysis.FiniteRadialEnergySelection

noncomputable section
open Set Filter MeasureTheory
open scoped Topology _root_.Topology ENNReal

namespace HolomorphicAnosov.Analysis

/-- Tao, 246C Notes 2, Theorem 20 proof, local text lines 255–265.
Restrict the finite radial integral to `(0, δ)` and apply the public divergent
inverse-integral selection theorem to the literal ENNReal angular slice. -/
theorem exists_small_disk_derivative_radius (f : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (henergy : (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖deriv f z‖ ^ 2) ∂volume) < ⊤)
    (ζ : ℂ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    let F := (Metric.ball (0 : ℂ) 1).indicator
      (fun z ↦ ENNReal.ofReal (‖deriv f z‖ ^ 2))
    ∃ r ∈ Ioo (0 : ℝ) δ,
      ENNReal.ofReal (r ^ 2) *
        (∫⁻ t in Ioo (-Real.pi) Real.pi,
          F (ζ + Complex.polarCoord.symm (r, t)) ∂volume) < ENNReal.ofReal ε := by
  let F := (Metric.ball (0 : ℂ) 1).indicator
    (fun z ↦ ENNReal.ofReal (‖deriv f z‖ ^ 2))
  exact HolomorphicAnosov.Analysis.exists_small_weighted_radius hδ hε
    ((lintegral_mono_set Ioo_subset_Ioi_self).trans_lt
      (disk_derivative_radial_energy_finite f hhol henergy ζ))


end HolomorphicAnosov.Analysis
