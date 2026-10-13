import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import HolomorphicAnosov.Analysis.Distribution.ClassicalDbarPairing
import HolomorphicAnosov.Analysis.Distribution.RegularPairingL2Bound
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# L² control of distributional antiholomorphic derivative pairings

Source: Zhang, Lemma 4.3, printed p.16, passage from equation (31) to
Lemma 4.1. DAG node: `analysis.l2_dbar_pairing_g7`.
-/

open MeasureTheory TopologicalSpace Filter
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.DistributionalSection

/-- If the classical antiholomorphic derivative coefficients of smooth functions
have vanishing L² mass on the support of a fixed test, their distributional
antiholomorphic derivative pairings tend to zero. Integration by parts identifies
the pairings; Cauchy–Schwarz bounds them by the product of the two L² norms.
The square root of the first squared norm tends to zero and the test norm is
fixed. No integrability away from the compact support or boundary condition
on the coefficient is required. Source: Zhang Lemma 4.3, p.16, equation (31)
and its concluding distributional argument. The compact-support estimate is
supplied by the public theorem regular_pairing_l2_bound.

For every n, real smoothness on the open domain makes the classical derivative
coefficient continuous. Apply the public L² estimate to this coefficient and the
fixed test. Compose the assumed squared-integral limit with continuity of square
root and multiply by the fixed finite test norm. The resulting upper bound tends
to zero, so the norm squeeze theorem gives convergence of the regular pairings.
The public integration-by-parts theorem classical_dbar_pairing identifies each
one with the asserted distributional derivative pairing. The test support lies
inside Ω; if Ω is empty the test vanishes, and if d = 0 there is no direction j. -/
theorem l2_dbar_pairing_tendsto_zero {d : ℕ}
    (Ω : Opens (Fin d → ℂ)) (a : ℕ → (Fin d → ℂ) → ℂ)
    (ha : ∀ n, ContDiffOn ℝ ∞ (a n) Ω) (j : Fin d) (φ : TestFunction Ω ℂ ⊤)
    (hL2 : Tendsto (fun n ↦ ∫ z in tsupport φ,
      ‖(2 : ℂ)⁻¹ * (fderiv ℝ (a n) z (Pi.single j 1) +
        Complex.I * fderiv ℝ (a n) z (Pi.single j Complex.I))‖ ^ 2 ∂volume)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ dbarPairing Ω (a n) j φ) atTop (𝓝 0) := by
  let b := fun n z ↦ (2 : ℂ)⁻¹ * (fderiv ℝ (a n) z (Pi.single j 1) +
    Complex.I * fderiv ℝ (a n) z (Pi.single j Complex.I))
  have hb (n : ℕ) : ContinuousOn (b n) Ω := by
    have hD := (ha n).continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)
    exact ((hD.clm_apply continuousOn_const).add
      ((hD.clm_apply continuousOn_const).const_mul Complex.I)).const_mul _
  have hpair : Tendsto (fun n ↦ regularPairing Ω (b n) φ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ regular_pairing_l2_bound Ω (b n) (hb n) φ)
    have hs := (Real.continuous_sqrt.continuousAt.tendsto.comp hL2).mul_const
      (Real.sqrt (∫ z in tsupport φ, ‖φ z‖ ^ 2 ∂volume))
    simpa only [Real.sqrt_zero, zero_mul, Function.comp_def] using hs
  simpa only [classical_dbar_pairing Ω _ (ha _) j φ] using hpair


end HolomorphicAnosov.DistributionalSection
