import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Connected.Basic

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_analyticOnNhd {d : ℕ} (hd : 1 ≤ d)
    {U : Set (Fin d → ℂ)} {a : (Fin d → ℂ) → ℂ}
    (hU : IsOpen U) (ha : DifferentiableOn ℂ a U) : AnalyticOnNhd ℂ a U := by
  intro p hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  let R : Fin d → ℝ := fun _ ↦ ε / 2
  have hR : ∀ i, 0 < R i := fun _ ↦ half_pos hε
  have hclosed : HolomorphicAnosov.PolydiscBoundaryCauchySeries.closedPolydisc p R ⊆ U := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    apply (pi_norm_lt_iff hε).mpr
    intro j
    have hj : ‖z j - p j‖ ≤ ε / 2 := hz j
    exact lt_of_le_of_lt hj (by linarith)
  have hsep : ∀ (z : Fin d → ℂ) (j : Fin d),
      DifferentiableOn ℂ (fun t : ℂ ↦ a (Function.update z j t))
        ((fun t : ℂ ↦ Function.update z j t) ⁻¹' U) := by
    intro z j t ht
    exact (ha.differentiableAt (hU.mem_nhds ht)).comp t
      (hasFDerivAt_update (𝕜 := ℂ) z t).differentiableAt |>.differentiableWithinAt
  exact (HolomorphicAnosov.PolydiscCauchy.polydisc_cauchy_power_series hd U hU a
    ha.continuousOn hsep p R hR hclosed).2.2.2.2

end HolomorphicAnosov.Analysis
