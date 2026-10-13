import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma disk_orders_finite (a b : ℂ) (r : ℝ) (f : ℂ → ℂ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a r))
    (hboundary : ∀ z ∈ Metric.sphere a r, f z ≠ b) :
    ∀ x ∈ Metric.closedBall a r, analyticOrderAt (fun z ↦ f z - b) x ≠ ⊤ := by
  let h := fun z ↦ f z - b
  have hh : AnalyticOnNhd ℂ h (Metric.closedBall a r) := hf.sub analyticOnNhd_const
  have hz : a + r ∈ Metric.sphere a r := by
    rw [Metric.mem_sphere]
    simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr]
  have hne : analyticOrderAt h (a + r) ≠ ⊤ := by
    have ho : analyticOrderAt h (a + r) = 0 :=
      (hh _ (Metric.sphere_subset_closedBall hz)).analyticOrderAt_eq_zero.mpr
        (sub_ne_zero.mpr (hboundary _ hz))
    simp [ho]
  intro x hx
  exact hh.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall a r).isPreconnected (Metric.sphere_subset_closedBall hz) hx hne


end
end HolomorphicAnosov
