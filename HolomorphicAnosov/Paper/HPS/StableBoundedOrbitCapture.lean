import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions

import HolomorphicAnosov.Paper.HPS.StableGraphDeparture
import HolomorphicAnosov.Paper.HPS.NormalizedGrowthVanishes

open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov








theorem hps_stable_bounded_orbit_capture
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (T₁ : E₁ ≃L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (g : E₁ × E₂ → E₁ × E₂) (s ε ρ : ℝ) (hs : 0 < s) (hρ : 0 < ρ)
    (ha : ‖T₁.symm.toContinuousLinearMap‖ ≠ 0)
    (hgap : ρ < ‖T₁.symm.toContinuousLinearMap‖⁻¹ - 2 * ε)
    (hR : ∀ z ∈ Metric.ball (0 : E₁ × E₂) s,
      ∀ z' ∈ Metric.ball (0 : E₁ × E₂) s,
      ‖(g z - (T₁ z.1, T₂ z.2)) - (g z' - (T₁ z'.1, T₂ z'.2))‖ ≤
        ε * ‖z - z'‖)
    (v : E₂ → E₁) (hvzero : v 0 = 0)
    (hgraph : ∀ y ∈ Metric.ball (0 : E₂) s, (v y, y) ∈ Metric.ball 0 s)
    (hLip : ∀ y ∈ Metric.ball (0 : E₂) s, ∀ y' ∈ Metric.ball (0 : E₂) s,
      ‖v y - v y'‖ ≤ ‖y - y'‖)
    (hinv : ∀ y ∈ Metric.ball (0 : E₂) s,
      g (v y, y) ∈ Metric.ball 0 s ∧ (g (v y, y)).1 = v (g (v y, y)).2)
    (w : ℕ → E₁ × E₂) (hmem : ∀ n, w n ∈ Metric.ball 0 s)
    (horbit : ∀ n, g (w n) = w (n + 1))
    (M : ℝ) (hbound : ∀ n, ‖w n‖ / ρ ^ n ≤ M) : (w 0).1 = v (w 0).2 := by
  have hstep (n : ℕ) :
      (‖T₁.symm.toContinuousLinearMap‖⁻¹ - 2 * ε) * ‖(w n).1 - v (w n).2‖ ≤
        ‖(w (n + 1)).1 - v (w (n + 1)).2‖ := by
    have h := hps_stable_graph_departure T₁ T₂ g s ε ha hR v hgraph hLip hinv
      (w n) (hmem n) (by rw [horbit]; exact hmem (n + 1))
    simpa only [horbit] using h
  have hcompare (n : ℕ) : ‖(w n).1 - v (w n).2‖ ≤ 2 * ‖w n‖ := by
    have hy : (w n).2 ∈ Metric.ball (0 : E₂) s := by
      exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using
        (norm_snd_le (w n)).trans_lt (by simpa using hmem n))
    have hv : ‖v (w n).2‖ ≤ ‖(w n).2‖ := by
      simpa only [hvzero, sub_zero] using hLip (w n).2 hy 0 (by simpa using hs)
    calc
      ‖(w n).1 - v (w n).2‖ ≤ ‖(w n).1‖ + ‖v (w n).2‖ := norm_sub_le _ _
      _ ≤ ‖w n‖ + ‖w n‖ := add_le_add (norm_fst_le _) (hv.trans (norm_snd_le _))
      _ = 2 * ‖w n‖ := by ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (hps_normalized_growth_vanishes
    (fun n ↦ ‖(w n).1 - v (w n).2‖) (fun n ↦ ‖w n‖)
    (‖T₁.symm.toContinuousLinearMap‖⁻¹ - 2 * ε) ρ 2 M hρ hgap (by norm_num)
    (norm_nonneg _) hstep hcompare hbound))

end HolomorphicAnosov
