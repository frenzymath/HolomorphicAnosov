import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions

import HolomorphicAnosov.Paper.HPS.LocalComponentEstimates

open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov







theorem hps_stable_graph_departure
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (T₁ : E₁ ≃L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (g : E₁ × E₂ → E₁ × E₂) (s ε : ℝ)
    (ha : ‖T₁.symm.toContinuousLinearMap‖ ≠ 0)
    (hR : ∀ z ∈ Metric.ball (0 : E₁ × E₂) s,
      ∀ z' ∈ Metric.ball (0 : E₁ × E₂) s,
      ‖(g z - (T₁ z.1, T₂ z.2)) - (g z' - (T₁ z'.1, T₂ z'.2))‖ ≤
        ε * ‖z - z'‖)
    (v : E₂ → E₁)
    (hgraph : ∀ y ∈ Metric.ball (0 : E₂) s, (v y, y) ∈ Metric.ball 0 s)
    (hLip : ∀ y ∈ Metric.ball (0 : E₂) s, ∀ y' ∈ Metric.ball (0 : E₂) s,
      ‖v y - v y'‖ ≤ ‖y - y'‖)
    (hinv : ∀ y ∈ Metric.ball (0 : E₂) s,
      g (v y, y) ∈ Metric.ball 0 s ∧ (g (v y, y)).1 = v (g (v y, y)).2)
    (z : E₁ × E₂) (hz : z ∈ Metric.ball 0 s) (hgz : g z ∈ Metric.ball 0 s) :
    (‖T₁.symm.toContinuousLinearMap‖⁻¹ - 2 * ε) * ‖z.1 - v z.2‖ ≤
      ‖(g z).1 - v (g z).2‖ := by
  have hsnd (w : E₁ × E₂) (hw : w ∈ Metric.ball (0 : E₁ × E₂) s) :
      w.2 ∈ Metric.ball (0 : E₂) s := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (norm_snd_le w).trans_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  have hy := hsnd z hz
  have hg := hinv z.2 hy
  obtain ⟨h₁, h₂⟩ := hps_local_component_estimates T₁ T₂ g s ε ha hR z
    (v z.2, z.2) hz (hgraph z.2 hy)
  have hnorm : ‖z - (v z.2, z.2)‖ = ‖z.1 - v z.2‖ := by
    simp [Prod.norm_def]
  simp only [sub_self, norm_zero, mul_zero, zero_add, hnorm] at h₁ h₂
  have hvl := hLip (g z).2 (hsnd _ hgz) (g (v z.2, z.2)).2 (hsnd _ hg.1)
  have htri : ‖(g z).1 - (g (v z.2, z.2)).1‖ ≤
      ‖(g z).1 - v (g z).2‖ + ε * ‖z.1 - v z.2‖ := by
    rw [hg.2]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (v (g z).2) _).trans
      (add_le_add_right (hvl.trans h₂) _)
  nlinarith

end HolomorphicAnosov
