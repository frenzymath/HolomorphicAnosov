import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

open Filter _root_.Topology
open scoped ZeroAtInfty BoundedContinuousFunction

namespace HolomorphicAnosov.Analysis

/-- The first-order superposition estimate with bounded-sequence codomain.
Source: Wells (1976), p.288, mean-value display, with weight one. On each coordinate,
apply the convex mean-value estimate on the intersection of the source ball with
its uniform derivative-variation neighborhood. Taking the supremum bounds the
remainder by `ε * ‖v‖`; the little-o criterion gives the derivative. The bounded
codomain allows nonzero limiting derivative coefficients. -/
theorem bounded_c0_hasFDerivAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ℝ) (f : E → F) (g : E → E →L[ℝ] F)
    (hfg : ∀ x ∈ Metric.ball (0 : E) s, HasFDerivAt f (g x) x)
    (C : C₀(ℕ, E) → (ℕ →ᵇ F))
    (hC : ∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ n : ℕ, C w n = f (w n))
    (w : C₀(ℕ, E)) (hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s)
    (D : C₀(ℕ, E) →L[ℝ] (ℕ →ᵇ F))
    (hD : ∀ v n, D v n = g (w n) (v n))
    (hU : ∀ ε > 0, ∃ δ > 0, ∀ n y, ‖y - w n‖ < δ → ‖g y - g (w n)‖ < ε) :
    HasFDerivAt C D w := by
  have hcoord (z : C₀(ℕ, E)) (n : ℕ) : ‖z n‖ ≤ ‖z‖ :=
    BoundedContinuousFunction.norm_coe_le_norm z.toBCF n
  have hw' : ‖w‖ < s := by simpa using hw
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hU ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C₀(ℕ, E)) (lt_min hδ (sub_pos.mpr hw'))]
    with v hv
  have hv' : ‖v‖ < min δ (s - ‖w‖) := by simpa using hv
  have hvδ : ‖v‖ < δ := hv'.trans_le (min_le_left _ _)
  have hwv : ‖w + v‖ < s := (norm_add_le _ _).trans_lt
    (by linarith [hv'.trans_le (min_le_right δ (s - ‖w‖))])
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro n
  change ‖C (w + v) n - C w n - D v n‖ ≤ ε * ‖v‖
  rw [hC (w + v) (by simpa using hwv) n, hC w hw n, hD v n]
  let t : Set E := Metric.ball 0 s ∩ Metric.ball (w n) δ
  have ha : w n ∈ t := ⟨by simpa using (hcoord w n).trans_lt hw', by simpa using hδ⟩
  have hb : (w + v) n ∈ t := ⟨by simpa using (hcoord (w + v) n).trans_lt hwv, by
    simpa [dist_eq_norm] using (hcoord v n).trans_lt hvδ⟩
  have hrem := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (hs := (convex_ball (0 : E) s).inter (convex_ball (w n) δ))
    (fun x hx ↦ (hfg x hx.1).hasFDerivWithinAt)
    (fun x hx ↦ (hbound n x (by simpa [dist_eq_norm] using hx.2)).le) ha hb
  have : ‖f ((w + v) n) - f (w n) - g (w n) (v n)‖ ≤ ε * ‖v n‖ := by
    simpa using hrem
  exact this.trans (mul_le_mul_of_nonneg_left (hcoord v n) hε.le)

end HolomorphicAnosov.Analysis

