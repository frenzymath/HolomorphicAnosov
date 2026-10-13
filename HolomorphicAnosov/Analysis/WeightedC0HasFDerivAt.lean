import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

open Filter _root_.Topology
open scoped ZeroAtInfty

namespace HolomorphicAnosov.Analysis

/-- The uniform first-order estimate in Wells's weighted composition proof.
Source: Wells (1976), p.288, mean-value display following equation (1).
For each positive error, the assumed uniform variation of the coordinate derivative
fields bounds the mean-value remainder on the intersection of the source ball and
a ball about each scaled coordinate. Multiplication by the output weight cancels
the inverse input weight. The supremum of the remainders is therefore bounded by
the error times the c0 increment norm, which is the Fréchet derivative criterion. -/
theorem weighted_c0_hasFDerivAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s lam : ℝ) (hlam : 1 ≤ lam) (f : E → F) (g : E → E →L[ℝ] F)
    (hfg : ∀ x ∈ Metric.ball (0 : E) s, HasFDerivAt f (g x) x)
    (C : C₀(ℕ, E) → C₀(ℕ, F))
    (hC : ∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ n : ℕ,
      C w n = (lam ^ n) • f ((lam ^ n)⁻¹ • w n))
    (w : C₀(ℕ, E)) (hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s)
    (D : C₀(ℕ, E) →L[ℝ] C₀(ℕ, F))
    (hD : ∀ v n, D v n = g ((lam ^ n)⁻¹ • w n) (v n))
    (hU : ∀ ε > 0, ∃ δ > 0, ∀ n y,
      ‖y - (lam ^ n)⁻¹ • w n‖ < δ →
      ‖g y - g ((lam ^ n)⁻¹ • w n)‖ < ε) :
    HasFDerivAt C D w := by
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hscaled_norm (z : C₀(ℕ, E)) (n : ℕ) : ‖(lam ^ n)⁻¹ • z n‖ ≤ ‖z‖ := by
    calc
      ‖(lam ^ n)⁻¹ • z n‖ = (lam ^ n)⁻¹ * ‖z n‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_pos hlam0 n).le)]
      _ ≤ 1 * ‖z n‖ := mul_le_mul_of_nonneg_right
        (inv_le_one_of_one_le₀ (one_le_pow₀ hlam)) (norm_nonneg _)
      _ ≤ ‖z‖ := by simpa using BoundedContinuousFunction.norm_coe_le_norm z.toBCF n
  have hw' : ‖w‖ < s := by simpa using hw
  have hscaled (z : C₀(ℕ, E)) (hz : ‖z‖ < s) (n : ℕ) :
      (lam ^ n)⁻¹ • z n ∈ Metric.ball (0 : E) s := by
    simpa using (hscaled_norm z n).trans_lt hz
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hU ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C₀(ℕ, E)) (lt_min hδ (sub_pos.mpr hw'))]
    with v hv
  have hv' : ‖v‖ < min δ (s - ‖w‖) := by simpa using hv
  have hvδ : ‖v‖ < δ := hv'.trans_le (min_le_left _ _)
  have hwv : ‖w + v‖ < s := (norm_add_le _ _).trans_lt
    (by linarith [hv'.trans_le (min_le_right δ (s - ‖w‖))])
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro n
  change ‖C (w + v) n - C w n - D v n‖ ≤ ε * ‖v‖
  rw [hC (w + v) (by simpa using hwv) n, hC w hw n, hD v n]
  let a : E := (lam ^ n)⁻¹ • w n
  let b : E := (lam ^ n)⁻¹ • (w + v) n
  let t : Set E := Metric.ball 0 s ∩ Metric.ball a δ
  have ha : a ∈ t := ⟨hscaled w hw' n, by simpa using hδ⟩
  have hab : b - a = (lam ^ n)⁻¹ • v n := by simp [a, b, smul_add]
  have hb : b ∈ t := ⟨hscaled (w + v) hwv n, by
    rw [Metric.mem_ball, dist_eq_norm, hab]
    exact (hscaled_norm v n).trans_lt hvδ⟩
  have hrem := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (hs := (convex_ball (0 : E) s).inter (convex_ball a δ))
    (fun x hx ↦ (hfg x hx.1).hasFDerivWithinAt)
    (fun x hx ↦ (hbound n x (by simpa [dist_eq_norm, a] using hx.2)).le) ha hb
  have hcancel : (lam ^ n) • g a (b - a) = g a (v n) := by
    rw [hab, map_smul, smul_smul, mul_inv_cancel₀ (pow_pos hlam0 n).ne', one_smul]
  calc
    ‖(lam ^ n) • f b - (lam ^ n) • f a - g a (v n)‖ =
        lam ^ n * ‖f b - f a - g a (b - a)‖ := by
      rw [← hcancel, ← smul_sub, ← smul_sub, norm_smul,
        Real.norm_of_nonneg (pow_pos hlam0 n).le]
    _ ≤ lam ^ n * (ε * ‖b - a‖) := mul_le_mul_of_nonneg_left hrem (pow_pos hlam0 n).le
    _ = ε * ‖v n‖ := by
      rw [hab, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_pos hlam0 n).le)]
      field_simp
    _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_left
      (BoundedContinuousFunction.norm_coe_le_norm v.toBCF n) hε.le

end HolomorphicAnosov.Analysis

