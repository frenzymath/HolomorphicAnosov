import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Derivative lower bound from a local inverse Lipschitz estimate

This is the elementary J2 inverse audit used by the Journé provider.  A local
anti-Lipschitz estimate for `f` at `x`, together with a Fréchet derivative,
passes to the derivative by the real scaled difference quotient.  The result
is independent of the Journé data and is suitable for any finite-dimensional
inverse-chart argument.
-/

noncomputable section
namespace HolomorphicAnosov
open Filter
open scoped Topology _root_.Topology

/-- A local anti-Lipschitz estimate bounds the derivative from below.

The proof uses Mathlib's `HasFDerivAt.lim_real`: along
`x + c⁻¹ • v`, multiply the anti-Lipschitz inequality by positive `c` and
pass to the limit.  The hypothesis is only required eventually in the
neighborhood filter at `x`; no inverse map or differentiability of that
inverse is assumed.
-/
theorem hasFDerivAt_norm_lower_of_eventually_antiLipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {x : E} {K : ℝ}
    (hf : HasFDerivAt f f' x)
    (hanti : ∀ᶠ y in 𝓝 x, ‖y - x‖ ≤ K * ‖f y - f x‖) :
    ∀ v, ‖v‖ ≤ K * ‖f' v‖ := by
  intro v
  have hpath : Tendsto (fun c : ℝ ↦ x + c⁻¹ • v) atTop (𝓝 x) := by
    have hi : Tendsto (fun c : ℝ ↦ c⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa only [zero_smul, add_zero] using
      ((tendsto_const_nhds (x := x)).add (hi.smul_const v))
  have he : ∀ᶠ c : ℝ in atTop,
      ‖x + c⁻¹ • v - x‖ ≤ K * ‖f (x + c⁻¹ • v) - f x‖ :=
    hpath.eventually hanti
  have he' : ∀ᶠ c : ℝ in atTop, 0 ≤ c ∧
      ‖v‖ ≤ K * ‖c • (f (x + c⁻¹ • v) - f x)‖ := by
    filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with c hc hc0
    have hcne : c ≠ 0 := ne_of_gt hc0
    have hcscale : c * ‖c⁻¹ • v‖ = ‖v‖ := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc0]
      field_simp
    have hm := mul_le_mul_of_nonneg_left hc (le_of_lt hc0)
    have harg : x + c⁻¹ • v - x = c⁻¹ • v := by abel
    rw [harg, hcscale] at hm
    refine ⟨le_of_lt hc0, ?_⟩
    calc
      ‖v‖ ≤ c * (K * ‖f (x + c⁻¹ • v) - f x‖) := hm
      _ = K * ‖c • (f (x + c⁻¹ • v) - f x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
        ring
  have hleft : Tendsto (fun _ : ℝ ↦ ‖v‖) atTop (𝓝 ‖v‖) := tendsto_const_nhds
  have hright : Tendsto (fun c : ℝ ↦ K * ‖c • (f (x + c⁻¹ • v) - f x)‖)
      atTop (𝓝 (K * ‖f' v‖)) := by
    simpa only [norm_smul, abs_of_nonneg] using
      (hf.lim_real v).norm.const_mul K
  exact le_of_tendsto_of_tendsto hleft hright (he'.mono fun c hc ↦ hc.2)


end HolomorphicAnosov
