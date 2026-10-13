import Mathlib.Analysis.Normed.Module.Basic

namespace HolomorphicAnosov

open Set

/-- Normalizing after a linear norm change and then normalizing back fixes unit vectors.
Source: the explicit radial inverse in `topo.unit_sphere_simply_connected_g9`.
Linearity moves the positive first normalization factor through the inverse map;
the source unit norm then makes the second normalization factor its reciprocal. -/
theorem unit_sphere_normalize_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (v : E) (hv : ‖v‖ = 1) :
    ‖e.symm (‖e v‖⁻¹ • e v)‖⁻¹ • e.symm (‖e v‖⁻¹ • e v) = v := by
  have hv₀ : v ≠ 0 := by
    intro h
    simp [h] at hv
  have he₀ : ‖e v‖ ≠ 0 := norm_ne_zero_iff.mpr (e.map_ne_zero_iff.mpr hv₀)
  rw [map_smul, e.symm_apply_apply, norm_smul, norm_inv, norm_norm, hv, mul_one,
    inv_inv, smul_smul, mul_inv_cancel₀ he₀, one_smul]

end HolomorphicAnosov

