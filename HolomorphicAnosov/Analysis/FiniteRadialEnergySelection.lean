import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Small radii from finite weighted radial energy

This is the radial selection step used in the finite-energy circular crosscut
argument.  It is stated for the literal ENNReal lower integral, so no
totalized real integral is substituted for a possibly infinite slice.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace HolomorphicAnosov.Analysis

/-- Finite weighted radial energy admits a radius with arbitrarily small scaled energy.

Source: Tao, *246C Notes 2*, §2, Theorem 20 proof,
`literature/Tao-246C-Notes2-2018.txt`, lines 255--265.

If every scaled energy were at least ε, multiplying by the positive finite
inverse of `ofReal r` would give `ofReal (ε / r) ≤ ofReal r * E r` throughout
`(0, δ)`, including points where `E r = ∞`. The inverse function is measurable
and nonnegative on this interval. Its finite lower integral would imply
integrability, but the power integrability criterion at exponent -1 would then
imply `-1 < -1`. Its lower integral is therefore infinite. Pulling out the
positive finite factor ε and integrating the pointwise comparison contradicts
finite weighted energy. No measurability assumption on E is needed.
-/
theorem exists_small_weighted_radius
    {E : ℝ → ℝ≥0∞} {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hfin : (∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal r * E r ∂volume) < ⊤) :
    ∃ r ∈ Ioo (0 : ℝ) δ,
      ENNReal.ofReal (r ^ 2) * E r < ENNReal.ofReal ε := by
  by_contra hn
  push Not at hn
  have hpoint : ∀ r ∈ Ioo (0 : ℝ) δ,
      ENNReal.ofReal ε ≤ ENNReal.ofReal (r ^ 2) * E r := by
    intro r hr
    exact hn r hr
  have h_inv_top :
      (∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (r⁻¹) ∂volume) = ⊤ := by
    by_contra htop
    have h_inv_ne :
        (∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (r⁻¹) ∂volume) ≠ ⊤ := htop
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) δ)] (fun r : ℝ ↦ r⁻¹) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact inv_nonneg.mpr hr.1.le
    have h_inv_int : IntegrableOn (fun r : ℝ ↦ r⁻¹) (Ioo (0 : ℝ) δ) :=
      (lintegral_ofReal_ne_top_iff_integrable
        measurable_inv.aestronglyMeasurable hnonneg).mp h_inv_ne
    have hpow : IntegrableOn (fun r : ℝ ↦ r ^ (-1 : ℝ)) (Ioo (0 : ℝ) δ) := by
      simpa only [Real.rpow_neg_one] using h_inv_int
    have hfalse : (-1 : ℝ) < -1 :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mp hpow
    exact (lt_irrefl _ hfalse)
  have h_eps_inv_top :
      (∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (ε * r⁻¹) ∂volume) = ⊤ := by
    rw [show (fun r : ℝ ↦ ENNReal.ofReal (ε * r⁻¹)) =
        (fun r : ℝ ↦ ENNReal.ofReal ε * ENNReal.ofReal (r⁻¹)) by
          funext r; rw [ENNReal.ofReal_mul (le_of_lt hε)],
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      h_inv_top]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr hε).ne'
  have h_dom : ∀ r ∈ Ioo (0 : ℝ) δ,
      ENNReal.ofReal (ε * r⁻¹) ≤ ENNReal.ofReal r * E r := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hrpow : r ^ 2 = r * r := by ring
    have h := hpoint r hr
    have hm := mul_le_mul_right h (ENNReal.ofReal r)⁻¹
    have hro : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr0).ne'
    have hrt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal (ε * r⁻¹) = (ENNReal.ofReal r)⁻¹ * ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_mul (le_of_lt hε), ENNReal.ofReal_inv_of_pos hr0]
        ring
      _ ≤ (ENNReal.ofReal r)⁻¹ * (ENNReal.ofReal (r ^ 2) * E r) := hm
      _ = ENNReal.ofReal r * E r := by
        rw [hrpow, ENNReal.ofReal_mul hr0.le]
        rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hro hrt, one_mul]
  have h_le :
      (∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (ε * r⁻¹) ∂volume) ≤
        (∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal r * E r ∂volume) :=
    setLIntegral_mono' measurableSet_Ioo h_dom
  rw [h_eps_inv_top] at h_le
  exact (not_lt_of_ge h_le) hfin

end HolomorphicAnosov.Analysis
