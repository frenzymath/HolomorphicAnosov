import HolomorphicAnosov.Analysis.Complex.QCRengelRectangleEnergy
import HolomorphicAnosov.Analysis.Complex.QCHorizontalRectangleEnergy
import HolomorphicAnosov.Analysis.Complex.HolomorphicImageArea

open Set MeasureTheory
open scoped ENNReal
open HolomorphicAnosov.Analysis.MarkedRectangle

namespace HolomorphicAnosov

/-- Rengel's two inequalities for a holomorphic rectangle whose image lies in
an ambient rectangle and whose opposite boundary sides lie in narrow strips.
Source: Lehto--Virtanen (1973), I.Lemma 4.3, p.26, equation (4.15).

Proof: injectivity and the holomorphic Jacobian formula identify squared
complex derivative energy with image area, bounded by the ambient area `M`.
Vertical endpoint separation is at least `1 - 2ε`, and horizontal separation
is at least `M - 2ε`. The vertical and horizontal rectangle energy inequalities
therefore give `a(1-2ε)² ≤ bM` and `b(M-2ε)² ≤ aM`. Divide by the positive
side lengths and separation factors. No boundary derivative is assumed. -/
theorem qc_rengel_strip_bounds {a b M ε : ℝ} {f : ℂ → ℂ}
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hεM : ε < M / 2) (hεone : ε < 1 / 2)
    (hc : ContinuousOn f (ClosedRectangle a b))
    (hf : DifferentiableOn ℂ f (OpenRectangle a b))
    (hi : InjOn f (OpenRectangle a b))
    (hmaps : MapsTo f (OpenRectangle a b) (OpenRectangle M 1))
    (hvertical : ∀ x ∈ Ioo 0 a,
      (f (x : ℂ)).im ≤ ε ∧ 1 - ε ≤ (f ((x : ℂ) + b * Complex.I)).im)
    (hhorizontal : ∀ y ∈ Ioo 0 b,
      (f (y * Complex.I)).re ≤ ε ∧ M - ε ≤ (f ((a : ℂ) + y * Complex.I)).re) :
    (M - 2 * ε) ^ 2 / M ≤ a / b ∧ a / b ≤ M / (1 - 2 * ε) ^ 2 := by
  have harea : (∫⁻ z in OpenRectangle a b, ‖deriv f z‖ₑ ^ 2) ≤ ENNReal.ofReal M := by
    have heq := Analysis.Complex.lintegral_norm_deriv_sq_eq_volume_image
      (isOpen_Ioo.reProdIm isOpen_Ioo) hf hi
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at heq
    change (∫⁻ z in OpenRectangle a b, ‖deriv f z‖ₑ ^ 2) =
      volume (f '' OpenRectangle a b) at heq
    rw [heq]
    calc
      volume (f '' OpenRectangle a b) ≤ volume (OpenRectangle M 1) :=
        measure_mono hmaps.image_subset
      _ = ENNReal.ofReal M := by
        have ht := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
          (Ioo (0 : ℝ) M ×ˢ Ioo (0 : ℝ) 1)
        change volume (OpenRectangle M 1) = volume (Ioo (0 : ℝ) M ×ˢ Ioo (0 : ℝ) 1) at ht
        rw [ht]
        change volume.prod volume (Ioo (0 : ℝ) M ×ˢ Ioo (0 : ℝ) 1) = _
        rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
        simp
  have hs : 0 < 1 - 2 * ε := by linarith
  have ht : 0 < M - 2 * ε := by linarith
  have hv := qc_rengel_rectangle_energy ha hb hs.le hc hf (fun x hx ↦ by
    have him := Complex.abs_im_le_norm
      (f ((x : ℂ) + b * Complex.I) - f (x : ℂ))
    rw [Complex.sub_im] at him
    rw [dist_comm, dist_eq_norm]
    exact (show 1 - 2 * ε ≤
      (f ((x : ℂ) + b * Complex.I)).im - (f (x : ℂ)).im by
        linarith [(hvertical x hx).1, (hvertical x hx).2]).trans
      ((le_abs_self _).trans him))
  have henergy : (∫⁻ z in OpenRectangle a b, ‖fderiv ℝ f z 1‖ₑ ^ 2) =
      ∫⁻ z in OpenRectangle a b, ‖deriv f z‖ₑ ^ 2 := by
    apply setLIntegral_congr_fun (isOpen_Ioo.reProdIm isOpen_Ioo).measurableSet
    intro z hz
    have hd := ((hf.differentiableAt
      ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv
    dsimp only
    rw [hd]
    simp
  have hh := qc_horizontal_rectangle_energy ha ht.le hc
    ((hf.contDiffOn (isOpen_Ioo.reProdIm isOpen_Ioo)).restrict_scalars ℝ)
    (fun y hy ↦ by
      have hre := Complex.abs_re_le_norm
        (f ((a : ℂ) + y * Complex.I) - f (y * Complex.I))
      rw [Complex.sub_re] at hre
      rw [dist_comm, dist_eq_norm]
      exact (show M - 2 * ε ≤
        (f ((a : ℂ) + y * Complex.I)).re - (f (y * Complex.I)).re by
          linarith [(hhorizontal y hy).1, (hhorizontal y hy).2]).trans
        ((le_abs_self _).trans hre))
  rw [henergy] at hh
  have hv' := hv.trans (mul_le_mul le_rfl harea bot_le bot_le)
  have hh' := hh.trans (mul_le_mul le_rfl harea bot_le bot_le)
  rw [← ENNReal.ofReal_mul hb.le] at hv'
  rw [← ENNReal.ofReal_mul ha.le] at hh'
  have hvR : a * (1 - 2 * ε) ^ 2 ≤ b * M :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hv'
  have hhR : b * (M - 2 * ε) ^ 2 ≤ a * M :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh'
  constructor
  · apply (div_le_div_iff₀ hM hb).2
    nlinarith [hhR]
  · apply (div_le_div_iff₀ hb (sq_pos_of_pos hs)).2
    nlinarith [hvR]


/-- The strip estimate in an ambient rectangle of arbitrary positive height.
Divide the holomorphic map by that height to apply the normalized estimate. -/
lemma qc_rengel_strip_bounds_scaled {a b A B ε : ℝ} {f : ℂ → ℂ}
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (hεA : ε < (A / B) / 2) (hεone : ε < 1 / 2)
    (hc : ContinuousOn f (ClosedRectangle a b))
    (hf : DifferentiableOn ℂ f (OpenRectangle a b))
    (hi : InjOn f (OpenRectangle a b))
    (hmaps : MapsTo f (OpenRectangle a b) (OpenRectangle A B))
    (hv : ∀ x ∈ Ioo 0 a,
      (f (x : ℂ)).im ≤ B * ε ∧ B * (1 - ε) ≤ (f ((x : ℂ) + b * Complex.I)).im)
    (hh : ∀ y ∈ Ioo 0 b,
      (f (y * Complex.I)).re ≤ B * ε ∧ A - B * ε ≤ (f ((a : ℂ) + y * Complex.I)).re) :
    (A / B - 2 * ε) ^ 2 / (A / B) ≤ a / b ∧
      a / b ≤ (A / B) / (1 - 2 * ε) ^ 2 := by
  let g : ℂ → ℂ := fun z ↦ f z / (B : ℂ)
  have hBC : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have gre (z : ℂ) : (g z).re = (f z).re / B := by simp [g, Complex.div_ofReal_re]
  have gim (z : ℂ) : (g z).im = (f z).im / B := by simp [g, Complex.div_ofReal_im]
  apply qc_rengel_strip_bounds ha hb (div_pos hA hB) hεA hεone
    (hc.div_const _) (hf.div_const _)
  · intro z hz w hw heq
    apply hi hz hw
    exact (div_left_inj' hBC).mp heq
  · intro z hz
    have h := hmaps hz
    change (0 < (g z).re ∧ (g z).re < A / B) ∧ (0 < (g z).im ∧ (g z).im < 1)
    rw [gre, gim]
    exact ⟨⟨div_pos h.1.1 hB, (div_lt_div_iff_of_pos_right hB).mpr h.1.2⟩,
      ⟨div_pos h.2.1 hB, (div_lt_one hB).mpr h.2.2⟩⟩
  · intro x hx
    rw [gim, gim]
    constructor
    · apply (div_le_iff₀ hB).mpr
      simpa only [mul_comm] using (hv x hx).1
    · apply (le_div_iff₀ hB).mpr
      simpa only [mul_comm] using (hv x hx).2
  · intro y hy
    rw [gre, gre]
    constructor
    · apply (div_le_iff₀ hB).mpr
      simpa only [mul_comm] using (hh y hy).1
    · apply (le_div_iff₀ hB).mpr
      have h := (hh y hy).2
      rw [sub_mul, div_mul_cancel₀ _ hB.ne']
      simpa only [mul_comm] using h

end HolomorphicAnosov

