import HolomorphicAnosov.Analysis.Complex.QCRegularEnergyArea
import HolomorphicAnosov.Analysis.Complex.QCHorizontalRectangleEnergy

/-! # Grötzsch's inequality for regular rectangle maps

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973),
I.Theorem 3.1, pp.18–19, equations (3.3)–(3.4).
-/

open Set MeasureTheory
open HolomorphicAnosov.Analysis.MarkedRectangle

namespace HolomorphicAnosov

/-- A regular injective map between positive rectangles, whose horizontal endpoints
are separated by the target width, distorts width/height by at most its directional
distortion bound.

Source: Lehto–Virtanen I.Theorem 3.1, pp.18–19. The Jacobian inequality and change
of variables bound horizontal energy by K times the target area. The continuous
horizontal slices and Schwarz inequality bound the same energy below by source
height times target width squared divided by source width. Compute the rectangle
area, pass the resulting finite extended-real inequality to real numbers, and cancel
the positive target width. No derivative on the boundary is required.
-/
theorem qc_regular_rectangle_distortion {a b A B K : ℝ} {f : ℂ → ℂ}
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B) (hK : 0 ≤ K)
    (hc : ContinuousOn f (ClosedRectangle a b))
    (hf : ContDiffOn ℝ 1 f (OpenRectangle a b))
    (hbij : BijOn f (OpenRectangle a b) (OpenRectangle A B))
    (hd : ∀ z ∈ OpenRectangle a b, ∃ L : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt f (L : ℂ →L[ℝ] ℂ) z ∧ 0 < (L : ℂ →L[ℝ] ℂ).det)
    (hDist : ∀ z ∈ OpenRectangle a b, ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ f z v‖ ≤ K * ‖fderiv ℝ f z w‖)
    (hsep : ∀ y ∈ Ioo 0 b,
      A ≤ dist (f (y * Complex.I)) (f ((a : ℂ) + y * Complex.I))) :
    A / B ≤ K * (a / b) := by
  have hlow := qc_horizontal_rectangle_energy ha hA.le hc hf hsep
  have hhigh := qc_regular_energy_le_image_area (S := OpenRectangle a b)
    (isOpen_Ioo.reProdIm isOpen_Ioo).measurableSet hbij.injOn hK hd hDist
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at hhigh
  have harea : volume (OpenRectangle A B) = ENNReal.ofReal (A * B) := by
    have ht := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
      (Ioo (0 : ℝ) A ×ˢ Ioo (0 : ℝ) B)
    change volume (OpenRectangle A B) = volume (Ioo (0 : ℝ) A ×ˢ Ioo (0 : ℝ) B) at ht
    rw [ht]
    change volume.prod volume (Ioo (0 : ℝ) A ×ˢ Ioo (0 : ℝ) B) = _
    rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    simp only [sub_zero, ENNReal.ofReal_mul hA.le]
  rw [hbij.image_eq, harea] at hhigh
  have he := hlow.trans (mul_le_mul le_rfl hhigh bot_le bot_le)
  rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul ha.le] at he
  have hr : b * A ^ 2 ≤ a * (K * (A * B)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  apply (div_le_iff₀ hB).2
  have hm : A * b ≤ K * a * B := by nlinarith [hA]
  calc
    A ≤ (K * a * B) / b := (le_div_iff₀ hb).2 (by nlinarith [hm])
    _ = K * (a / b) * B := by ring

end HolomorphicAnosov

