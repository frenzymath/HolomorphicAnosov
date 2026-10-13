import HolomorphicAnosov.Analysis.Complex.QCDirectionalJacobianBound
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Derivative energy bounded by image area

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973),
I.Theorem 3.1, p.18, equation (3.4). The estimate is stated on arbitrary
measurable subsets so that it applies to the actual rectangle conjugation.
-/

open Set MeasureTheory

namespace HolomorphicAnosov

/-- The horizontal derivative energy of an injective regular planar map is
at most its directional distortion bound times the area of its image.

Source: Lehto–Virtanen I.Theorem 3.1, p.18, equation (3.4).
At each point the positive determinant and the unit-direction inequality
imply `‖Df(1)‖² ≤ K det(Df)`. Integrate this inequality over the original
measurable set. Positivity identifies the determinant with its absolute value;
the injective real change-of-variables formula integrates that absolute
Jacobian to exactly the image area. Pulling the finite nonnegative constant K
outside the lower integral gives the assertion. Infinite image area, a null
or empty source, and no boundary regularity are allowed.
-/
theorem qc_regular_energy_le_image_area {S : Set ℂ} {f : ℂ → ℂ} {K : ℝ}
    (hS : MeasurableSet S) (hinj : InjOn f S) (hK : 0 ≤ K)
    (hd : ∀ z ∈ S, ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt f (A : ℂ →L[ℝ] ℂ) z ∧ 0 < (A : ℂ →L[ℝ] ℂ).det)
    (hDist : ∀ z ∈ S, ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ f z v‖ ≤ K * ‖fderiv ℝ f z w‖) :
    (∫⁻ z in S, ENNReal.ofReal (‖fderiv ℝ f z 1‖ ^ 2)) ≤
      ENNReal.ofReal K * volume (f '' S) := by
  have hpoint (z : ℂ) (hz : z ∈ S) :
      ENNReal.ofReal (‖fderiv ℝ f z 1‖ ^ 2) ≤
        ENNReal.ofReal K * ENNReal.ofReal |(fderiv ℝ f z).det| := by
    obtain ⟨A, hA, hdet⟩ := hd z hz
    have hdist := hDist z hz
    rw [hA.fderiv] at hdist ⊢
    rw [← ENNReal.ofReal_mul hK, abs_of_pos hdet]
    exact ENNReal.ofReal_le_ofReal (qc_directional_jacobian_bound A hdet hdist)
  have harea : (∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det|) ≤ volume (f '' S) := by
    apply lintegral_abs_det_fderiv_le_addHaar_image volume hS _ hinj
    intro z hz
    obtain ⟨A, hA, _⟩ := hd z hz
    rw [hA.fderiv]
    exact hA.hasFDerivWithinAt
  calc
    _ ≤ ∫⁻ z in S, ENNReal.ofReal K * ENNReal.ofReal |(fderiv ℝ f z).det| :=
      setLIntegral_mono' hS hpoint
    _ ≤ ENNReal.ofReal K * volume (f '' S) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul le_rfl harea bot_le bot_le

end HolomorphicAnosov

