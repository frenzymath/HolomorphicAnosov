import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Area of an injective holomorphic image

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed p.342, the change-of-variables equality for the
Jacobian in the length–area chain. The complex-derivative formulation also
appears in Tao, *246C Notes 2: Circle packings, conformal maps, and
quasiconformal maps*, §2, Theorem 20 proof, local text lines 255–256.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace HolomorphicAnosov.Analysis.Complex

/-- The area of an injective holomorphic image equals the lower integral of the
squared complex derivative norm. The equality allows infinite area.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, printed p.342;
Tao, *246C Notes 2*, §2, Theorem 20 proof, text lines 255–256.

Proof: At every point of the open domain, complex differentiability gives a real
Fréchet derivative by restricting scalars. This real derivative is multiplication
by the complex derivative. Its real determinant is the complex algebra norm of
that scalar, hence its squared complex norm; it is nonnegative. Apply the real
injective change-of-variables theorem for lower integrals to the constant density
one on the measurable open domain. Its image integral is precisely the volume
of the image, and its source integral is the squared derivative norm integral.
No boundary regularity, nonvanishing derivative or finite-area premise is needed.
-/
theorem lintegral_norm_deriv_sq_eq_volume_image {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    (∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ 2) ∂volume) = volume (f '' U) := by
  let f' : ℂ → (ℂ →L[ℝ] ℂ) := fun z ↦
    (deriv f z • (1 : ℂ →L[ℂ] ℂ)).restrictScalars ℝ
  have hd (z : ℂ) (hz : z ∈ U) : HasFDerivWithinAt f (f' z) U z := by
    have hzderiv := (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    convert (hzderiv.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt using 1
    ext w
    simp [f', mul_comm]
  have harea := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    hU.measurableSet hd hi (fun _ ↦ (1 : ℝ≥0∞))
  calc
    (∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ 2) ∂volume) =
        ∫⁻ z in U, ENNReal.ofReal |(f' z).det| ∂volume := by
      apply setLIntegral_congr_fun hU.measurableSet
      intro z hz
      change ENNReal.ofReal (‖deriv f z‖ ^ 2) =
        ENNReal.ofReal |LinearMap.det ((deriv f z • (1 : ℂ →ₗ[ℂ] ℂ)).restrictScalars ℝ)|
      rw [LinearMap.det_restrictScalars]
      simp [Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq,
        abs_of_nonneg (sq_nonneg (‖deriv f z‖))]
    _ = volume (f '' U) := by simpa using harea.symm

end HolomorphicAnosov.Analysis.Complex

