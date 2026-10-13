import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Cancellation of inverse derivative weights on a holomorphic branch

Source: Mathlib's injective lower-integral change-of-variables theorem,
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, specialized to a holomorphic
branch and its reciprocal squared derivative density. This is the local
Jacobian cancellation in step 6 of the current Ghys Proposition 4.1 proof.
DAG node: `analysis.holomorphic_inverse_weighted_area_g6`.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HolomorphicAnosov.Analysis.Complex

/-- A nonnegative source weight transported by an injective holomorphic branch
and divided by its squared derivative norm has exactly the original integral.
The inverse need only be a left inverse on the measurable source piece.

Proof: Complex differentiability on the open ambient domain gives the real
within derivative on the measurable piece by restricting scalars. Its real
determinant is the squared complex derivative norm. Apply Mathlib's injective
change-of-variables theorem to the displayed target density. The left inverse
identity evaluates that density at the original source point. The nonzero
complex derivative makes its squared norm strictly positive and finite, so the
Jacobian cancels its reciprocal, including when the source weight is infinite.
No smooth boundary, finite area, measurability of the arbitrary weight or
regularity of the inverse away from the image is needed for lower integrals.

Source: `Mathlib/MeasureTheory/Function/Jacobian.lean`,
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`; the complex determinant
identity uses `LinearMap.det_restrictScalars` and `Algebra.norm_complex_eq`.
This is the analytic specialization used by the agent-written direct-n proof
of Ghys Proposition 4.1; it does not assert existence of its dynamical branches.
-/
theorem lintegral_image_inverse_deriv_weight
    {U S : Set ℂ} {f h : ℂ → ℂ}
    (hU : IsOpen U) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (hleft : ∀ z ∈ S, h (f z) = z) (hnz : ∀ z ∈ S, deriv f z ≠ 0)
    (w : ℂ → ℝ≥0∞) :
    (∫⁻ y in f '' S, w (h y) / ENNReal.ofReal (‖deriv f (h y)‖ ^ 2) ∂volume) =
      ∫⁻ z in S, w z ∂volume := by
  let f' : ℂ → (ℂ →L[ℝ] ℂ) := fun z ↦
    (deriv f z • (1 : ℂ →L[ℂ] ℂ)).restrictScalars ℝ
  have hd (z : ℂ) (hz : z ∈ S) : HasFDerivWithinAt f (f' z) S z := by
    have hzderiv := (hf.differentiableAt (hU.mem_nhds (hSU hz))).hasDerivAt
    convert (hzderiv.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt using 1
    ext v
    simp [f', mul_comm]
  have hi : InjOn f S := by
    intro z hz z' hz' he
    rw [← hleft z hz, ← hleft z' hz', he]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hd hi]
  apply setLIntegral_congr_fun hS
  intro z hz
  dsimp only
  rw [hleft z hz]
  have hdet : |(f' z).det| = ‖deriv f z‖ ^ 2 := by
    change |LinearMap.det ((deriv f z • (1 : ℂ →ₗ[ℂ] ℂ)).restrictScalars ℝ)| = _
    rw [LinearMap.det_restrictScalars]
    simp [Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq,
      abs_of_nonneg (sq_nonneg (‖deriv f z‖))]
  rw [hdet]
  exact ENNReal.mul_div_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr
    (sq_pos_of_pos (norm_pos_iff.mpr (hnz z hz))))) ENNReal.ofReal_ne_top

end HolomorphicAnosov.Analysis.Complex

