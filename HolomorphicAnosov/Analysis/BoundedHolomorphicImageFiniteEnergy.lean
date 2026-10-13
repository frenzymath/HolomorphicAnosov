import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Finite Dirichlet energy from a bounded injective holomorphic image

The argument is the change-of-variables step in Terence Tao, *246C Notes 2: Circle packings,
conformal maps, and quasiconformal maps* (12 April 2018), §2, Theorem 20 proof,
`literature/Tao-246C-Notes2-2018.txt`, lines 255--265. Tao identifies the area of a bounded
holomorphic image with the integral of the squared complex derivative. The implementation uses
Mathlib's `MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image` for the needed direction of the
injective real area formula and `LinearMap.det_restrictScalars` for the determinant of complex
multiplication.

This helper supplies the finite-energy premise used by
`HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCrosscuts.exists_short_crosscuts` whenever its
holomorphic disk map is presented by `Set.BijOn` onto a bounded target. It assumes only openness
of the source, complex differentiability there, injectivity onto the target, and boundedness of
the target image. The lower integral is the canonical complex Lebesgue lower integral.
-/

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/--
For an injective holomorphic map on an open complex set, boundedness of the image implies finite
Dirichlet energy. This is the change-of-variables/area step in Tao, *246C Notes 2*, §2,
Theorem 20 proof, lines 255--265. Mathlib's injective real Jacobian inequality bounds the
integral of the absolute real determinant by the area of the image; the determinant of the
real restriction of multiplication by `φ' z` is `‖φ' z‖²`.
-/
theorem finite_energy_of_bijOn_bounded
    {D Q : Set ℂ} {φ : ℂ → ℂ}
    (hD : IsOpen D) (hhol : DifferentiableOn ℂ φ D)
    (hbij : BijOn φ D Q) (hQ : Bornology.IsBounded Q) :
    (∫⁻ z in D, ENNReal.ofReal (‖deriv φ z‖ ^ 2) ∂volume) < ⊤ := by
  let f' : ℂ → (ℂ →L[ℝ] ℂ) := fun z ↦
    (deriv φ z • (1 : ℂ →L[ℂ] ℂ)).restrictScalars ℝ
  have harea :
      (∫⁻ z in D, ENNReal.ofReal |(f' z).det| ∂volume) ≤ volume (φ '' D) := by
    apply lintegral_abs_det_fderiv_le_addHaar_image volume hD.measurableSet
      (fun z hz ↦ ?_) hbij.injOn
    have hd := (hhol.differentiableAt (hD.mem_nhds hz)).hasDerivAt
    convert (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt using 1
    ext w
    simp [f', mul_comm]
  calc
    (∫⁻ z in D, ENNReal.ofReal (‖deriv φ z‖ ^ 2) ∂volume) =
        ∫⁻ z in D, ENNReal.ofReal |(f' z).det| ∂volume := by
      apply setLIntegral_congr_fun hD.measurableSet
      intro z hz
      change ENNReal.ofReal (‖deriv φ z‖ ^ 2) =
        ENNReal.ofReal |((deriv φ z • (1 : ℂ →L[ℂ] ℂ)).restrictScalars ℝ).det|
      change ENNReal.ofReal (‖deriv φ z‖ ^ 2) =
        ENNReal.ofReal |LinearMap.det ((deriv φ z • (1 : ℂ →ₗ[ℂ] ℂ)).restrictScalars ℝ)|
      rw [LinearMap.det_restrictScalars]
      simp [Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq,
        abs_of_nonneg (sq_nonneg (‖deriv φ z‖))]
    _ ≤ volume (φ '' D) := harea
    _ = volume Q := by rw [hbij.image_eq]
    _ < ⊤ := hQ.measure_lt_top

end HolomorphicAnosov.Analysis

