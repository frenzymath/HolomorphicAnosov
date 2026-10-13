import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Determinant
import HolomorphicAnosov.Analysis.Complex.QCRealLinearDeterminant

namespace HolomorphicAnosov

/-- For a real-linear map on `ℂ`, the oriented area of `A 1` and `A v` is scaled by its determinant. -/
theorem qc_real_linear_area (A : ℂ →L[ℝ] ℂ) (v : ℂ) :
    (starRingEnd ℂ (A 1) * A v).im = A.det * v.im := by
  have hv : A v = v.re • A 1 + v.im • A Complex.I := by
    conv_lhs => rw [← Complex.re_add_im v]
    simp only [Complex.real_smul, map_add, ← map_smul, mul_one]
  rw [hv, qc_real_linear_determinant]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

end HolomorphicAnosov
