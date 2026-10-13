import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Determinant

namespace HolomorphicAnosov

/-- The real determinant of a continuous real-linear map on `ℂ`, in the basis `(1,I)`. -/
theorem qc_real_linear_determinant (A : ℂ →L[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  change LinearMap.det A.toLinearMap = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI A.toLinearMap, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

end HolomorphicAnosov
