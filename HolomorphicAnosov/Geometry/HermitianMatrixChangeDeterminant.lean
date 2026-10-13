import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Complex.Basic

namespace HolomorphicAnosov

universe u

variable {d : ℕ}

/-- The determinant change law for Demailly's first-linear coefficient convention. (Demailly, VI §4.) -/
theorem hermitian_matrix_change_det (H C : Matrix (Fin d) (Fin d) ℂ) :
    (C.transpose * H * C.map (starRingEnd ℂ)).det =
      H.det * (‖C.det‖ ^ 2 : ℝ) := by
  have hc : (C.map (starRingEnd ℂ)).det = starRingEnd ℂ C.det :=
    (RingHom.map_det (starRingEnd ℂ) C).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  rw [mul_comm C.det H.det, mul_assoc, Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]


end HolomorphicAnosov
