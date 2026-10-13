import HolomorphicAnosov.Geometry.SmoothMetricMatrixDet
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped ContDiff Matrix

namespace HolomorphicAnosov

noncomputable section

/-- Entries of the inverse of a smooth matrix are smooth wherever its determinant is nonzero (Andrews, Prop. 10.3.1). -/
theorem smooth_metric_matrix_inverse_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {s : Set E} (G : E → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) s)
    (hdet : ∀ z ∈ s, (G z).det ≠ 0) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ ((G z)⁻¹) i j) s := by
  classical
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((smooth_metric_matrix_det G hG).inv hdet).mul ?_
  apply smooth_metric_matrix_det
  intro k l
  by_cases h : k = j
  · subst k
    simpa only [Matrix.updateRow_self] using
      (contDiffOn_const (c := ((Pi.single i (1 : ℝ)) : Fin n → ℝ) l) (s := s)
        (𝕜 := ℝ) (n := ∞))
  · simpa only [Matrix.updateRow_ne h] using hG k l

end
end HolomorphicAnosov
