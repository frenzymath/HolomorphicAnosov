import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped ContDiff

namespace HolomorphicAnosov

noncomputable section

/-- The determinant of a smooth finite matrix-valued function is smooth, including the empty matrix. -/
theorem smooth_metric_matrix_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {s : Set E} (G : E → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) s) :
    ContDiffOn ℝ ∞ (fun z ↦ (G z).det) s := by
  classical
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ ↦ contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ ↦ hG (σ i) i

end
end HolomorphicAnosov
