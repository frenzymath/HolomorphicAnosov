import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Basic.Real.Basic

/-!
Integer matrices preserve integer-coordinate vectors in real coordinate space. (Zhang, §3, p.11)
-/

namespace HolomorphicAnosov.IntegerLatticePreservation

variable {n : ℕ}

/-- The real matrix action of an integer matrix sends integer-coordinate vectors to
integer-coordinate vectors. (Zhang, §3, p.11) -/
theorem matrix_preserves_integer_coordinates (M : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℝ) (hv : ∀ i, ∃ z : ℤ, v i = (z : ℝ)) :
    ∀ i, ∃ z : ℤ, Matrix.mulVecLin (fun i j ↦ (M i j : ℝ)) v i = (z : ℝ) := by
  classical
  choose z hz using hv
  intro i
  refine ⟨∑ j, M i j * z j, ?_⟩
  change (∑ j, (M i j : ℝ) * v j) = (∑ j, M i j * z j : ℤ)
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hz, Int.cast_mul]

end HolomorphicAnosov.IntegerLatticePreservation

