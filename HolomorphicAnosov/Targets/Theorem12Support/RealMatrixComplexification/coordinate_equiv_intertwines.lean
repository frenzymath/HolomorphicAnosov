import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Basic

/-!
The tensor-coordinate equivalence identifies the complexification of a real matrix action with its entrywise complex cast. (Zhang, Theorem 1.2, §3, p.11)
-/

open TensorProduct

namespace HolomorphicAnosov.Theorem12MatrixScratch

/-- The canonical tensor-coordinate equivalence intertwines the complexification of a real matrix
action with the action of its entrywise complex cast. (Zhang, Theorem 1.2, §3, p.11) -/
theorem coordinate_equiv_intertwines {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (w : ℂ ⊗[ℝ] (Fin n → ℝ)) :
    TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n)
        ((Matrix.mulVecLin M).baseChange ℂ w) =
      Matrix.mulVecLin (fun i j ↦ (M i j : ℂ))
        (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z x =>
    simp only [LinearMap.baseChange_tmul, Matrix.mulVecLin_apply]
    ext i
    change ((∑ j, M i j * x j : ℝ) : ℂ) * z =
      ∑ j, (M i j : ℂ) * ((x j : ℂ) * z)
    simp [Finset.sum_mul, mul_assoc]
  | add w v hw hv => simp only [map_add, hw, hv]

end HolomorphicAnosov.Theorem12MatrixScratch
