import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Module
open scoped Matrix

namespace HolomorphicAnosov
noncomputable section

/-- A vector is recovered from its pairings with a finite basis by applying the inverse Gram matrix
to those pairings. (Andrews, Lecture 10, p. 98) -/
theorem metric_frame_reconstruction
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (b : Basis (Fin n) ℝ V) (v : V) :
    ∑ i : Fin n, ((Matrix.gram ℝ b)⁻¹ *ᵥ (fun j ↦ inner ℝ (b j) v)) i • b i = v := by
  have hG : Matrix.gram ℝ b *ᵥ b.repr v = fun j ↦ inner ℝ (b j) v := by
    funext j
    have h := congrArg (fun w ↦ inner ℝ (b j) w) (b.sum_repr v)
    simpa only [Matrix.mulVec, dotProduct, Matrix.gram_apply, inner_sum,
      inner_smul_right, mul_comm] using h
  have hdet := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).mpr
    b.linearIndependent
  rw [← hG, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]
  exact b.sum_repr v


end
end HolomorphicAnosov
