import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open scoped BigOperators
noncomputable section
universe u
namespace HolomorphicAnosov

/-- The algebraic last step of the torus Lefschetz calculation: the alternating sum
of principal minors is the determinant of identity minus the matrix.

Source: step 6 of `topo.original_torus_lefschetz_determinant_g7`; the determinant
expansion is supplied by Mathlib's `Matrix.charpoly_coeff_eq_sum_minors`.
Evaluate the characteristic polynomial at one, reverse its finite coefficient
sum, and replace each coefficient by its signed principal-minor expression.
This applies to every matrix, including the empty matrix and singular matrices. -/
theorem torus_lefschetz_alternating_principal_minors (n : ℕ)
    (B : Matrix (Fin n) (Fin n) ℚ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
      ∑ S ∈ Finset.univ.powersetCard k,
        (B.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det) =
      Matrix.det (1 - B) := by
  classical
  have hcoeff : ∀ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * ∑ S ∈ Finset.univ.powersetCard k,
        (B.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det =
          B.charpoly.coeff (n - k) := by
    intro k hk
    simpa only [Fintype.card_fin] using
      (Matrix.charpoly_coeff_eq_sum_minors B k (by simpa using (Nat.le_of_lt_succ
        (Finset.mem_range.mp hk)))).symm
  rw [Finset.sum_congr rfl hcoeff]
  calc
    (∑ k ∈ Finset.range (n + 1), B.charpoly.coeff (n - k)) =
        ∑ k ∈ Finset.range (n + 1), B.charpoly.coeff k := by
      simpa using Finset.sum_range_reflect (fun k ↦ B.charpoly.coeff k) (n + 1)
    _ = B.charpoly.eval 1 := by
      simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, one_pow, mul_one]
        using (Polynomial.eval_eq_sum_range (p := B.charpoly) (1 : ℚ)).symm
    _ = Matrix.det (1 - B) := by simp [Matrix.eval_charpoly]



end HolomorphicAnosov
