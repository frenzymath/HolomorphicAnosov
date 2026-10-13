import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

open Filter
open scoped Topology _root_.Topology BigOperators

namespace HolomorphicAnosov

/-- The diagonal power identity in the triangular calculation of Axler,
Linear Algebra Done Right, fourth edition, 5.81 p.179, used in Step 11(C4a).
In multiplying two upper triangular matrices, every off-diagonal intermediate
index gives zero in one factor; induction therefore gives the diagonal powers.
The statement includes exponent zero and needs no diagonalizability. -/
theorem franks_manning_triangular_pow_diag {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.BlockTriangular id) (m : ℕ) (i : Fin n) :
    (T ^ m) i i = T i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply, pow_succ]
    rw [Finset.sum_eq_single i]
    · rw [ih]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [(hT.pow m) hlt]
        simp
      · rw [hT hgt]
        simp
    · simp

/-- Manning (1974), Theorem A, pp.425–426, and the explicit triangular trace
calculation in source Step 11(C4a): a positive simple strictly dominant diagonal
occurrence gives normalized trace limit one. The same triangular matrix is used
for every power, so repeated smaller eigenvalues are retained in the finite sum.

The diagonal power identity expresses the normalized trace as the sum of powers
of diagonal-entry ratios. The distinguished ratio is one, and every other ratio
has norm less than one, hence its powers tend to zero. Passing to the finite-sum
limit gives one. Triangularization and the Perron spectral gap are hypotheses
to be supplied for the actual transition matrix, not conclusions of this lemma. -/
theorem franks_manning_triangular_trace_limit {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.BlockTriangular id)
    (i₀ : Fin n) (ρ : ℝ) (hρ : 0 < ρ) (hmain : T i₀ i₀ = (ρ : ℂ))
    (hgap : ∀ i, i ≠ i₀ → ‖T i i‖ < ρ) :
    Tendsto (fun m : ℕ ↦ Matrix.trace (T ^ m) / (ρ : ℂ) ^ m) atTop (𝓝 1) := by
  have hi (i : Fin n) : Tendsto (fun m : ℕ ↦ (T i i / (ρ : ℂ)) ^ m)
      atTop (𝓝 (if i = i₀ then 1 else 0)) := by
    by_cases he : i = i₀
    · subst i
      simp [hmain, ne_of_gt hρ]
    · have hnorm : ‖T i i / (ρ : ℂ)‖ < 1 := by
        rw [norm_div]
        simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] using
          (div_lt_one hρ).mpr (hgap i he)
      simpa only [ite_eq_right he] using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  convert tendsto_finsetSum Finset.univ (fun i _ ↦ hi i) using 1
  · ext m
    simp [Matrix.trace, Matrix.diag, franks_manning_triangular_pow_diag T hT,
      div_eq_mul_inv, Finset.sum_mul, mul_pow]
  · simp

/-- The same principal-trace limit for the original endomorphism, computed in
one triangular basis for every power. Axler, fourth edition, 3.43 p.74 and
8.49–52 pp.326–328 give the power and trace basis identities used in the parent
Step 11(C4a). The basis need not be orthogonal, and no operator norm is changed. -/
theorem franks_manning_endomorphism_trace_limit
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin n) ℂ V) (f : V →ₗ[ℂ] V)
    (hT : (LinearMap.toMatrix b b f).BlockTriangular id)
    (i₀ : Fin n) (ρ : ℝ) (hρ : 0 < ρ)
    (hmain : LinearMap.toMatrix b b f i₀ i₀ = (ρ : ℂ))
    (hgap : ∀ i, i ≠ i₀ → ‖LinearMap.toMatrix b b f i i‖ < ρ) :
    Tendsto (fun m : ℕ ↦ LinearMap.trace ℂ V (f ^ m) / (ρ : ℂ) ^ m)
      atTop (𝓝 1) := by
  simpa only [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_pow] using
    franks_manning_triangular_trace_limit (LinearMap.toMatrix b b f) hT i₀ ρ hρ hmain hgap

end HolomorphicAnosov

