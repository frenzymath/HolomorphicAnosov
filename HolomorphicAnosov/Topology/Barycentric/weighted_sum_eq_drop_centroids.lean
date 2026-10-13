import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module
import HolomorphicAnosov.Topology.Barycentric.sum_range_smul_eq_sum_drops

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem weighted_sum_eq_drop_centroids
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (a : ℕ → ℝ) (z : ℕ → E) (n : ℕ) (hterminal : a n = 0) :
    (∑ i ∈ Finset.range n, a i • z i) =
      ∑ k ∈ Finset.range n,
        ((a k - a (k + 1)) * ((k + 1 : ℕ) : ℝ)) •
          (((k + 1 : ℕ) : ℝ)⁻¹ • ∑ j ∈ Finset.range (k + 1), z j) := by
  rw [sum_range_smul_eq_sum_drops, hterminal, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_smul]
  congr 1
  rw [mul_assoc, mul_inv_cancel₀ (by positivity : (((k + 1 : ℕ) : ℝ)) ≠ 0), mul_one]

end HolomorphicAnosov.BarycentricGeometry
