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
theorem sum_drop_weights
    (a : ℕ → ℝ) (n : ℕ) (hterminal : a n = 0) :
    (∑ k ∈ Finset.range n, (a k - a (k + 1)) * ((k + 1 : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range n, a k := by
  have h := sum_range_smul_eq_sum_drops a (fun _ ↦ (1 : ℝ)) n
  simpa [smul_eq_mul, hterminal] using h.symm

end HolomorphicAnosov.BarycentricGeometry
