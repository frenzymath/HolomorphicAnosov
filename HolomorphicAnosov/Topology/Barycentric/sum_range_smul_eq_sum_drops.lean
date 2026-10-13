import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem sum_range_smul_eq_sum_drops
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (a : ℕ → ℝ) (z : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range n, a i • z i) =
      (∑ k ∈ Finset.range n,
        (a k - a (k + 1)) • ∑ j ∈ Finset.range (k + 1), z j) +
      a n • ∑ j ∈ Finset.range n, z j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (f := fun i ↦ a i • z i),
      Finset.sum_range_succ (f := fun k ↦
        (a k - a (k + 1)) • ∑ j ∈ Finset.range (k + 1), z j),
      Finset.sum_range_succ (f := z), ih]
    simp only [sub_smul, smul_add]
    abel

end HolomorphicAnosov.BarycentricGeometry
