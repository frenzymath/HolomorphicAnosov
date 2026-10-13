import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem centroid_mem_convexHull_range
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    {E : Type u} [AddCommGroup E] [Module ℝ E] (w : ι → E) :
    s.centroid ℝ w ∈ convexHull ℝ (range w) := by
  rw [Finset.centroid_def]
  apply affineCombination_mem_convexHull
  · intro i hi
    simp only [Finset.centroidWeights_apply]
    exact inv_nonneg.mpr (by positivity)
  · exact s.sum_centroidWeights_eq_one_of_nonempty ℝ hs

end HolomorphicAnosov.BarycentricGeometry
