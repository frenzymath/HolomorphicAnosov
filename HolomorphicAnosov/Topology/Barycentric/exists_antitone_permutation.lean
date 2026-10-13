import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem exists_antitone_permutation (m : ℕ) (w : Fin m → ℝ) :
    ∃ σ : Equiv.Perm (Fin m), Antitone (w ∘ σ) := by
  refine ⟨Tuple.sort (fun i ↦ -w i), ?_⟩
  intro i j hij
  have h := Tuple.monotone_sort (fun i : Fin m ↦ -w i) hij
  simpa only [Function.comp_apply, neg_le_neg_iff] using h

end HolomorphicAnosov.BarycentricGeometry
