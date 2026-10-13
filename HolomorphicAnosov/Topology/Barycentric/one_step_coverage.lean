import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module
import HolomorphicAnosov.Topology.Barycentric.convexHull_subset_union_children
import HolomorphicAnosov.Topology.Barycentric.child_convexHull_subset

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem one_step_coverage
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (v : Fin m → E) :
    convexHull ℝ (range v) =
      ⋃ σ : Equiv.Perm (Fin m), convexHull ℝ (range (fun k : Fin m ↦
        (Finset.univ.filter (fun j : Fin m ↦ j ≤ k)).centroid ℝ (v ∘ σ))) := by
  apply Set.Subset.antisymm (convexHull_subset_union_children m v)
  intro x hx
  obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hx
  exact child_convexHull_subset m v σ hσ

end HolomorphicAnosov.BarycentricGeometry
