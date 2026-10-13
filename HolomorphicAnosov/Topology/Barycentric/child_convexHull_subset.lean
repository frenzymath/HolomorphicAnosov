import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module
import HolomorphicAnosov.Topology.Barycentric.centroid_mem_convexHull_range

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem child_convexHull_subset
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (v : Fin m → E) (σ : Equiv.Perm (Fin m)) :
    convexHull ℝ (range (fun k : Fin m ↦
      (Finset.univ.filter (fun j : Fin m ↦ j ≤ k)).centroid ℝ (v ∘ σ)))
      ⊆ convexHull ℝ (range v) := by
  classical
  apply convexHull_min _ (convex_convexHull ℝ (range v))
  rintro x ⟨k, rfl⟩
  have hs : (Finset.univ.filter (fun j : Fin m ↦ j ≤ k)).Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl k⟩⟩
  exact (convexHull_mono (Set.range_comp_subset_range σ v))
    (centroid_mem_convexHull_range _ hs (v ∘ σ))

end HolomorphicAnosov.BarycentricGeometry
