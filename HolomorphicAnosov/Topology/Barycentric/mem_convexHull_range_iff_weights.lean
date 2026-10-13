import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem mem_convexHull_range_iff_weights
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (v : Fin m → E) (x : E) :
    x ∈ convexHull ℝ (range v) ↔
      ∃ w : Fin m → ℝ, (∀ i, 0 ≤ w i) ∧
        (∑ i, w i) = 1 ∧ (∑ i, w i • v i) = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw, hsum, heq⟩ := hx
    let w' : Fin m → ℝ := fun i ↦ if i ∈ s then w i else 0
    refine ⟨w', ?_, ?_, ?_⟩
    · intro i
      simp only [w']
      split_ifs with hi
      · exact hw i hi
      · exact le_refl 0
    · simpa [w', Finset.sum_ite] using hsum
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at heq
      simpa [w', ite_smul, Finset.sum_ite] using heq
  · rintro ⟨w, hw, hsum, heq⟩
    exact mem_convexHull_of_exists_fintype w v hw hsum (by simp) heq

end HolomorphicAnosov.BarycentricGeometry
