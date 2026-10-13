import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem prefix_centroid_eq_smul_sum
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (w : Fin m → E) (k : Fin m) :
    (Finset.univ.filter (fun j : Fin m ↦ j ≤ k)).centroid ℝ w =
      ((k.val + 1 : ℕ) : ℝ)⁻¹ • ∑ j ∈ Finset.Iic k, w j := by
  classical
  have hs : (Finset.Iic k).Nonempty := ⟨k, Finset.mem_Iic.mpr (le_refl k)⟩
  have hcard : (Finset.Iic k).card = k.val + 1 := Fin.card_Iic k
  have hp : Finset.univ.filter (fun j : Fin m ↦ j ≤ k) = Finset.Iic k := by
    ext j
    simp
  rw [hp]
  rw [Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      ((Finset.Iic k).sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, hcard, ← Finset.smul_sum]

end HolomorphicAnosov.BarycentricGeometry
