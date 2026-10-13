import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module
import HolomorphicAnosov.Topology.Barycentric.mem_convexHull_range_iff_weights
import HolomorphicAnosov.Topology.Barycentric.exists_antitone_permutation
import HolomorphicAnosov.Topology.Barycentric.prefix_centroid_eq_smul_sum
import HolomorphicAnosov.Topology.Barycentric.sum_range_smul_eq_sum_drops
import HolomorphicAnosov.Topology.Barycentric.sum_drop_weights
import HolomorphicAnosov.Topology.Barycentric.weighted_sum_eq_drop_centroids
import HolomorphicAnosov.Topology.Barycentric.sum_Iic_eq_range_of_fin

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Public reusable finite barycentric helper extracted from BarycentricCoverage. -/
theorem convexHull_subset_union_children
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (v : Fin m → E) :
    convexHull ℝ (range v) ⊆
      ⋃ σ : Equiv.Perm (Fin m), convexHull ℝ (range (fun k : Fin m ↦
        (Finset.univ.filter (fun j : Fin m ↦ j ≤ k)).centroid ℝ (v ∘ σ))) := by
  classical
  intro x hx
  obtain ⟨w, hw, hsum, heq⟩ := (mem_convexHull_range_iff_weights m v x).mp hx
  obtain ⟨σ, hanti⟩ := exists_antitone_permutation m w
  let a : ℕ → ℝ := fun i ↦ if h : i < m then w (σ ⟨i, h⟩) else 0
  let z : ℕ → E := fun i ↦ if h : i < m then v (σ ⟨i, h⟩) else 0
  let c : Fin m → ℝ := fun k ↦
    (a k.val - a (k.val + 1)) * ((k.val + 1 : ℕ) : ℝ)
  have hterminal : a m = 0 := by simp [a]
  have hdrop_nonneg : ∀ k : Fin m, 0 ≤ c k := by
    intro k
    apply mul_nonneg _ (by positivity)
    apply sub_nonneg.mpr
    by_cases hk : k.val + 1 < m
    · have hle : k ≤ (⟨k.val + 1, hk⟩ : Fin m) := by
        change k.val ≤ k.val + 1
        omega
      simpa [a, k.isLt, hk] using hanti hle
    · simp [a, k.isLt, hk, hw]
  have hsum_a : (∑ i ∈ Finset.range m, a i) = 1 := by
    rw [← Fin.sum_univ_eq_sum_range a m]
    simpa [a] using (Equiv.sum_comp σ w).trans hsum
  have hsum_c : (∑ k : Fin m, c k) = 1 := by
    rw [Finset.sum_fin_eq_sum_range]
    calc
      (∑ k ∈ Finset.range m, if h : k < m then c ⟨k, h⟩ else 0) =
          ∑ k ∈ Finset.range m,
            (a k - a (k + 1)) * ((k + 1 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [c, Finset.mem_range.mp hk]
      _ = 1 := (sum_drop_weights a m hterminal).trans hsum_a
  have hchild (k : Fin m) :
      (Finset.univ.filter (fun j : Fin m ↦ j ≤ k)).centroid ℝ (v ∘ σ) =
        ((k.val + 1 : ℕ) : ℝ)⁻¹ • ∑ j ∈ Finset.range (k.val + 1), z j := by
    rw [prefix_centroid_eq_smul_sum, sum_Iic_eq_range_of_fin]
    rfl
  have hsum_z : (∑ i ∈ Finset.range m, a i • z i) = x := by
    calc
      (∑ i ∈ Finset.range m, a i • z i) =
          ∑ i : Fin m, w (σ i) • v (σ i) := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        simp [a, z, Finset.mem_range.mp hi]
      _ = ∑ i : Fin m, w i • v i := Equiv.sum_comp σ (fun i ↦ w i • v i)
      _ = x := heq
  have hsum_child :
      (∑ k : Fin m, c k •
        (Finset.univ.filter (fun j : Fin m ↦ j ≤ k)).centroid ℝ (v ∘ σ)) = x := by
    rw [← hsum_z, weighted_sum_eq_drop_centroids a z m hterminal,
      Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    simp [c, a, hchild, hkm]
  apply Set.mem_iUnion.mpr
  refine ⟨σ, mem_convexHull_of_exists_fintype c _ hdrop_nonneg hsum_c ?_ hsum_child⟩
  simp

end HolomorphicAnosov.BarycentricGeometry
