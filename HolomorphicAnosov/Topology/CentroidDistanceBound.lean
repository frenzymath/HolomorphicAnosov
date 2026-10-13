import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Normed.Affine.AddTorsor
noncomputable section
open scoped BigOperators
namespace HolomorphicAnosov.BarycentricMesh
variable {V E ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

private lemma sum_vsub_centroid_zero (s : Finset ι) (hs : s.Nonempty) (v : ι → E) :
    ∑ i ∈ s, (v i -ᵥ s.centroid ℝ v) = 0 := by
  have hw := s.sum_centroidWeights_eq_one_of_nonempty ℝ hs
  have hc : s.centroid ℝ v =
      (s.weightedVSubOfPoint v (s.centroid ℝ v)) (s.centroidWeights ℝ) +ᵥ s.centroid ℝ v := by
    rw [← Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      s _ _ hw]
    rfl
  have hz := congrArg (fun x : E => x -ᵥ s.centroid ℝ v) hc
  simp only [vadd_vsub] at hz
  have hz' : (s.card : ℝ)⁻¹ • (∑ i ∈ s, (v i -ᵥ s.centroid ℝ v)) = 0 := by
    simpa [Finset.weightedVSubOfPoint_apply, Finset.centroidWeights_apply,
      ← Finset.smul_sum] using hz.symm
  exact (smul_eq_zero.mp hz').resolve_left (inv_ne_zero (by exact_mod_cast hs.card_pos.ne'))

private lemma centroid_vsub_mem_convexHull_range (s : Finset ι) (hs : s.Nonempty)
    (v : ι → E) (a : E) :
    s.centroid ℝ (fun i => v i -ᵥ a) ∈ convexHull ℝ (Set.range (fun i => v i -ᵥ a)) := by
  rw [s.centroid_eq_centerMass hs]
  apply s.centerMass_mem_convexHull
  · intro i hi
    simp [Finset.centroidWeights_apply]
  · rw [s.sum_centroidWeights_eq_one_of_nonempty ℝ hs]
    norm_num
  · intro i hi
    exact Set.mem_range_self i

/-- The distance from the centroid of a nonempty finite indexed family to a fixed point
is bounded by the average of its distances. This is the finite norm-sum estimate used
in Hatcher, Algebraic Topology, Proposition 2.21, p.120. -/
theorem centroid_dist_le_average (s : Finset ι) (hs : s.Nonempty) (v : ι → E) (a : E) :
    dist (s.centroid ℝ v) a ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, dist (v i) a := by
  rw [dist_eq_norm_vsub V, Finset.centroid_vsub_const ℝ s hs,
    Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
      (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, ← Finset.smul_sum]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  gcongr
  simpa only [dist_eq_norm_vsub V] using norm_sum_le s (fun i => v i -ᵥ a)
end HolomorphicAnosov.BarycentricMesh
