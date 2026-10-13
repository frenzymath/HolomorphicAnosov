import HolomorphicAnosov.Topology.Barycentric.StandardFlagPositiveWeightCommon
import HolomorphicAnosov.Topology.Barycentric.StandardFlagLinearIndependent
import HolomorphicAnosov.Topology.Barycentric.MemConvexHullFinsetImage

namespace HolomorphicAnosov.BarycentricGeometry
/-- Convex hulls of standard barycenters along finite strict chains intersect
exactly in the convex hull of their common vertices. Source: Schultz, Math 246A
§I.2, Theorem 4, pp.24–25; Math 205B §IV.2, p.52. Write a point in the two hulls
with nonnegative weights. Positive weights on the first chain occur in the second
chain by the coordinate separator argument. Discard the zero weights. The reverse
inclusion is convex hull monotonicity. -/
theorem standard_flag_convexHull_inter {ι : Type*} [DecidableEq ι]
    (C D : Finset (Finset ι)) (hneC : ∀ F ∈ C, F.Nonempty)
    (hneD : ∀ F ∈ D, F.Nonempty)
    (hC : (C : Set (Finset ι)).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F))
    (hD : (D : Set (Finset ι)).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F)) :
    let b : Finset ι → ι → ℝ := fun F ↦ (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i 1
    convexHull ℝ (b '' (C : Set _)) ∩ convexHull ℝ (b '' (D : Set _)) =
      convexHull ℝ ((b '' (C : Set _)) ∩ (b '' (D : Set _))) := by
  classical
  intro b
  apply Set.Subset.antisymm
  · rintro x ⟨hxC, hxD⟩
    obtain ⟨w, hw, hsum, heq⟩ := (mem_convexHull_finset_image_iff C b
      (standard_flag_linearIndependent C hneC hC).injOn x).mp hxC
    obtain ⟨v, hv, _, heqD⟩ := (mem_convexHull_finset_image_iff D b
      (standard_flag_linearIndependent D hneD hD).injOn x).mp hxD
    let S := C.filter (fun F ↦ F ∈ D)
    have hzero : ∀ F ∈ C, F ∉ S → w F = 0 := by
      intro F hF hn
      apply le_antisymm _ (hw F hF)
      by_contra hp
      have hFD := standard_flag_positive_weight_common C D hC hD w v hw hv
        (heq.trans heqD.symm) F hF (hneC F hF) (lt_of_not_ge hp)
      exact hn (Finset.mem_filter.mpr ⟨hF, hFD⟩)
    have hsumS : ∑ F ∈ S, w F = 1 := by
      rw [← hsum]
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun F hF hn ↦ hzero F hF hn)
    have heqS : ∑ F ∈ S, w F • b F = x := by
      rw [← heq]
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun F hF hn ↦ by rw [hzero F hF hn, zero_smul])
    rw [← heqS]
    have h : S.centerMass w b ∈ convexHull ℝ ((b '' (C : Set _)) ∩ (b '' (D : Set _))) :=
      S.centerMass_mem_convexHull
      (fun F hF ↦ hw F (Finset.mem_filter.mp hF).1) (by rw [hsumS]; norm_num)
      (fun F hF ↦ ⟨Set.mem_image_of_mem b (Finset.mem_filter.mp hF).1,
        Set.mem_image_of_mem b (Finset.mem_filter.mp hF).2⟩)
    simpa [Finset.centerMass_eq_of_sum_1 _ _ hsumS] using h
  · exact Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_mono Set.inter_subset_right)

end HolomorphicAnosov.BarycentricGeometry
