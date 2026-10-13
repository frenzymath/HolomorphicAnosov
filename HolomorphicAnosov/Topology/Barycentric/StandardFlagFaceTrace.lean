import HolomorphicAnosov.Topology.Barycentric.StandardBarycenterMemFace
import HolomorphicAnosov.Topology.Barycentric.StandardFlagLinearIndependent
import HolomorphicAnosov.Topology.Barycentric.MemConvexHullFinsetImage

namespace HolomorphicAnosov.BarycentricGeometry
/-- Intersection of a standard barycentric flag cell with an original face removes
precisely the flag members not contained in that face. Source: Schultz, Math 246A
§I.2, p.21, with the nonnegative barycentric coefficient argument of Theorem 4.
Outside coordinates vanish on the original face, so a positive weight cannot occur
on any set containing an outside index. Restrict the convex combination accordingly. -/
theorem standard_flag_face_trace {ι : Type*} [DecidableEq ι]
    (C : Finset (Finset ι)) (hne : ∀ F ∈ C, F.Nonempty)
    (hC : (C : Set (Finset ι)).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F)) (A : Finset ι) :
    let b : Finset ι → ι → ℝ := fun F ↦ (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i 1
    convexHull ℝ (b '' (C : Set _)) ∩
      convexHull ℝ ((fun i ↦ (Pi.single i 1 : ι → ℝ)) '' (A : Set ι)) =
      convexHull ℝ (b '' ((C.filter (fun F ↦ F ⊆ A)) : Set _)) := by
  classical
  intro b
  have hbc : ∀ G i, b G i = if i ∈ G then (G.card : ℝ)⁻¹ else 0 :=
    standard_barycenter_coordinate
  apply Set.Subset.antisymm
  · rintro x ⟨hxC, hxA⟩
    obtain ⟨w, hw, hsum, heq⟩ := (mem_convexHull_finset_image_iff C b
      (standard_flag_linearIndependent C hne hC).injOn x).mp hxC
    let S := C.filter (fun F ↦ F ⊆ A)
    have hzero : ∀ F ∈ C, F ∉ S → w F = 0 := by
      intro F hF hn
      apply le_antisymm _ (hw F hF)
      by_contra hp
      have hwF : 0 < w F := lt_of_not_ge hp
      have hnFA : ¬ F ⊆ A := fun h ↦ hn (Finset.mem_filter.mpr ⟨hF, h⟩)
      obtain ⟨i, hiF, hiA⟩ := Finset.not_subset.mp hnFA
      have hpos : 0 < (∑ G ∈ C, w G • b G) i := by
        rw [Finset.sum_apply]
        change 0 < ∑ G ∈ C, w G * b G i
        apply lt_of_lt_of_le (mul_pos hwF ?_) (Finset.single_le_sum (fun G hG ↦
          mul_nonneg (hw G hG) (by rw [hbc]; split_ifs <;> positivity)) hF)
        rw [hbc, ite_eq_left hiF]
        exact inv_pos.mpr (Nat.cast_pos.mpr (hne F hF).card_pos)
      rw [heq, standard_face_coordinate_zero A i hiA x hxA] at hpos
      exact (lt_irrefl 0) hpos
    have hsumS : ∑ F ∈ S, w F = 1 := by
      rw [← hsum]
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun F hF hn ↦ hzero F hF hn)
    have heqS : ∑ F ∈ S, w F • b F = x := by
      rw [← heq]
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun F hF hn ↦ by rw [hzero F hF hn, zero_smul])
    rw [← heqS]
    have h : S.centerMass w b ∈ convexHull ℝ (b '' (S : Set _)) :=
      S.centerMass_mem_convexHull
        (fun F hF ↦ hw F (Finset.mem_filter.mp hF).1) (by rw [hsumS]; norm_num)
        (fun F hF ↦ Set.mem_image_of_mem b hF)
    simpa [S, Finset.centerMass_eq_of_sum_1 _ _ hsumS] using h
  · apply Set.subset_inter
    · exact convexHull_mono (Set.image_mono (Finset.filter_subset _ _))
    · apply convexHull_min _ (convex_convexHull ℝ _)
      rintro x ⟨F, hF, rfl⟩
      exact (standard_barycenter_mem_face_iff F A (hne F (Finset.mem_filter.mp hF).1)).mpr
        (Finset.mem_filter.mp hF).2

end HolomorphicAnosov.BarycentricGeometry
