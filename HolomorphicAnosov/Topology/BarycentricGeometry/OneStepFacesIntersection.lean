import HolomorphicAnosov.Topology.BarycentricGeometry.FlagFacesOneStep
import HolomorphicAnosov.Topology.BarycentricGeometry.CoordinateFlagIntersectionEuclidean

noncomputable section
open Set
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- Two one-step barycentric descendant faces meet in the convex hull of their
common vertices. Source: Schultz, Mathematics 246A §I.2 Theorem 4, pp.23–25,
and Mathematics 205B §IV.2 Lemma 6, p.51. The prefix/flag equivalence expresses
both descendant faces as finite chains of nonempty original faces. Forgetting
the nonemptiness proofs gives strict chains of finite index subsets. The
Euclidean centroid is the inverse coordinate equivalence applied to the
uniform coordinate barycenter. Transport the coordinate flag-intersection
identity through that injective linear equivalence. Its image preserves both
convex hulls and intersections, giving exactly the asserted common-vertex hull.
Singleton flags and the zero-dimensional simplex are included. -/
theorem oneStepFaces_convexHull_inter (n : ℕ)
    (s t : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (hs : s ∈ iteratedFaces (standardVertices n) 1)
    (ht : t ∈ iteratedFaces (standardVertices n) 1) :
    convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩
      convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
        convexHull ℝ ((s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ t) := by
  rw [← flagFaces_eq_iteratedFaces_one] at hs ht
  obtain ⟨C, rfl⟩ := hs
  obtain ⟨D, rfl⟩ := ht
  let e := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
  let b : Finset (Fin (n + 1)) → Fin (n + 1) → ℝ :=
    fun F ↦ (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)
  let indices := fun C : FaceFlag n ↦ C.finset.image Subtype.val
  have hflags (C : FaceFlag n) :
      (∀ F ∈ indices C, F.Nonempty) ∧
      (indices C : Set (Finset (Fin (n + 1)))).Pairwise
        (fun F G ↦ F ⊂ G ∨ G ⊂ F) := by
    constructor
    · rintro F hF
      obtain ⟨F, _, rfl⟩ := Finset.mem_image.mp hF
      exact F.property
    · rintro F hF G hG hFG
      obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
      rcases C.comparable ⟨F', hF'⟩ ⟨G', hG'⟩ with h | h
      · exact Or.inl (Finset.ssubset_iff_subset_ne.mpr ⟨h, hFG⟩)
      · exact Or.inr (Finset.ssubset_iff_subset_ne.mpr ⟨h, hFG.symm⟩)
  have hb (F : OriginalFace n) : faceBarycenter n F = e (b F.val) := by
    unfold faceBarycenter
    rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination]
    · simp only [Finset.centroidWeights_apply]
      rw [← Finset.smul_sum]
      change _ = WithLp.toLp 2 _
      rw [WithLp.toLp_smul, WithLp.toLp_sum]
      congr 1
    · simpa using F.val.sum_centroidWeights_eq_one_of_nonempty ℝ F.property
  have hv (C : FaceFlag n) :
      (flagVertices n C : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
        e.toLinearMap '' (b '' (indices C : Set _)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨b F.val, ⟨F.val, Finset.mem_image.mpr ⟨F, hF, rfl⟩, rfl⟩, (hb F).symm⟩
    · rintro ⟨y, ⟨F, hF, rfl⟩, rfl⟩
      change F ∈ C.finset.image Subtype.val at hF
      obtain ⟨G, hG, hGF⟩ := (Finset.mem_image (f := (Subtype.val : OriginalFace n → _))).mp hF
      subst F
      exact Finset.mem_image.mpr ⟨G, hG, hb G⟩
  rw [hv C, hv D]
  have he : Function.Injective (e.toLinearMap : (Fin (n + 1) → ℝ) → _) := e.injective
  rw [← Set.image_inter he]
  conv_rhs => rw [← LinearMap.image_convexHull]
  exact coordinate_flag_cell_intersection_transport n (indices C) (indices D)
    (hflags C) (hflags D)

end HolomorphicAnosov.BarycentricGeometry
