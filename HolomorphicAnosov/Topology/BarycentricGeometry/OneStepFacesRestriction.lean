import HolomorphicAnosov.Topology.BarycentricGeometry.FlagFacesOneStep
import HolomorphicAnosov.Topology.Barycentric.StandardBarycenterMemFace

noncomputable section
open Set
open scoped Classical BigOperators

namespace HolomorphicAnosov.BarycentricGeometry

/-- The one-step barycentric cells lying in an original face are exactly the
one-step cells of that face's vertex tuple. Source: Schultz, Math 246A §I.2,
Proposition 1 and Corollary 2 p.21, subdivision definition p.22, and Theorem 4
pp.23–25. Express a cell as the centroids of a nonempty flag of index sets.
A centroid belongs to the original face exactly when its support is contained
in the face's vertex set, by positivity of its coordinates. Thus every member
of a flag whose cell lies in the face is supported there. Pull its index sets
back through the vertex injection; inclusion and nonemptiness are preserved,
and centroid relabeling preserves the vertex set. Conversely push a face flag
forward through the injection. Its centroid vertices lie in the original face,
so convexity contains the whole cell there. This includes singleton faces and
the zero-dimensional simplex. -/
theorem oneStepFaces_restriction (n m : ℕ) (a : Fin (m + 1) ↪ Fin (n + 1)) :
    {s ∈ iteratedFaces (standardVertices n) 1 |
      convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
        convexHull ℝ (range (standardVertices n ∘ a))} =
      iteratedFaces (standardVertices n ∘ a) 1 := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  let J := Finset.univ.image a
  let L := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ))
  have hvertex (i : Fin (n + 1)) : L (standardVertices n i) = Pi.single i 1 := rfl
  have hface : L.toLinearMap '' convexHull ℝ (range (standardVertices n ∘ a)) =
      convexHull ℝ ((fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ)) '' (J : Set _)) := by
    rw [LinearMap.image_convexHull]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hvertex (a i) |>.symm⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨standardVertices n (a i), ⟨i, rfl⟩, hvertex (a i)⟩
  have hcent (F : OriginalFace n) : L (F.val.centroid ℝ (standardVertices n)) =
      (F.val.card : ℝ)⁻¹ • ∑ i ∈ F.val, (Pi.single i 1 : Fin (n + 1) → ℝ) := by
    rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
      (F.val.sum_centroidWeights_eq_one_of_nonempty ℝ F.property)]
    simp only [map_sum, map_smul, Finset.centroidWeights_apply, hvertex, Finset.smul_sum]
  have hb (F : OriginalFace n) :
      F.val.centroid ℝ (standardVertices n) ∈
        convexHull ℝ (range (standardVertices n ∘ a)) ↔ F.val ⊆ J := by
    constructor
    · intro h
      apply (standard_barycenter_mem_face_iff F.val J F.property).mp
      rw [← hcent F, ← hface]
      exact ⟨_, h, rfl⟩
    · intro h
      have h' := (standard_barycenter_mem_face_iff F.val J F.property).mpr h
      rw [← hcent F, ← hface] at h'
      obtain ⟨z, hz, he⟩ := h'
      exact L.injective he ▸ hz
  rw [← flagCentroids_eq_iteratedFaces_one (standardVertices n),
    ← flagCentroids_eq_iteratedFaces_one (standardVertices n ∘ a)]
  ext s
  constructor
  · rintro ⟨⟨C, rfl⟩, hsub⟩
    have hFC : ∀ F ∈ C.finset, F.val ⊆ J := by
      intro F hF
      apply (hb F).mp
      exact hsub (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨F, hF, rfl⟩))
    let b := Function.invFun a
    have hab (i : Fin (n + 1)) (hi : i ∈ J) : a (b i) = i := by
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact Function.apply_invFun_apply
    let P : OriginalFace n → OriginalFace m := fun F ↦ ⟨F.val.image b, F.property.image b⟩
    let D : FaceFlag m := {
      finset := C.finset.image P
      nonempty := C.nonempty.image P
      comparable := by
        rintro ⟨F, hF⟩ ⟨G, hG⟩
        obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
        obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
        rcases C.comparable ⟨F', hF'⟩ ⟨G', hG'⟩ with h | h
        · exact Or.inl (Finset.image_mono _ h)
        · exact Or.inr (Finset.image_mono _ h) }
    have hrecover (F : OriginalFace n) (hF : F ∈ C.finset) :
        (P F).val.map a = F.val := by
      change (F.val.image b).map a = F.val
      rw [Finset.map_eq_image, Finset.image_image]
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        simpa only [Function.comp_apply, hab j (hFC F hF hj)] using hj
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, hab i (hFC F hF hi)⟩
    have hcentP (F : OriginalFace n) (hF : F ∈ C.finset) :
        (P F).val.centroid ℝ (standardVertices n ∘ a) =
          F.val.centroid ℝ (standardVertices n) := by
      rw [← Finset.centroid_map, hrecover F hF]
    refine ⟨D, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨F, hF, hFx⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨P F, Finset.mem_image.mpr ⟨F, hF, rfl⟩,
        (hcentP F hF).trans hFx⟩
    · intro hx
      obtain ⟨F, hF, hFx⟩ := Finset.mem_image.mp hx
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
      exact Finset.mem_image.mpr ⟨G, hG, (hcentP G hG).symm.trans hFx⟩
  · rintro ⟨D, rfl⟩
    let P : OriginalFace m → OriginalFace n := fun F ↦ ⟨F.val.map a, F.property.map⟩
    let C : FaceFlag n := {
      finset := D.finset.image P
      nonempty := D.nonempty.image P
      comparable := by
        rintro ⟨F, hF⟩ ⟨G, hG⟩
        obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
        obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
        rcases D.comparable ⟨F', hF'⟩ ⟨G', hG'⟩ with h | h
        · exact Or.inl (Finset.map_subset_map.mpr h)
        · exact Or.inr (Finset.map_subset_map.mpr h) }
    have hcentP (F : OriginalFace m) :
        (P F).val.centroid ℝ (standardVertices n) =
          F.val.centroid ℝ (standardVertices n ∘ a) :=
      F.val.centroid_map ℝ a (standardVertices n)
    constructor
    · refine ⟨C, ?_⟩
      ext x
      constructor
      · intro hx
        obtain ⟨F, hF, hFx⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨P F, Finset.mem_image.mpr ⟨F, hF, rfl⟩,
          (hcentP F).trans hFx⟩
      · intro hx
        obtain ⟨F, hF, hFx⟩ := Finset.mem_image.mp hx
        obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
        exact Finset.mem_image.mpr ⟨G, hG, (hcentP G).symm.trans hFx⟩
    · apply convexHull_min _ (convex_convexHull ℝ _)
      intro x hx
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hx
      rw [← hcentP]
      apply (hb (P F)).mpr
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

end HolomorphicAnosov.BarycentricGeometry

