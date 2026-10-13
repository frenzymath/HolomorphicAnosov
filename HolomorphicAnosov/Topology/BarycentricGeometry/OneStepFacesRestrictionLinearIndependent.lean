import HolomorphicAnosov.Topology.BarycentricGeometry.OneStepFacesLinearIndependent
import HolomorphicAnosov.Topology.BarycentricGeometry.OneStepFacesRestriction

noncomputable section
open Set
open scoped Classical

namespace HolomorphicAnosov.BarycentricGeometry

/-- One-step barycentric subdivision of an independent vertex tuple restricts
to the intrinsic subdivision of every injectively indexed vertex face.
Source: Schultz, Mathematics 246A §I.2 Proposition 1 and Corollary 2, p.21,
barycentric subdivision definition p.22, and Theorem 4 proof pp.23–25.

Send the standard coordinate vertices to the given independent tuple by their
linear-combination map. Independence makes the map injective. Prefix centroids
and every permutation path commute with this map, so both the full subdivision
and the selected face subdivision are images of the standard-coordinate ones.
Linear maps preserve convex hulls, and injectivity both preserves and reflects
containment of their images. Transport the standard one-step restriction
identity along this map. This includes singleton faces, full faces, and arbitrary
vertex injections; no ambient spanning hypothesis is needed. -/
theorem oneStepFaces_restriction_of_linearIndependent {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin (n + 1) → E) (hv : LinearIndependent ℝ v)
    (m : ℕ) (a : Fin (m + 1) ↪ Fin (n + 1)) :
    {s ∈ iteratedFaces v 1 | convexHull ℝ (s : Set E) ⊆
      convexHull ℝ (range (v ∘ a))} = iteratedFaces (v ∘ a) 1 := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  let L : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] E :=
    (Fintype.linearCombination ℝ v).comp
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap
  have hL : Function.Injective L :=
    hv.fintypeLinearCombination_injective.comp (WithLp.linearEquiv 2 ℝ _).injective
  have hvertices : L ∘ standardVertices n = v := by
    funext i
    change Fintype.linearCombination ℝ v (Pi.single i 1) = v i
    simp
  have hfaceVertices : L ∘ (standardVertices n ∘ a) = v ∘ a := by
    rw [← Function.comp_assoc, hvertices]
  have hfull : iteratedFaces v 1 =
      (Finset.image L) '' iteratedFaces (standardVertices n) 1 := by
    rw [← hvertices, iteratedFaces_image_linearMap]
  have hface : iteratedFaces (v ∘ a) 1 =
      (Finset.image L) '' iteratedFaces (standardVertices n ∘ a) 1 := by
    rw [← hfaceVertices, iteratedFaces_image_linearMap]
  have hfaceHull : convexHull ℝ (range (v ∘ a)) =
      L '' convexHull ℝ (range (standardVertices n ∘ a)) := by
    rw [← hfaceVertices, Set.range_comp, LinearMap.image_convexHull]
  ext s
  constructor
  · rintro ⟨hs, hsub⟩
    rw [hfull] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have hsub' : convexHull ℝ (s' : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
        convexHull ℝ (range (standardVertices n ∘ a)) := by
      apply (Set.image_subset_image_iff hL).mp
      rw [LinearMap.image_convexHull]
      simpa only [Finset.coe_image, hfaceHull] using hsub
    rw [hface]
    exact ⟨s', (oneStepFaces_restriction n m a).subset ⟨hs', hsub'⟩, rfl⟩
  · rw [hface]
    rintro ⟨s', hs', rfl⟩
    obtain ⟨hs', hsub'⟩ := (oneStepFaces_restriction n m a).symm.subset hs'
    refine ⟨hfull.symm ▸ Set.mem_image_of_mem _ hs', ?_⟩
    rw [hfaceHull, Finset.coe_image, ← LinearMap.image_convexHull]
    exact Set.image_mono hsub'

end HolomorphicAnosov.BarycentricGeometry

