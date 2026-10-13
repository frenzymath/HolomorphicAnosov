import HolomorphicAnosov.Topology.BarycentricGeometry.OneStepFacesIntersection
import HolomorphicAnosov.Topology.Barycentric.prefix_centroid_eq_smul_sum

/-!
# Common faces of a barycentric subdivision in independent coordinates

Source: Schultz, Mathematics 246A §I.2, Theorem 4 and its proof, printed pp.23–25.
The proof treats a simplex with arbitrary vertices using their unique coefficients.
Here a linearly independent tuple gives an injective linear coordinate map from the
standard simplex. Equal-weight centroids, their faces, and convex hulls commute with
this map, transporting the already proved standard-coordinate intersection theorem.
-/

noncomputable section
open Set
open scoped Classical BigOperators

namespace HolomorphicAnosov.BarycentricGeometry

/-- Linear maps commute with the literal permutation-path encoding of subdivision.
This is coordinate transport: prefix centroids commute with linear maps by their
finite equal-weight sum formula, then induction handles the permutation list.
No injectivity or independence is required for this encoding identity. -/
theorem iteratedFaces_image_linearMap {m : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (v : Fin (m + 1) → E) (r : ℕ) :
    iteratedFaces (L ∘ v) r = (Finset.image L) '' iteratedFaces v r := by
  classical
  have hc (w : Fin (m + 1) → E) (σ : Equiv.Perm (Fin (m + 1))) :
      BarycentricMesh.childVertices (L ∘ w) σ = L ∘ BarycentricMesh.childVertices w σ := by
    funext k
    simp only [BarycentricMesh.childVertices, prefix_centroid_eq_smul_sum,
      Function.comp_apply, map_smul, map_sum]
  have hi (p : List (Equiv.Perm (Fin (m + 1)))) (w : Fin (m + 1) → E) :
      BarycentricMesh.iteratedVertices (L ∘ w) p =
        L ∘ BarycentricMesh.iteratedVertices w p := by
    induction p generalizing w with
    | nil => rfl
    | cons σ p ih =>
      simp only [BarycentricMesh.iteratedVertices, hc]
      exact ih _
  ext s
  constructor
  · rintro ⟨p, hp, A, hA, rfl⟩
    refine ⟨A.image (BarycentricMesh.iteratedVertices v p), ⟨p, hp, A, hA, rfl⟩, ?_⟩
    rw [Finset.image_image, hi]
  · rintro ⟨u, ⟨p, hp, A, hA, rfl⟩, rfl⟩
    exact ⟨p, hp, A, hA, by rw [Finset.image_image, hi]⟩

/-- One-step barycentric faces of a linearly independent vertex tuple intersect exactly
in the convex hull of their common vertices. Source: Schultz, Mathematics 246A §I.2,
Theorem 4, printed pp.23–25, specialized to a linearly independent tuple.

Send each standard coordinate vertex to the corresponding given vertex by the linear
combination map. Independence makes this map injective. Its linearity preserves every
prefix centroid, so the same permutation and selected index set lift each given face to
a standard one-step face. Linear images commute with convex hulls, and injectivity makes
them commute with intersections. Apply the standard-coordinate common-face theorem and
map its equality forward. Singleton faces and a one-vertex simplex are included. -/
theorem oneStepFaces_convexHull_inter_of_linearIndependent {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : Fin (n + 1) → E)
    (hv : LinearIndependent ℝ v) (s t : Finset E)
    (hs : s ∈ iteratedFaces v 1) (ht : t ∈ iteratedFaces v 1) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) =
      convexHull ℝ ((s : Set E) ∩ t) := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  let L : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] E :=
    (Fintype.linearCombination ℝ v).comp
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap
  have hL : Function.Injective L :=
    hv.fintypeLinearCombination_injective.comp (WithLp.linearEquiv 2 ℝ _).injective
  have hvertex (i : Fin (n + 1)) : L (standardVertices n i) = v i := by
    change Fintype.linearCombination ℝ v (Pi.single i 1) = v i
    simp
  have hvertices : L ∘ standardVertices n = v := funext hvertex
  have hlift (u : Finset E) (hu : u ∈ iteratedFaces v 1) :
      ∃ u' ∈ iteratedFaces (standardVertices n) 1,
        (u : Set E) = L '' (u' : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    rw [← hvertices, iteratedFaces_image_linearMap] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    exact ⟨u', hu', by simp only [Finset.coe_image]⟩
  obtain ⟨s', hs', hsi⟩ := hlift s hs
  obtain ⟨t', ht', hti⟩ := hlift t ht
  rw [hsi, hti, ← Set.image_inter hL, ← LinearMap.image_convexHull,
    ← LinearMap.image_convexHull, ← Set.image_inter hL,
    oneStepFaces_convexHull_inter n s' t' hs' ht', LinearMap.image_convexHull]

end HolomorphicAnosov.BarycentricGeometry

