import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesIntersection
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesNonemptyDownClosed
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesEmbedding
import HolomorphicAnosov.Topology.SimplicialFaceCentroid
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesCoverage

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- Iterated barycentric subdivision restricts exactly to each original vertex face.
Source: Schultz, Mathematics 246A §I.2 Proposition 1 and Corollary 2 p.21,
barycentric flag definition p.22, and iteration after Theorem 4 p.25;
Hatcher, Proposition 2.21(1), pp.119–121. The source omits the face-detection
argument; its agent-written expansion is the separate public dependency
`simplicial_face_centroid_mem_iff`, proved from Mathlib affine independence.

The face-subdivision embedding theorem first identifies every descendant of the
original face as a descendant of the full simplex. This follows by induction:
a first child of the face is a subface of a first child of the full simplex by
one-step restriction; injectively identify its vertices and apply induction to
the remaining path. Coverage of the face subdivision equals the original face
hull. For a full-complex cell whose hull lies there, take its centroid and choose
a face-subdivision cell containing that point. Both are faces of the already
proved full geometric complex. The centroid criterion forces the entire first
vertex set into the chosen second one; downward closure makes it a face of the
face subdivision. Conversely every face-subdivision cell is already a cell of
the full complex, and coverage puts its hull inside the original face. Thus both
literal face families agree at every depth. Nonempty faces make the centroid
weights positive; singleton faces and depth zero are included without exceptions. -/
theorem iteratedFaces_restriction (n r m : ℕ) (a : Fin (m + 1) ↪ Fin (n + 1)) :
    {s ∈ iteratedFaces (standardVertices n) r |
      convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
        convexHull ℝ (range (standardVertices n ∘ a))} =
      iteratedFaces (standardVertices n ∘ a) r := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  have hclosed := iteratedFaces_nonempty_down_closed (standardVertices n) r
  let K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))) := {
    faces := iteratedFaces (standardVertices n) r
    isRelLowerSet_faces := fun s hs ↦
      ⟨hclosed.1 s hs, fun t hts ht ↦ hclosed.2 s hs t hts ht⟩
    indep := fun hs ↦ iteratedFaces_affineIndependent n r _ hs
    inter_subset_convexHull := fun hs ht ↦ iteratedFaces_convexHull_inter_subset n r _ hs _ ht }
  have hstandard : LinearIndependent ℝ (standardVertices n) := by
    exact (Pi.linearIndependent_single_one (Fin (n + 1)) ℝ).map'
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ _).symm.injective)
  have hinclusion := iteratedFaces_embedding_subset (standardVertices n) hstandard r m a
  ext s
  constructor
  · rintro ⟨hs, hsub⟩
    have hsK : s ∈ K.faces := hs
    have hsne := K.nonempty_of_mem_faces hsK
    let x := s.centroid ℝ id
    have hxs : x ∈ convexHull ℝ (s : Set _) := s.centroid_mem_convexHull hsne
    have hxf := hsub hxs
    rw [← iteratedFaces_convexHull_union (standardVertices n ∘ a) r] at hxf
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxf
    have htK : t ∈ K.faces := hinclusion ht
    have hst : s ⊆ t := (simplicial_face_centroid_mem_iff K hsK htK).mp hxt
    exact (iteratedFaces_nonempty_down_closed (standardVertices n ∘ a) r).2 t ht s hst hsne
  · intro hs
    refine ⟨hinclusion hs, ?_⟩
    intro x hx
    rw [← iteratedFaces_convexHull_union (standardVertices n ∘ a) r]
    exact Set.mem_iUnion₂.mpr ⟨s, hs, hx⟩

end HolomorphicAnosov.BarycentricGeometry

