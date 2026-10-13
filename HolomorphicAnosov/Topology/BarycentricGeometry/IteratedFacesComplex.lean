import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesIntersection
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesRestriction
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesCoverage
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesAffineIndependent
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesNonemptyDownClosed
import HolomorphicAnosov.Topology.BarycentricGeometry.EuclideanSimplexHull

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- The finite-depth prefix descendants form a simplicial complex whose
restriction to each original face equals that face's own subdivision.
Source: Schultz, Math 246A §I.2 Theorem 4 and proof pp.23–25, Proposition 1
and Corollary 2 p.21; Math 205B §IV.2 Lemma 6 and proof p.51; Hatcher pp.119–121.
Proof: at depth zero take all nonempty vertex subsets of the standard simplex.
Their affine independence and common-face intersections follow from the
coordinate vertices. For the induction step, subdivide every parent simplex
by its barycentric flags. Its affine-independent vertex tuple identifies it
affinely with a standard simplex; the coordinate flag theorem transports
independence, common-face intersections, and exact face traces across this
identification. On a shared parent face both local subdivisions agree, since
its face barycenters do not depend on the containing simplex. Schultz Lemma 6
glues these finite local complexes: an intersection of cells from different
parents lies in the shared parent face and is the hull of the common child
vertices by the trace theorem. Nonempty subfaces remain local cells. Coverage
of each parent by its prefix cells proves that the space is unchanged. Paths
append one permutation at each stage, so the resulting faces are exactly the
specified iteratedFaces. Restriction to an original face commutes at depth
zero and with each subsequent subdivision by the same centroid and trace
calculation; induction gives the stated equality for every injective face
tuple, including singleton faces. -/
theorem iteratedFaces_simplicialComplex (n r : ℕ) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))),
      K.faces = iteratedFaces (standardVertices n) r ∧
      K.space = euclideanSimplex n ∧
      ∀ (m : ℕ) (a : Fin (m + 1) ↪ Fin (n + 1)),
        {s ∈ K.faces | convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
          convexHull ℝ (range (standardVertices n ∘ a))} =
            iteratedFaces (standardVertices n ∘ a) r := by
  classical
  have hclosed := iteratedFaces_nonempty_down_closed (standardVertices n) r
  let K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))) := {
    faces := iteratedFaces (standardVertices n) r
    isRelLowerSet_faces := fun s hs ↦
      ⟨hclosed.1 s hs, fun t hts ht ↦ hclosed.2 s hs t hts ht⟩
    indep := fun hs ↦ iteratedFaces_affineIndependent n r _ hs
    inter_subset_convexHull := fun hs ht ↦ iteratedFaces_convexHull_inter_subset n r _ hs _ ht }
  refine ⟨K, rfl, ?_, ?_⟩
  · exact (iteratedFaces_convexHull_union (standardVertices n) r).trans
      (euclideanSimplex_eq_convexHull n).symm
  · intro m a
    exact iteratedFaces_restriction n r m a

end HolomorphicAnosov.BarycentricGeometry

