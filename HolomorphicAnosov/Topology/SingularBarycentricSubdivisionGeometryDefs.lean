import HolomorphicAnosov.Topology.BarycentricGeometry.FaceFlag
import HolomorphicAnosov.Topology.BarycentricGeometry.OriginalFace
import HolomorphicAnosov.Topology.BarycentricCoverage
import HolomorphicAnosov.Topology.StandardSimplexBarycentricFlagIntersections
import HolomorphicAnosov.Topology.BarycentricIteratedMesh
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Order.NonemptyFiniteChains

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry
/-- Original Euclidean coordinate vertices of Δⁿ (Hatcher pp.119–120). -/
def standardVertices (n : ℕ) : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
  fun i ↦ EuclideanSpace.single i 1

/-- Mathlib's standard simplex weights, embedded into its Euclidean coordinate space. This fixes
both the actual standard simplex and its Euclidean metric (Hatcher p.120). -/
def euclideanSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  range fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) ↦ WithLp.toLp 2 (fun i ↦ t.weights i)

/-- Original-face barycenter, with exactly the indexed equal weights in the source. The actual
finite-set centroid is Mathlib's (Hatcher pp.119–120). -/
def faceBarycenter (n : ℕ) (F : OriginalFace n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  F.val.centroid ℝ (standardVertices n)

/-- Actual barycentric vertices of a flag (Hatcher pp.119–120, Appendix pp.534–535). -/
def flagVertices (n : ℕ) (C : FaceFlag n) : Finset (EuclideanSpace ℝ (Fin (n + 1))) :=
  C.finset.image (faceBarycenter n)

/-- All finite flag simplices, not just maximal flags (Hatcher pp.119–120). The empty hull is
treated separately; Mathlib geometric complexes have nonempty faces. -/
def flagFaces (n : ℕ) : Set (Finset (EuclideanSpace ℝ (Fin (n + 1)))) :=
  {s | ∃ C : FaceFlag n, s = flagVertices n C}

/-- Maximal one-step cells are the actual prefix-centroid hulls already constructed in the library.
Hatcher's recursively coned construction is identified with these in the theorem. -/
def maximalCells (n : ℕ) : Set (Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  {S | ∃ σ : Equiv.Perm (Fin (n + 1)),
    S = BarycentricMesh.hull (BarycentricMesh.childVertices (standardVertices n) σ)}

/-- The same recursive coning: complete flags in a codimension-one original face coned to the full
barycenter. At dimension zero, retain the unchanged vertex (Hatcher pp.119–120). A flag with n
members in an opposite n-vertex face is a maximal flag of that face. -/
def conedMaximalCells (n : ℕ) : Set (Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  if n = 0 then {euclideanSimplex n} else
    {S | ∃ i : Fin (n + 1), ∃ C : FaceFlag n,
      C.finset.card = n ∧ (∀ F ∈ C.finset, i ∉ F.val) ∧
      S = convexHull ℝ
        (insert ((Finset.univ : Finset (Fin (n + 1))).centroid ℝ (standardVertices n))
          (flagVertices n C : Set (EuclideanSpace ℝ (Fin (n + 1)))))}

/-- All nonempty subfaces of the finite-depth permutation-prefix cells. The iteration is the
existing genuine `BarycentricMesh.iteratedVertices`, not an assumed map. Hatcher pp.120–121; index
subsets keep lower-dimensional cells. -/
def iteratedFaces {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin (m + 1) → E) (r : ℕ) : Set (Finset E) :=
  {s | ∃ p : List (Equiv.Perm (Fin (m + 1))), p.length = r ∧
    ∃ A : Finset (Fin (m + 1)), A.Nonempty ∧
      s = A.image (BarycentricMesh.iteratedVertices v p)}

end HolomorphicAnosov.BarycentricGeometry
