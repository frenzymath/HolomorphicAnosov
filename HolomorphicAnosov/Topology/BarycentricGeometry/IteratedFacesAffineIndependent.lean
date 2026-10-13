import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs
import HolomorphicAnosov.Topology.BarycentricGeometry.ChildVerticesLinearIndependent
import Mathlib.LinearAlgebra.StdBasis

/-!
# Affine independence of finite-depth barycentric faces

Source: Schultz, Mathematics 246A §I.2, Proposition 3, p.23, and the iterated subdivision
construction after Theorem 4, p.25; Hatcher, Proposition 2.21(1), pp.119–121.
-/

noncomputable section
open Set
open scoped Classical

namespace HolomorphicAnosov.BarycentricGeometry

/-- Every nonempty vertex subface of a finite-depth barycentric descendant of the standard
simplex is affinely independent. Source: Schultz, Mathematics 246A §I.2, Proposition 3, p.23,
and iteration after Theorem 4, p.25; Hatcher, Proposition 2.21(1), pp.119–121.
The original coordinate vertices are linearly independent. Induction on the permutation
list preserves linear independence by the prefix-child theorem. Restriction to a finite
set of the resulting vertices preserves linear independence, which implies affine
independence. The empty path and the zero-dimensional simplex are included. -/
theorem iteratedFaces_affineIndependent (n r : ℕ)
    (s : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (hs : s ∈ iteratedFaces (standardVertices n) r) :
    AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin (n + 1))) := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  have hstandard : LinearIndependent ℝ (standardVertices n) := by
    let e := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
    exact (Pi.linearIndependent_single_one (Fin (n + 1)) ℝ).map'
      e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  obtain ⟨p, hp, A, hA, rfl⟩ := hs
  clear hp hA
  have hiter : ∀ (v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))),
      LinearIndependent ℝ v → LinearIndependent ℝ (BarycentricMesh.iteratedVertices v p) := by
    induction p with
    | nil => intro v hv; exact hv
    | cons σ p ih =>
      intro v hv
      exact ih (BarycentricMesh.childVertices v σ) (childVertices_linearIndependent v hv σ)
  apply (hiter _ hstandard).linearIndepOn_id.affineIndepOn.mono
  rw [Finset.coe_image]
  exact Set.image_subset_range _ _

end HolomorphicAnosov.BarycentricGeometry

