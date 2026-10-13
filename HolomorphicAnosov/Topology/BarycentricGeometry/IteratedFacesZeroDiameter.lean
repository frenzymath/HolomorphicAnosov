import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs

/-!
# Zero-dimensional barycentric cells

Source: Hatcher, *Algebraic Topology*, Proposition 2.21(1), printed pp.119–121.
A zero-dimensional vertex tuple has just one index, so every nonempty subface
of every finite-depth descendant has a singleton convex hull.
-/

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- Every zero-dimensional cell has diameter zero, including at depth zero.
Source: Hatcher, *Algebraic Topology*, Proposition 2.21(1), pp.119–121.
Write the cell as the image of an index subset under its descendant tuple.
Every index in `Fin 1` equals zero, so the cell lies in the singleton consisting
of the tuple's value at zero. Its convex hull lies in that same singleton by
convex-hull monotonicity. The diameter of a subsingleton is zero.
No positivity of the subdivision depth is used. -/
theorem iteratedFaces_diam_zero (r : ℕ)
    (s : Finset (EuclideanSpace ℝ (Fin (0 + 1))))
    (hs : s ∈ iteratedFaces (standardVertices 0) r) :
    Metric.diam (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (0 + 1))))) = 0 := by
  let : DecidableEq (EuclideanSpace ℝ (Fin (0 + 1))) := Classical.decEq _
  obtain ⟨p, _, A, _, rfl⟩ := hs
  apply Metric.diam_subsingleton
  apply Set.subsingleton_of_subset_singleton
  refine (convexHull_mono ?_).trans_eq (convexHull_singleton
    (BarycentricMesh.iteratedVertices (standardVertices 0) p 0))
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  simp only [Fin.eq_zero i, Set.mem_singleton_iff]

end HolomorphicAnosov.BarycentricGeometry
