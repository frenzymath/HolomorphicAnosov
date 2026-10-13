import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs
import HolomorphicAnosov.Topology.BarycentricHullBridge
import HolomorphicAnosov.Topology.BarycentricGeometry.EuclideanSimplexHull

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- Every finite-depth cell has diameter at most the fixed-dimensional contraction
factor to that depth times the original diameter.
Source: Hatcher, Algebraic Topology, Proposition 2.21(1), pp.120–121.
Proof: finite vertex hulls are bounded, so their diameter bounds all vertex
pairs. Apply the iterated mesh estimate and diameter monotonicity to a subface. -/
theorem iteratedFaces_diam_le (n r : ℕ)
    (s : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (hs : s ∈ iteratedFaces (standardVertices n) r) :
    Metric.diam (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≤
      ((n : ℝ) / ((n : ℝ) + 1)) ^ r * Metric.diam (euclideanSimplex n) := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  obtain ⟨p, hp, A, hA, rfl⟩ := hs
  have hb : Bornology.IsBounded (euclideanSimplex n) := by
    rw [euclideanSimplex_eq_convexHull]
    exact ((Set.finite_range _).isCompact_convexHull ℝ).isBounded
  have hv (i : Fin (n + 1)) : standardVertices n i ∈ euclideanSimplex n := by
    rw [euclideanSimplex_eq_convexHull]
    exact subset_convexHull ℝ _ ⟨i, rfl⟩
  have hd := ((BarycentricMesh.iterated_mesh_contraction n (standardVertices n)).2.2.1
    (Metric.diam (euclideanSimplex n))
    (fun i j ↦ Metric.dist_le_diam_of_mem hb (hv i) (hv j)) p).2
  rw [barycentricMesh_hull_eq_convexHull_range, hp] at hd
  refine le_trans (Metric.diam_mono ?_ ?_) hd
  · apply convexHull_mono
    rintro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, rfl⟩
  · exact ((Set.finite_range _).isCompact_convexHull ℝ).isBounded

end HolomorphicAnosov.BarycentricGeometry

