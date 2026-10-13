import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs
import HolomorphicAnosov.Topology.Barycentric.mem_convexHull_range_iff_weights

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- The Euclidean carrier is the convex hull of its standard coordinate vertices. -/
theorem euclideanSimplex_eq_convexHull (n : ℕ) :
    euclideanSimplex n = convexHull ℝ (range (standardVertices n)) := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
  let S : Set (Fin (n + 1) → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1}
  have hweights :
      range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) ↦
        fun i ↦ t.weights i) = S := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext x
    simp [S]
  have hsimplex : euclideanSimplex n = e '' S := by
    rw [← hweights, ← range_comp]
    rfl
  have hstandard : S =
      convexHull ℝ (range (fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ))) := by
    ext x
    rw [mem_convexHull_range_iff_weights]
    constructor
    · intro hx
      refine ⟨x, hx.1, hx.2, ?_⟩
      ext i
      simp [Pi.single_apply, smul_eq_mul]
    · rintro ⟨w, hw, hsum, heq⟩
      have hwx : w = x := by
        simpa [Pi.single_apply, funext_iff] using congrFun heq
      change (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1
      rw [← hwx]
      exact ⟨hw, hsum⟩
  rw [hsimplex, hstandard]
  change e.toLinearMap '' convexHull ℝ (range (fun i ↦ Pi.single i 1)) = _
  rw [e.toLinearMap.image_convexHull, ← range_comp]
  congr 1

end HolomorphicAnosov.BarycentricGeometry

