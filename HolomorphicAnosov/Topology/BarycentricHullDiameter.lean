import HolomorphicAnosov.Topology.BarycentricIteratedMeshDefs
import Mathlib.Analysis.Normed.Module.Convex

noncomputable section
namespace HolomorphicAnosov.BarycentricMesh

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- The transported affine hull has diameter bounded by the pairwise vertex bound.
Source: Hatcher, Algebraic Topology, Proposition 2.21 proof (1), printed p.120.
For two hull points, translate to vector coordinates at w(0). Mathlib's
`convexHull_exists_dist_ge2` bounds their distance by that of two translated
vertices. Translation is an isometry, so the hypothesis bounds this by C.
The self-distance bound gives C ≥ 0; the metric diameter criterion then applies. -/
theorem hull_diam_le_of_vertex_dist {n : ℕ} :
    ∀ (w : Fin (n + 1) → E) (C : ℝ),
      (∀ i j : Fin (n + 1), dist (w i) (w j) ≤ C) →
      Metric.diam (hull w) ≤ C := by
  intro w C hw
  have hC : 0 ≤ C := le_trans dist_nonneg (hw 0 0)
  apply Metric.diam_le_of_forall_dist_le hC
  intro x hx y hy
  rcases hx with ⟨zx, hzx, rfl⟩
  rcases hy with ⟨zy, hzy, rfl⟩
  rcases convexHull_exists_dist_ge2 hzx hzy with
    ⟨a, ha, b, hb, hab⟩
  rcases ha with ⟨i, rfl⟩
  rcases hb with ⟨j, rfl⟩
  calc
    dist (zx +ᵥ w 0) (zy +ᵥ w 0) =
        dist zx zy := dist_vadd_cancel_right _ _ _
    _ ≤ dist (w i -ᵥ w 0) (w j -ᵥ w 0) := hab
    _ = dist (w i) (w j) := dist_vsub_cancel_right _ _ _
    _ ≤ C := hw i j
end HolomorphicAnosov.BarycentricMesh
