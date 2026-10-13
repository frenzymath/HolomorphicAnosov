import HolomorphicAnosov.Geometry.GraphAtlasGluing

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-- Every graph chart in the glued atlas belongs to its maximal complex atlas. -/
theorem native_leaf_graph_atlas_chart_mem_maximal
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M)
    (A : NativeLeafGraphAtlas (k := k) (d := d) inc)
    {x : L}
    (G : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x) :
    (letI := A.charts
     letI := A.complex_manifold
     G.chart ∈ IsManifold.maximalAtlas (complexModel k) ∞ L) := by
  let := A.charts
  let := A.complex_manifold
  exact IsManifold.subset_maximalAtlas (A.graph_chart_mem x G)

end HolomorphicAnosov
