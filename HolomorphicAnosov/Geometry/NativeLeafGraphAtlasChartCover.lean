import HolomorphicAnosov.Geometry.GraphAtlasGluing

namespace HolomorphicAnosov
universe u v

/-- The selected local projection graph charts cover the source carrier and belong to the glued
complex atlas. -/
theorem native_leaf_graph_atlas_chart_cover
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M)
    (A : NativeLeafGraphAtlas (k := k) (d := d) inc)
    (hlocal : ∀ x : L,
      Nonempty (NativeLeafLocalProjectionGraph (k := k) (d := d) inc x)) :
    ∀ z : L, ∃ x : L,
      ∃ G : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x,
        G.chart ∈ A.charts.atlas ∧ z ∈ G.chart.source := by
  intro z
  rcases hlocal z with ⟨G⟩
  exact ⟨z, G, A.graph_chart_mem z G, G.point_mem_chart⟩

end HolomorphicAnosov
