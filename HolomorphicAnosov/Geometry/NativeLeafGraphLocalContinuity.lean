import HolomorphicAnosov.Geometry.GraphAtlasGluing

namespace HolomorphicAnosov
open scoped ContDiff Manifold Topology _root_.Topology
universe u v

/-- The inclusion is continuous at the marked point of a local projection graph chart. -/
theorem native_leaf_graph_local_continuity_at
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M)
    (_A : NativeLeafGraphAtlas (k := k) (d := d) inc)
    {x : L}
    (G : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x) :
    ContinuousAt inc x := by
  have heq : G.ambientChart (inc x) = G.linearModel (G.chart x) := by
    have hgraph := G.graph_equation (by exact (G.chart.extend (complexModel k)).map_source (by simpa only [G.chart.extend_source] using G.point_mem_chart))
    simpa [Function.comp_apply, G.chart.left_inv G.point_mem_chart] using hgraph
  have hcoord : G.linearModel (G.chart x) ∈ G.ambientChart.target := by
    rw [← heq]
    exact G.ambientChart.map_source G.point_mem_ambient
  have hlocal : ∀ᶠ y in 𝓝 x, inc y =
      G.ambientChart.symm (G.linearModel (G.chart y)) := by
    filter_upwards [G.chart.open_source.mem_nhds G.point_mem_chart] with y hy
    have hyambient : inc y ∈ G.ambientChart.source := G.source_inside_ambient hy
    have hyextend : G.chart y ∈ (G.chart.extend (complexModel k)).target :=
      by exact (G.chart.extend (complexModel k)).map_source (by simpa only [G.chart.extend_source] using hy)
    have heq : G.ambientChart (inc y) = G.linearModel (G.chart y) := by
      have hgraph := G.graph_equation hyextend
      simpa [Function.comp_apply, G.chart.left_inv hy] using hgraph
    rw [← G.ambientChart.left_inv hyambient, heq]
  have hchart : ContinuousAt G.chart x := G.chart.continuousAt G.point_mem_chart
  have hlin : ContinuousAt G.linearModel (G.chart x) := G.linearModel.continuous.continuousAt
  have hlinx : ContinuousAt G.linearModel (G.chart x) := G.linearModel.continuous.continuousAt
  have hcomp : ContinuousAt (G.linearModel ∘ G.chart) x := hlinx.comp hchart
  have hamb := G.ambientChart.continuousAt_symm hcoord
  have houter : ContinuousAt (G.ambientChart.symm ∘ G.linearModel) (G.chart x) :=
    hamb.comp hlinx
  have hall : ContinuousAt (G.ambientChart.symm ∘ G.linearModel ∘ G.chart) x :=
    houter.comp hchart
  exact hall.congr_of_eventuallyEq hlocal

end HolomorphicAnosov
