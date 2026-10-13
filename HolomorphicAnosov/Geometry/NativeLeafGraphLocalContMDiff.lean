import HolomorphicAnosov.Geometry.GraphAtlasGluing
import HolomorphicAnosov.Geometry.NativeLeafGraphAtlasChartMaximal
import HolomorphicAnosov.Geometry.NativeLeafGraphLocalContinuity

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-- The inclusion is complex-smooth at the marked point of a local projection graph chart in the
glued atlas. -/
theorem native_leaf_graph_local_contMDiffAt
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (A : NativeLeafGraphAtlas (k := k) (d := d) inc)
    {x : L}
    (G : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x) :
    (letI := A.charts
     letI := A.complex_manifold
     ContMDiffAt (complexModel k) (complexModel d) ∞ inc x) := by
  let := A.charts
  let := A.complex_manifold
  have hsource : x ∈ G.chart.source := G.point_mem_chart
  have htgt : inc x ∈ G.ambientChart.source := G.point_mem_ambient
  have hdom := native_leaf_graph_atlas_chart_mem_maximal inc A G
  have hcod := G.ambientChart_mem_complex_atlas
  apply (contMDiffAt_iff_of_mem_maximalAtlas hdom hcod hsource htgt).2
  constructor
  · exact native_leaf_graph_local_continuity_at inc A G
  · have hgraph := G.graph_equation
    have hext : ContDiff ℂ ∞ G.linearModel := G.linearModel.contDiff
    have hext' : ContDiffWithinAt ℂ ∞ G.linearModel
        (Set.range (complexModel k)) (G.chart x) := hext.contDiffWithinAt
    apply hext'.congr_of_eventuallyEq
    · filter_upwards [G.chart.extend_target_mem_nhdsWithin (I := complexModel k) hsource] with u hu
      exact G.graph_equation hu
    · exact G.graph_equation (by
        exact (G.chart.extend (complexModel k)).map_source
          (by simpa only [G.chart.extend_source] using hsource))

end HolomorphicAnosov
