import HolomorphicAnosov.Geometry.GraphAtlasGluing
import HolomorphicAnosov.Geometry.ComplexLinearSplitNormalForm
import HolomorphicAnosov.Geometry.NativeLeafGraphAtlasChartMaximal

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-- The inclusion is a complex immersion at the marked source point of a local projection graph
chart. -/
theorem native_leaf_graph_local_immersion_at
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M)
    (A : NativeLeafGraphAtlas (k := k) (d := d) inc)
    {x : L}
    (G : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x) :
    (letI := A.charts
     letI := A.complex_manifold
     Manifold.IsImmersionAt (complexModel k) (complexModel d) ∞ inc x) := by
  let := A.charts
  let := A.complex_manifold
  obtain ⟨F, e, he⟩ := complex_linear_split_normal_form
    G.linearModel G.linearModel_injective
  apply Manifold.IsImmersionAt.mk_of_charts e G.chart G.ambientChart
  · exact G.point_mem_chart
  · exact G.point_mem_ambient
  · exact native_leaf_graph_atlas_chart_mem_maximal inc A G
  · exact G.ambientChart_mem_complex_atlas
  · exact G.source_inside_ambient
  · intro u hu
    rw [G.graph_equation hu]
    exact (he u).symm

end HolomorphicAnosov
