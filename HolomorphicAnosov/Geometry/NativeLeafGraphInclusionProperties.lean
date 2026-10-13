import HolomorphicAnosov.Geometry.GraphAtlasToUpgrade
import HolomorphicAnosov.Geometry.NativeLeafGraphAtlasChartCover
import HolomorphicAnosov.Geometry.NativeLeafGraphAtlasChartMaximal
import HolomorphicAnosov.Geometry.NativeLeafGraphLocalImmersion
import HolomorphicAnosov.Geometry.NativeLeafGraphLocalContinuity
import HolomorphicAnosov.Geometry.NativeLeafGraphLocalContMDiff

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-- The inclusion is holomorphic and is a complex immersion at every point in the glued intrinsic
graph atlas. -/
theorem native_leaf_graph_inclusion_properties
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (A : NativeLeafGraphAtlas (k := k) (d := d) inc)
    (hlocal : ∀ x : L,
      Nonempty (NativeLeafLocalProjectionGraph (k := k) (d := d) inc x)) :
    (letI := A.charts
     ContMDiff (complexModel k) (complexModel d) ∞ inc) ∧
    (letI := A.charts
     ∀ z : L, Manifold.IsImmersionAt (complexModel k) (complexModel d) ∞ inc z) := by
  let := A.charts
  let := A.complex_manifold
  have hmdiff : ∀ z : L, ContMDiffAt (complexModel k) (complexModel d) ∞ inc z := by
    intro z
    rcases hlocal z with ⟨G⟩
    exact native_leaf_graph_local_contMDiffAt inc A G
  have himm : ∀ z : L, Manifold.IsImmersionAt (complexModel k) (complexModel d) ∞ inc z := by
    intro z
    rcases hlocal z with ⟨G⟩
    exact native_leaf_graph_local_immersion_at inc A G
  exact ⟨fun z => hmdiff z, himm⟩

end HolomorphicAnosov
