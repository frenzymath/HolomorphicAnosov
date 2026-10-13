import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! A real continuous linear equivalence changes complex chart coordinates to Euclidean real
coordinates. (Zhang, §3, p. 11) -/

namespace HolomorphicAnosov.Theorem12SupportW2

universe u

/-- The real atlas on `X` obtained by postcomposing its complex charts and preferred charts with
`B`. (Zhang, §3, p. 11) -/
@[instance_reducible]
noncomputable def rechart {d n : ℕ} (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X]
    (B : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) X where
  atlas := (fun e : OpenPartialHomeomorph X (ComplexModel d) ↦
    e.transHomeomorph B.toHomeomorph) '' atlas (ComplexModel d) X
  chartAt x := (chartAt (ComplexModel d) x).transHomeomorph B.toHomeomorph
  mem_chart_source x := ChartedSpace.mem_chart_source x
  chart_mem_atlas x := Set.mem_image_of_mem _ (ChartedSpace.chart_mem_atlas x)


end HolomorphicAnosov.Theorem12SupportW2
