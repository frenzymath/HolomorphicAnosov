import HolomorphicAnosov.Geometry.HermitianChartDensitySmooth
import HolomorphicAnosov.Geometry.HermitianChartDensityPositive

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- Once the coordinate gluing identity is established, the actual preferred form is smooth and positive. (Demailly, VI §4.) -/
theorem hermitian_volume_positive_of_chart_identity
    [IsManifold (complexModel d) ∞ X]
    (h : HermitianTangentMetricCore d X) (hh : IsSmoothHermitianTangentMetric h)
    (hchart : ∀ e : OpenPartialHomeomorph X (ComplexModel d),
      e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      Set.EqOn (realTangentTopFormChartCoefficient (hermitianMetricPreferredTopForm h) e)
        (hermitianMetricChartVolumeDensity h e) e.target) :
    IsSmoothPositiveRealTangentTopForm (hermitianMetricPreferredTopForm h) := by
  intro e he
  refine ⟨(hermitian_chart_density_smooth h hh e he).congr (hchart e he), ?_⟩
  intro z hz
  rw [hchart e he hz]
  exact hermitian_chart_density_pos h e he z hz

end HolomorphicAnosov

