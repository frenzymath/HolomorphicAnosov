import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.RealTangentTopForm

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The actual Hermitian coefficient determinant in a complex coordinate frame. (Demailly, VI §4.) -/
noncomputable def hermitianMetricChartVolumeDensity (h : HermitianTangentMetricCore d X)
    (e : OpenPartialHomeomorph X (ComplexModel d)) (z : ComplexModel d) : ℝ :=
  (Matrix.det fun i j => hermitianTangentChartCoefficient h e i j z).re

/-- A preferred-chart candidate containing actual continuous native tangent forms. (Demailly, VI §4.) -/
noncomputable def hermitianMetricPreferredTopForm (h : HermitianTangentMetricCore d X) :
    RealTangentTopForm d X :=
  fun x =>
    let e := chartAt (ComplexModel d) x
    hermitianMetricChartVolumeDensity h e (e x) • realTangentCoordinateTopFormAt e x

end HolomorphicAnosov
