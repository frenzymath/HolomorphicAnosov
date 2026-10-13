import HolomorphicAnosov.Geometry.RealTangentTopForm

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- Positive top forms are nonzero at every point. (Demailly, VI (4.2)) -/
theorem positive_topForm_ne_zero [IsManifold (complexModel d) ∞ X]
    (ν : RealTangentTopForm d X) (hν : IsSmoothPositiveRealTangentTopForm ν) (x : X) :
    ν x ≠ 0 := by
  let e := chartAt (ComplexModel d) x
  have hx : x ∈ e.source := ChartedSpace.mem_chart_source x
  have hz := (hν e (IsManifold.chart_mem_maximalAtlas x)).2 (e x) (e.map_source hx)
  rw [realTangentTopFormChartCoefficient, e.left_inv hx] at hz
  intro heq
  rw [heq] at hz
  exact (lt_irrefl (0 : ℝ)) hz


end HolomorphicAnosov
