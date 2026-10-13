import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathLength

namespace HolomorphicAnosov
open Set MeasureTheory
open scoped ContDiff Manifold ENNReal
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The infimum of the lengths of finite piecewise-smooth paths from `x` to `y`, as an extended
nonnegative real number, for the supplied metric. (Lee, p.277; Prop. 11.20, pp.278–279) -/
noncomputable def piecewiseSmoothRiemannianEDist
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun z : M ↦ TangentSpace I z))
    (x y : M) : ℝ≥0∞ :=
  ⨅ p : RiemannianPiecewiseSmoothPath I x y, ENNReal.ofReal (p.length h)

end HolomorphicAnosov
