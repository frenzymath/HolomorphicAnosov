import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothRiemannianEDist

namespace HolomorphicAnosov
open Set MeasureTheory
open scoped ContDiff Manifold ENNReal
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem piecewiseSmoothRiemannianEDist_le_path
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E
      (fun z : M ↦ TangentSpace I z))
    {x y : M} (p : RiemannianPiecewiseSmoothPath I x y) :
    piecewiseSmoothRiemannianEDist h x y ≤ ENNReal.ofReal (p.length h) := by
  unfold piecewiseSmoothRiemannianEDist
  exact iInf_le (fun q : RiemannianPiecewiseSmoothPath I x y ↦ ENNReal.ofReal (q.length h)) p

end HolomorphicAnosov

