import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathSpeed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace HolomorphicAnosov
open Set MeasureTheory
open scoped ContDiff Manifold ENNReal
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace RiemannianPiecewiseSmoothPath
variable {x y : M} (p : RiemannianPiecewiseSmoothPath I x y)
variable (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun z : M ↦ TangentSpace I z))

/-- The length of a piecewise-smooth path is the sum of the speed integrals over its pieces. (Lee,
p.275) -/
noncomputable def length : ℝ :=
  ∑ i : Fin (p.n + 1), ∫ t in p.time i.castSucc..p.time i.succ, p.speed h i t

end RiemannianPiecewiseSmoothPath

end HolomorphicAnosov
