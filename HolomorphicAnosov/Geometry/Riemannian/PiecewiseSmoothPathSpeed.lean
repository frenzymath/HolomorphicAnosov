import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathVelocity

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold ENNReal
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace RiemannianPiecewiseSmoothPath
variable {x y : M} (p : RiemannianPiecewiseSmoothPath I x y)
variable (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun z : M ↦ TangentSpace I z))

/-- The speed of a smooth piece is the square root of the supplied metric evaluated on its velocity
twice. (Lee, p.275) -/
noncomputable def speed (i : Fin (p.n + 1)) (t : ℝ) : ℝ :=
  Real.sqrt (h.inner (p.piece i t) (p.velocity i t) (p.velocity i t))

end RiemannianPiecewiseSmoothPath

end HolomorphicAnosov
