import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPath

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold ENNReal
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace RiemannianPiecewiseSmoothPath
variable {x y : M} (p : RiemannianPiecewiseSmoothPath I x y)

/-- The closed parameter interval of a smooth piece. (Lee, p.275) -/
def pieceInterval (i : Fin (p.n + 1)) : Set ℝ :=
  Icc (p.time i.castSucc) (p.time i.succ)

end RiemannianPiecewiseSmoothPath

end HolomorphicAnosov
