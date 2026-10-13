import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathInterval
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold ENNReal
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace RiemannianPiecewiseSmoothPath
variable {x y : M} (p : RiemannianPiecewiseSmoothPath I x y)

/-- The velocity of a smooth piece is its manifold derivative within its closed parameter interval,
evaluated on the unit time vector. (Lee, p.275) -/
noncomputable def velocity (i : Fin (p.n + 1)) (t : ℝ) :
    TangentSpace I (p.piece i t) :=
  mfderivWithin 𝓘(ℝ) I (p.piece i) (p.pieceInterval i) t
    (show TangentSpace 𝓘(ℝ) t from (1 : ℝ))

end RiemannianPiecewiseSmoothPath

end HolomorphicAnosov
