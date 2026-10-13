import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold ENNReal
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A finite piecewise-smooth path from `x` to `y`, with a strict partition of `[0, 1]` and smooth
pieces agreeing at adjacent endpoints. (Lee, p.275) -/
structure RiemannianPiecewiseSmoothPath (I : ModelWithCorners ℝ E H) (x y : M) where
  /-- One less than the number of smooth pieces. -/
  n : ℕ
  /-- The finite real parameter partition. -/
  time : Fin (n + 2) → ℝ
  /-- The partition times are strictly increasing. -/
  time_strictMono : StrictMono time
  /-- The first partition time is zero. -/
  time_zero : time 0 = 0
  /-- The final partition time is one. -/
  time_one : time (Fin.last (n + 1)) = 1
  /-- The smooth pieces, represented by maps defined on all real times. -/
  piece : Fin (n + 1) → ℝ → M
  /-- Each piece is smooth on its closed parameter interval. -/
  piece_smooth : ∀ i, ContMDiffOn 𝓘(ℝ) I ∞ (piece i)
    (Icc (time i.castSucc) (time i.succ))
  /-- The first piece starts at `x`. -/
  source : piece 0 0 = x
  /-- The last piece ends at `y`. -/
  target : piece (Fin.last n) 1 = y
  /-- Adjacent pieces agree at their common partition time. -/
  junction : ∀ i : Fin n,
    piece i.castSucc (time i.succ.castSucc) = piece i.succ (time i.succ.castSucc)

end HolomorphicAnosov
