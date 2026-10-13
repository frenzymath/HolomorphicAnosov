import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPath
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace H M] [ChartedSpace H' M'] [IsManifold I ∞ M] [IsManifold I' ∞ M']

/-- The image of a piecewise-smooth path under a smooth map, with the same partition. (Lee, p.275)
-/
def RiemannianPiecewiseSmoothPath.map {x y : M}
    (p : RiemannianPiecewiseSmoothPath I x y) (F : M → M')
    (hF : ContMDiff I I' ∞ F) : RiemannianPiecewiseSmoothPath I' (F x) (F y) where
  n := p.n
  time := p.time
  time_strictMono := p.time_strictMono
  time_zero := p.time_zero
  time_one := p.time_one
  piece i := F ∘ p.piece i
  piece_smooth i := hF.comp_contMDiffOn (p.piece_smooth i)
  source := congrArg F p.source
  target := congrArg F p.target
  junction i := congrArg F (p.junction i)

end HolomorphicAnosov
