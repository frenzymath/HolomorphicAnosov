import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.MaximalAtlasRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ChartSource
import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
/-- This selector assigns the coordinate coefficients on the chart domain. (Andrews, §8.3) -/
def localChristoffel (nabla : SmoothAffineConnection E M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (hs : Nonempty (chartSource c)) :
    Fin n → Fin n → Fin n → chartSource c → ℝ :=
  Classical.choose
    (((isSmoothAffineConnectionOperator_iff_christoffel nabla.cov).mp nabla.laws).2
      (chartSource c) n b (c.subtypeRestr hs)
      (HolomorphicAnosov.maximalAtlas_subtypeRestr c hc (chartSource c) hs))

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
