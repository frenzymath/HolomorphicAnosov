import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.Coefficients
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
/-- The extended coefficient function is arbitrary off the chart source. (Andrews, §8.3) -/
def extendedLocalChristoffel (nabla : SmoothAffineConnection E M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (i j k : Fin n) (p : M) : ℝ := by
  classical
  exact if hp : p ∈ c.source then
    localChristoffel nabla b c hc ⟨⟨p, hp⟩⟩ i j k ⟨p, hp⟩
  else 0

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
