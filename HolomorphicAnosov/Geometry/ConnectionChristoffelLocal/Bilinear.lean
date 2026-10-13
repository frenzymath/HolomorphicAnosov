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
/-- This construction reconstructs a Christoffel array from its coordinate coefficients. (Andrews, §8.3) -/
def coefficientBilinear {P : Type*} {n : ℕ} (b : Basis (Fin n) ℝ E)
    (Γ : Fin n → Fin n → Fin n → P → ℝ) (p : P) (u v : E) : E :=
  ∑ k, (∑ i, ∑ j, b.repr u i * b.repr v j * Γ i j k p) • b k

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
