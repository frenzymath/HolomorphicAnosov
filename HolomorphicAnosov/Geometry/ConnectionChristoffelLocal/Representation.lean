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
/-- This predicate records the coordinate representation equation for the connection. (Andrews, Prop. 8.3.1) -/
def RepresentsCoefficients (nabla : SmoothAffineConnection E M) (U : Opens M)
    {n : ℕ} (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (Γ : Fin n → Fin n → Fin n → U → ℝ) : Prop :=
  ∀ (X Y : LocalSmoothVectorField E M U) (p : U), p ∈ c.source → ∀ k,
    (nabla.cov U X Y).tangentCoefficient b c p k =
      (∑ i, X.tangentCoefficient b c p i *
        fderiv ℝ (LocalSmoothVectorField.coordinateCoefficient b c Y k) (c p) (b i)) +
      ∑ i, ∑ j, X.tangentCoefficient b c p i *
        Y.tangentCoefficient b c p j * Γ i j k p

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
