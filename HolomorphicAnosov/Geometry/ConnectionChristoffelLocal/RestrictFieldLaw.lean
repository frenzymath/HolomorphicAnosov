import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.InclusionDerivative
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.RestrictField
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
/-- The restricted field satisfies the relation required by `SmoothAffineConnection.laws`. (Andrews, §8.3) -/
theorem restrictField_isRestriction {U V : Opens M} (hUV : U ≤ V)
    (X : LocalSmoothVectorField E M V) :
    LocalSmoothVectorField.IsRestriction hUV X (restrictField hUV X) := by
  intro p
  exact (inclusion_mfderiv_isInvertible hUV p).self_apply_inverse (X (Opens.inclusion hUV p))

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
