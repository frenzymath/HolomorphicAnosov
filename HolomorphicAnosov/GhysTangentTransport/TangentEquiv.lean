import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.GhysTangentTransport.DerivativeLeftInverse
import HolomorphicAnosov.GhysTangentTransport.DerivativeRightInverse

open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.GhysTangentTransport
noncomputable section
universe u v
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  (e : Diffeomorph I J M N ∞)

/-- The derivative at a point is a continuous linear equivalence between the corresponding tangent spaces. -/
def tangentEquiv (x : M) : TangentSpace I x ≃L[ℝ] TangentSpace J (e x) :=
  ContinuousLinearEquiv.equivOfInverse (mfderiv I J e x)
    (mfderiv J I e.symm (e x)) (derivative_leftInverse e x)
    (derivative_rightInverse e x)


end
end HolomorphicAnosov.GhysTangentTransport
