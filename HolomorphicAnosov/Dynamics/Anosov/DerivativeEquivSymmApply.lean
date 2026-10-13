import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative
import HolomorphicAnosov.Analysis.MovingOperatorNormStrictLocalBound
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeForwardInverse
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeInverseForward
import HolomorphicAnosov.Geometry.DiffeomorphInverseIterateBasepoint
import HolomorphicAnosov.Geometry.DiffeomorphForwardInverseIterateBasepoint
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov.FixedBlockEstimates.Inverse
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The derivative equivalence's inverse is the derivative of the original inverse. -/
theorem derivative_equiv_symm_apply (g : Diffeomorph I I X X ∞) (x : X)
    (v : TangentSpace I (g x)) :
    (g.mfderivToContinuousLinearEquiv (by simp) x).symm v =
      mfderiv I I g.symm (g x) v := by
  apply (g.mfderivToContinuousLinearEquiv (by simp) x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change v = mfderiv I I g x (mfderiv I I g.symm (g x) v)
  have hh := HolomorphicAnosov.derivative_forward_inverse g (g x) v
  rw [g.symm_apply_apply] at hh
  exact hh.symm

end HolomorphicAnosov.FixedBlockEstimates.Inverse
