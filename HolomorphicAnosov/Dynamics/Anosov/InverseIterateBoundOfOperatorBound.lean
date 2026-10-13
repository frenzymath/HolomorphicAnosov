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
import HolomorphicAnosov.Dynamics.Anosov.InverseIterateNormLe

noncomputable section
namespace HolomorphicAnosov.FixedBlockEstimates.Inverse
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
variable [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x)]

/-- The original inverse-iterate estimate can use the common compact scalar bound. -/
theorem inverse_iterate_bound_of_operator_bound (g : Diffeomorph I I X X ∞)
    (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (theta : ℝ)
    (hbound : ∀ y,
      ‖(restrictedIterateDerivative g P hP n y).symm.toContinuousLinearMap‖ ≤ theta)
    (x : X) (v : TangentSpace I x) (hv : v ∈ P x) :
    ‖mfderiv I I ((g.symm : X → X)^[n]) x v‖ ≤ theta * ‖v‖ :=
  (inverse_iterate_norm_le g P hP n x v hv).trans
    (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg v))

end HolomorphicAnosov.FixedBlockEstimates.Inverse
