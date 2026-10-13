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
import HolomorphicAnosov.Dynamics.Anosov.InverseIterateNormLeAtForward

noncomputable section
namespace HolomorphicAnosov.FixedBlockEstimates.Inverse
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
variable [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x)]

/-- An explicit original basepoint equality transports the endpoint estimate, without
identifying or replacing either metric fibre. -/
theorem inverse_iterate_norm_le_of_basepoint (g : Diffeomorph I I X X ∞)
    (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (x y : X) (hxy : ((g : X → X)^[n]) x = y)
    (v : TangentSpace I y) (hv : v ∈ P y) :
    ‖mfderiv I I ((g.symm : X → X)^[n]) y v‖ ≤
      ‖(restrictedIterateDerivative g P hP n x).symm.toContinuousLinearMap‖ * ‖v‖ := by
  subst y
  exact inverse_iterate_norm_le_at_forward g P hP n x v hv

end HolomorphicAnosov.FixedBlockEstimates.Inverse
