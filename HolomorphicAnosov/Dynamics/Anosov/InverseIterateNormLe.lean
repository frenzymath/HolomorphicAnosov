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
import HolomorphicAnosov.Dynamics.Anosov.InverseIterateNormLeOfBasepoint

noncomputable section
namespace HolomorphicAnosov.FixedBlockEstimates.Inverse
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
variable [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x)]

/-- At an arbitrary original point the correct forward block base is its inverse iterate. -/
theorem inverse_iterate_norm_le (g : Diffeomorph I I X X ∞)
    (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (x : X) (v : TangentSpace I x) (hv : v ∈ P x) :
    ‖mfderiv I I ((g.symm : X → X)^[n]) x v‖ ≤
      ‖(restrictedIterateDerivative g P hP n (((g.symm : X → X)^[n]) x)).symm.toContinuousLinearMap‖ * ‖v‖ :=
  inverse_iterate_norm_le_of_basepoint g P hP n _ x
    (HolomorphicAnosov.forward_iterate_inverse_basepoint g n x) v hv

end HolomorphicAnosov.FixedBlockEstimates.Inverse
