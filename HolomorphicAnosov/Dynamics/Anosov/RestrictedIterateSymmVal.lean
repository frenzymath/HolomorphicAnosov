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
import HolomorphicAnosov.Dynamics.Anosov.DerivativeEquivSymmApply

noncomputable section
namespace HolomorphicAnosov.FixedBlockEstimates.Inverse
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The restricted inverse has the actual original inverse-iterate derivative as its value. -/
theorem restricted_iterate_symm_val (g : Diffeomorph I I X X ∞)
    (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (x : X) (v : P (((g : X → X)^[n]) x)) :
    ((restrictedIterateDerivative g P hP n x).symm v).val =
      mfderiv I I ((g.symm : X → X)^[n]) (((g : X → X)^[n]) x) v.val := by
  change (((realIterate I g n).mfderivToContinuousLinearEquiv (by simp) x).symm
    v.val) = _
  exact derivative_equiv_symm_apply (realIterate I g n) x v.val

end HolomorphicAnosov.FixedBlockEstimates.Inverse
