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
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateSymmVal

noncomputable section
namespace HolomorphicAnosov.FixedBlockEstimates.Inverse
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
variable [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x)]

/-- At the literal forward endpoint, the inverse block operator norm controls every vector. -/
theorem inverse_iterate_norm_le_at_forward (g : Diffeomorph I I X X ∞)
    (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (x : X) (v : TangentSpace I (((g : X → X)^[n]) x))
    (hv : v ∈ P (((g : X → X)^[n]) x)) :
    ‖mfderiv I I ((g.symm : X → X)^[n]) (((g : X → X)^[n]) x) v‖ ≤
      ‖(restrictedIterateDerivative g P hP n x).symm.toContinuousLinearMap‖ * ‖v‖ := by
  have h := (restrictedIterateDerivative g P hP n x).symm.toContinuousLinearMap.le_opNorm
    (⟨v, hv⟩ : P (((g : X → X)^[n]) x))
  have hval := restricted_iterate_symm_val g P hP n x (⟨v, hv⟩ : P (((g : X → X)^[n]) x))
  have hn := congrArg (fun w : TangentSpace I x ↦ ‖w‖) hval
  change ‖((restrictedIterateDerivative g P hP n x).symm ⟨v, hv⟩).val‖ ≤ _ at h
  rw [hn] at h
  have hnorm := congrArg (fun z : X ↦ (fun w : E ↦ @norm (TangentSpace I z) inferInstance w))
    (HolomorphicAnosov.inverse_iterate_basepoint g n x)
  exact (congrFun hnorm
    (mfderiv I I ((g.symm : X → X)^[n]) (((g : X → X)^[n]) x) v)).le.trans h

end HolomorphicAnosov.FixedBlockEstimates.Inverse
