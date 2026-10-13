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
import HolomorphicAnosov.Dynamics.Anosov.InverseDistributionInvariant
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateSymmVal

noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.FixedBlockEstimates.Native
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The operator norm of the inverse restricted iterate derivative equals that of the restricted
inverse iterate derivative at the forward endpoint. -/
theorem restricted_inverse_opNorm_at_forward
    (P : RealTangentDistribution 𝓘(ℝ, E) M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hP : ∀ x, (P x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x).toLinearMap = P (F x))
    (k : ℕ) (x : M) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
      ⟨g.toRiemannianMetric⟩
    ‖(restrictedIterateDerivative F P hP k x).symm.toContinuousLinearMap‖ =
      ‖(restrictedIterateDerivative F.symm P
        (FixedBlockEstimates.Inverse.inverse_distribution_invariant F P hP) k
          (((F : M → M)^[k]) x)).toContinuousLinearMap‖ := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
    ⟨g.toRiemannianMetric⟩
  let A := (restrictedIterateDerivative F P hP k x).symm.toContinuousLinearMap
  let B := (restrictedIterateDerivative F.symm P
    (FixedBlockEstimates.Inverse.inverse_distribution_invariant F P hP) k
      (((F : M → M)^[k]) x)).toContinuousLinearMap
  have hn (v : P (((F : M → M)^[k]) x)) : ‖A v‖ = ‖B v‖ := by
    change ‖((restrictedIterateDerivative F P hP k x).symm v).val‖ =
      ‖(restrictedIterateDerivative F.symm P
        (FixedBlockEstimates.Inverse.inverse_distribution_invariant F P hP) k
          (((F : M → M)^[k]) x) v).val‖
    rw [FixedBlockEstimates.Inverse.restricted_iterate_symm_val]
    have hnorm := congrArg (fun z : M ↦ (fun w : E ↦
      @norm (TangentSpace 𝓘(ℝ, E) z) inferInstance w))
      (HolomorphicAnosov.inverse_iterate_basepoint F k x)
    exact (congrFun hnorm
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((F.symm : M → M)^[k])
        (((F : M → M)^[k]) x) v.val)).symm
  apply le_antisymm
  · apply A.opNorm_le_bound (norm_nonneg B)
    intro v
    rw [hn]
    exact B.le_opNorm v
  · apply B.opNorm_le_bound (norm_nonneg A)
    intro v
    rw [← hn]
    exact A.le_opNorm v

end HolomorphicAnosov.FixedBlockEstimates.Native
