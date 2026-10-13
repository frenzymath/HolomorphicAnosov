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
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.FixedBlockEstimates.Native
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The Riemannian norm of a continuous tangent-valued family is continuous. (Zhang, p.1) -/
theorem continuous_original_norm
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {B : Type*} [TopologicalSpace B] (b : B → M)
    (v : ∀ p : B, TangentSpace 𝓘(ℝ, E) (b p))
    (hv : Continuous (fun p ↦ (⟨b p, v p⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toRiemannianMetric⟩
    Continuous (fun p ↦ ‖v p‖) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  simpa only [norm_eq_sqrt_real_inner] using (hv.inner_bundle hv).sqrt

end HolomorphicAnosov.FixedBlockEstimates.Native
