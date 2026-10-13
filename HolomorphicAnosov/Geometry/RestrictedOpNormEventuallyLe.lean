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
import HolomorphicAnosov.Geometry.RestrictedOpNormEventuallyLt

noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.FixedBlockEstimates.Native
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- If a restricted iterate derivative has operator norm less than `c` at a point, its norm is
bounded by a nonnegative constant `q < c` throughout a neighborhood. -/
theorem restricted_opNorm_eventually_le
    (P : ContinuousRealTangentSubbundle 𝓘(ℝ, E) M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hP : ∀ x, (P.toDistribution x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x).toLinearMap =
      P.toDistribution (F x)) (k : ℕ) (x : M) {c : ℝ} :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
      ⟨g.toRiemannianMetric⟩
    ‖(restrictedIterateDerivative F P.toDistribution hP k x).toContinuousLinearMap‖ < c →
    ∃ q : ℝ, 0 ≤ q ∧ q < c ∧ ∀ᶠ y in 𝓝 x,
      ‖(restrictedIterateDerivative F P.toDistribution hP k y).toContinuousLinearMap‖ ≤ q := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
    ⟨g.toRiemannianMetric⟩
  intro hc
  obtain ⟨q, hq, hqc⟩ := exists_between hc
  exact ⟨q, (norm_nonneg
    (restrictedIterateDerivative F P.toDistribution hP k x).toContinuousLinearMap).trans hq.le, hqc,
    (restricted_opNorm_eventually_lt P g F hP k x hq).mono fun _ hy ↦ hy.le⟩

end HolomorphicAnosov.FixedBlockEstimates.Native
