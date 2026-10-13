import HolomorphicAnosov.Paper.Zhang.OriginalRiemannianEDistContraction
import HolomorphicAnosov.Paper.Zhang.NoSurjectiveStrictContraction
import Mathlib.Geometry.Manifold.Riemannian.Basic

open Set Filter Manifold
open scoped ContDiff Manifold ENNReal Topology _root_.Topology Bundle

namespace HolomorphicAnosov.Proposition29Length

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- A smooth self-map of a connected compact nontrivial Riemannian manifold cannot be surjective if
its derivative contracts every tangent vector by a uniform factor less than one. (Zhang, Prop.
2.9) -/
theorem no_surjective_original_metric_contraction
    [T3Space M] [CompactSpace M] [ConnectedSpace M] [Nontrivial M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    (g : M → M) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 g)
    (hsurj : Function.Surjective g) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hbound : ∀ x (v : TangentSpace 𝓘(ℝ, E) x),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v‖ ≤ q * ‖v‖) : False := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  apply no_surjective_strict_contraction g hsurj (NNReal.mk q hq.le)
    (show NNReal.mk q hq.le < 1 from hq1)
  intro x y
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, E)),
    IsRiemannianManifold.out (I := 𝓘(ℝ, E))]
  simpa only [ENNReal.ofReal_eq_coe_nnreal hq.le] using
    original_riemannianEDist_contraction g hg q hq hbound x y


end HolomorphicAnosov.Proposition29Length
