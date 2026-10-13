import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataG8


open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open TopologicalSpace Set

namespace HolomorphicAnosov

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The supplied smooth tensor estimates become bundle-norm estimates under the associated Riemannian tangent-bundle instance. This is a direct norm identity. (Zhang, p. 1; HPS, (2.8)–(2.9).) -/
theorem tensorAnosovBounds_to_bundle
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (S : InvariantRealTangentSplitting f)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (h : Nonempty (TensorAnosovBounds f S g)) :
    let : Bundle.RiemannianBundle
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
    BundleAnosovBounds f S := by
  let : Bundle.RiemannianBundle
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨b⟩ := h
  have hi (x : M) (v w : TangentSpace 𝓘(ℝ, E) x) :
      inner ℝ v w = g.inner x v w := rfl
  refine ⟨b.C, b.lambda, b.C_pos, b.lambda_pos, b.lambda_lt_one, ?_, ?_⟩
  · intro n x v hv
    simpa only [norm_eq_sqrt_real_inner, hi] using b.stable n x v hv
  · intro n x v hv
    simpa only [norm_eq_sqrt_real_inner, hi] using b.unstable n x v hv

end HolomorphicAnosov
