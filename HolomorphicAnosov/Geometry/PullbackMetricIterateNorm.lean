import HolomorphicAnosov.Geometry.SmoothMetricPullback
import HolomorphicAnosov.Targets.Theorem12Support.SmoothSemiconjugacy.derivative_iterate_intertwining

/-! Conjugate iterated differentials preserve corresponding vector lengths in the inverse-pullback
metric. (Gallier–Quaintance, Defs. 14.4–14.5, p. 415; Prop. 18.5, pp. 534–535) -/

open scoped ContDiff Manifold Bundle
namespace HolomorphicAnosov
universe u v
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- In the inverse-pullback metric, semiconjugate iterated differentials have equal lengths on
corresponding vectors. (Gallier–Quaintance, Defs. 14.4–14.5, p. 415; Prop. 18.5, pp. 534–535) -/
theorem smoothMetricPullback_iterate_norm
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (metric : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {f : M → M} {g : N → N}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ g)
    (h : Function.Semiconj e f g) (n : ℕ) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨metric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y) :=
      ⟨(smoothMetricPullback e metric).toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (g^[n]) (e x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x v)‖ =
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (f^[n]) x v‖ := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨metric.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y) :=
    ⟨(smoothMetricPullback e metric).toRiemannianMetric⟩
  have hval := congrArg (fun L ↦ L v)
    (Theorem12SupportW2.derivative_iterate_intertwining e hf hg h n x)
  have hnorm := congrArg
    (fun w : TangentSpace 𝓘(ℝ, F) (e ((f^[n]) x)) ↦ ‖w‖) hval
  have hpoint := congrArg
    (fun y : N ↦ (fun w : F ↦ @norm (TangentSpace 𝓘(ℝ, F) y) inferInstance w))
    ((h.iterate_right n) x)
  calc
    _ = @norm (TangentSpace 𝓘(ℝ, F) (e ((f^[n]) x))) inferInstance
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (g^[n]) (e x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x v)) := (congrFun hpoint _).symm
    _ = ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e ((f^[n]) x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (f^[n]) x v)‖ := hnorm
    _ = _ := smoothMetricPullback_norm_forward e metric _ _

end HolomorphicAnosov
