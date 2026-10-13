import HolomorphicAnosov.Geometry.SmoothMetricPullbackCore
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! This file constructs the smooth metric obtained by pulling a Riemannian metric back along a finite-dimensional diffeomorphism and proves its defining length identities (Gallier–Quaintance, Definitions 14.4–14.5 and Prop. 18.5). -/

open scoped ContDiff Manifold Topology _root_.Topology
open Bundle Bornology ContinuousLinearMap

universe u v

namespace HolomorphicAnosov

noncomputable section


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- The pullback metric `(e.symm)*g` on the receiving manifold is smooth (Gallier–Quaintance, Definition 14.4). -/
def smoothMetricPullback [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
      (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y) :=
  transportedContMDiffRiemannianMetric e g

/-- The pullback metric evaluates by applying the inverse differential in both arguments (Gallier–Quaintance, Definition 14.4). -/
theorem smoothMetricPullback_inner [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (y : N) (v w : TangentSpace 𝓘(ℝ, F) y) :
    (smoothMetricPullback e g).inner y v w =
      g.inner (e.symm y) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e.symm y v)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e.symm y w) := rfl

open scoped Bundle in
/-- The pullback metric preserves lengths under the inverse differential (Gallier–Quaintance, Definitions 14.4–14.5). -/
theorem smoothMetricPullback_norm_inverse [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (y : N) (w : TangentSpace 𝓘(ℝ, F) y) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y) :=
      ⟨(smoothMetricPullback e g).toRiemannianMetric⟩
    ‖w‖ = ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e.symm y w‖ :=
  transported_norm_inverse e g y w

open scoped Bundle in
/-- The pullback metric preserves lengths under the forward differential (Gallier–Quaintance, Definition 14.5). -/
theorem smoothMetricPullback_norm_forward [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y) :=
      ⟨(smoothMetricPullback e g).toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x v‖ = ‖v‖ :=
  transported_norm_forward e g x v


end
end HolomorphicAnosov
