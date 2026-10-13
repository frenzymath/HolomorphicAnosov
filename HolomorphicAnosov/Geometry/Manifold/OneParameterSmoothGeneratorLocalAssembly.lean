import HolomorphicAnosov.Geometry.Manifold.CompactParameterIntegralDerivative
import HolomorphicAnosov.Geometry.Manifold.LocalSmoothGeneratorFromAverageG1
import HolomorphicAnosov.Geometry.Manifold.AverageJacobianInvertibilityG1
import HolomorphicAnosov.Geometry.Manifold.AverageJacobianShortTimeG1
import HolomorphicAnosov.Geometry.Manifold.ChartGluingGeneratorG1
import HolomorphicAnosov.Geometry.Manifold.AverageJetRegularityG1
import HolomorphicAnosov.Geometry.Manifold.AverageJetDifferentiabilityG1
import HolomorphicAnosov.Geometry.Manifold.AverageJetContinuityG1
import HolomorphicAnosov.Geometry.Manifold.LocalGeneratorChartSmoothG1
import HolomorphicAnosov.Geometry.Manifold.TangentFieldFromLocalGeneratorsG1
import HolomorphicAnosov.Geometry.Manifold.SmoothGeneratorConclusionG1
import HolomorphicAnosov.Geometry.Manifold.LocalGeneratorWitnessFromAverageG1
import HolomorphicAnosov.Geometry.Manifold.OrbitDerivativeUniquenessG1
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
Averaged spatial derivative identities for a continuous real action with smooth time slices
yield a global smooth tangent generator. (Bochner–Montgomery, Lemmas 2 and 5)
-/

open scoped Manifold ContDiff Interval
open Function Set

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A jointly continuous additive real action with smooth time slices and averaged spatial
derivative identities has a smooth tangent generator representing its orbit derivatives at zero.
(Bochner–Montgomery, Lemmas 2 and 5, pp. 688–689, 691) -/
theorem one_parameter_smooth_generator_local_assembly
    (a : ℝ → M → M)
    (hcont : Continuous (Function.uncurry a))
    (hzero : ∀ x, a 0 x = x)
    (hadd : ∀ s t x, a s (a t x) = a (s + t) x)
    (hdiff : ∀ t, ∃ g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ x, g x = a t x)
    (haverage : ∀ x : M, ∃ r > 0, ∀ h : ℝ, 0 ≤ h → h ≤ r / 2 →
      ∀ y ∈ Metric.ball (chartAt E x x) (r / 2), ∀ k : ℕ,
        HasFDerivAt
          (fun z ↦ ∫ t in 0..h, iteratedFDeriv ℝ k
            (fun w : E ↦ chartAt E x (a t ((chartAt E x).symm w))) z)
          (∫ t in 0..h, fderiv ℝ (iteratedFDeriv ℝ k
            (fun w : E ↦ chartAt E x (a t ((chartAt E x).symm w)))) y) y) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      CMDiff ∞ (T% X) ∧
        ∀ x, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ] TangentSpace 𝓘(ℝ, E) (a 0 x),
          HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t x) 0 L ∧
            X x = tangentSpaceCast (𝓘(ℝ, E)) (a 0 x) x
              (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1)) := by
  obtain ⟨X, hlocal, hderiv⟩ := local_generator_witness_from_average_g1 a hcont hzero hadd hdiff haverage
  have hX := chart_gluing_generator_g1 X hlocal
  exact smooth_generator_conclusion_g1 a X hX hderiv

end HolomorphicAnosov

