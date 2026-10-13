import HolomorphicAnosov.Geometry.Manifold.LocalGeneratorWitnessLocalSectionsG1


/-!
Averaged spatial derivative identities for a continuous real action with smooth time slices give
a tangent section that is locally smooth and represents the orbit derivative at zero.
-/

open scoped Manifold ContDiff Interval Topology _root_.Topology
open Function Set

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A jointly continuous additive real action with smooth time slices and averaged spatial
derivative identities admits a locally smooth tangent section representing its orbit derivatives
at zero. -/
theorem local_generator_witness_from_average_g1
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
      (∀ x, ∃ U ∈ 𝓝 x, CMDiff[U] ∞ (T% X)) ∧
      (∀ x, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ] TangentSpace 𝓘(ℝ, E) (a 0 x),
        HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t x) 0 L ∧
          X x = tangentSpaceCast (𝓘(ℝ, E)) (a 0 x) x
            (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1))) := by
  apply local_orbit_sections_glue_g1 a
  exact local_generator_local_sections_from_average_g1 a hcont hzero hadd hdiff haverage

end HolomorphicAnosov

