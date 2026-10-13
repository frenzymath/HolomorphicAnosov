import HolomorphicAnosov.Geometry.Manifold.CompactParameterIntegralDerivative
import HolomorphicAnosov.Geometry.Manifold.EuclideanOrbitMFDerivG1
import HolomorphicAnosov.Geometry.Manifold.LocalGeneratorChartBallCoreG1
import HolomorphicAnosov.Geometry.Manifold.SmoothGeneratorConclusionG1

/-!
Smooth local tangent sections representing orbit derivatives at zero determine a global locally
smooth tangent section.
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

omit [FiniteDimensional ℝ E] in
/-- Smooth local tangent sections representing orbit derivatives at zero determine a global locally
smooth tangent section representing those derivatives. -/
theorem local_orbit_sections_glue_g1
    (a : ℝ → M → M)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x,
      ∃ Y : (y : M) → TangentSpace 𝓘(ℝ, E) y,
        CMDiff[U] ∞ (T% Y) ∧
        ∀ y ∈ U, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ]
            TangentSpace 𝓘(ℝ, E) (a 0 y),
          HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t y) 0 L ∧
          Y y = tangentSpaceCast (𝓘(ℝ, E)) (a 0 y) y
            (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1))) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      (∀ x, ∃ U ∈ 𝓝 x, CMDiff[U] ∞ (T% X)) ∧
      (∀ x, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ] TangentSpace 𝓘(ℝ, E) (a 0 x),
        HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t x) 0 L ∧
          X x = tangentSpaceCast (𝓘(ℝ, E)) (a 0 x) x
            (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1))) := by
  let X : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun x ↦
    tangentSpaceCast (𝓘(ℝ, E)) (a 0 x) x
      ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t x) 0)
        ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1))
  refine ⟨X, ?_, ?_⟩
  · intro x
    obtain ⟨U, hU, Y, hY, hderiv⟩ := hloc x
    refine ⟨U, hU, hY.congr ?_⟩
    intro y hy
    obtain ⟨L, hL, heq⟩ := hderiv y hy
    have hXY : X y = Y y := by
      change tangentSpaceCast (𝓘(ℝ, E)) (a 0 y) y
        ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t y) 0)
          ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1)) = Y y
      rw [hL.mfderiv, heq]
    change (⟨y, X y⟩ : TangentBundle (𝓘(ℝ, E)) M) = ⟨y, Y y⟩
    rw [hXY]
  · intro x
    obtain ⟨U, hU, Y, hY, hderiv⟩ := hloc x
    obtain ⟨L, hL, heq⟩ := hderiv x (mem_of_mem_nhds hU)
    refine ⟨L, hL, ?_⟩
    change tangentSpaceCast (𝓘(ℝ, E)) (a 0 x) x
      ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t x) 0)
        ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1)) = _
    rw [hL.mfderiv]

/-- A jointly continuous additive real action with smooth time slices and averaged spatial
derivative identities admits smooth local tangent sections representing its orbit derivatives at
zero. -/
theorem local_generator_local_sections_from_average_g1
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
    ∀ x : M, ∃ U ∈ 𝓝 x,
      ∃ Y : (y : M) → TangentSpace 𝓘(ℝ, E) y,
        CMDiff[U] ∞ (T% Y) ∧
        ∀ y ∈ U, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ]
            TangentSpace 𝓘(ℝ, E) (a 0 y),
          HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t y) 0 L ∧
          Y y = tangentSpaceCast (𝓘(ℝ, E)) (a 0 y) y
            (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1)) := by
  intro x
  obtain ⟨U, hU, hopen, Y, hY, hderiv⟩ :=
    local_generator_chart_ball_core_g1 a hcont hzero hadd hdiff haverage x
  exact ⟨U, hU, Y, hY, hderiv⟩
end HolomorphicAnosov
