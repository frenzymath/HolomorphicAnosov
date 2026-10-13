import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.glue_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_tube_laws
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_inverse_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_frame
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_centered_frame_domain

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Over a compact set, a positive uniform radius bounded by `ρ` keeps vectors in the
exponential domain and their images under `f` in the chosen inverse domain.
(Hirsch–Pugh–Shub, p. 62) -/
theorem centered_radius
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (f : M → M) (hf : Continuous f)
    (B : Opens (M × M)) (hB : ∀ p ∈ A, (f p, f p) ∈ B)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R : ℝ, 0 < R ∧ R ≤ ρ ∧
      ∀ p ∈ A, ∀ v : TangentSpace 𝓘(ℝ, E) p, metricNorm g p v < R →
        (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExpDomain g ∧
          (f p, f (riemannianExp g p v)) ∈ B := by
  have hexp := riemannian_exponential_local_addition g
  let T : TangentBundle 𝓘(ℝ, E) M → M × M :=
    fun z ↦ (f z.proj, f (riemannianExponential g z))
  have hT : ContinuousOn T (riemannianExpDomain g) :=
    (hf.comp (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E)))).continuousOn.prodMk
      (hf.comp_continuousOn hexp.2.2.1.continuousOn)
  have hΩ : IsOpen (riemannianExpDomain g ∩ T ⁻¹' (B : Set _)) :=
    hT.isOpen_inter_preimage hexp.1 B.isOpen
  obtain ⟨U, δ, hAU, hδ, hU⟩ := compact_metric_tube g hΩ A hA (by
    intro p hp
    refine ⟨hexp.2.1 p, ?_⟩
    change (f p, f (riemannianExponential g ⟨p, 0⟩)) ∈ (B : Set _)
    rw [hexp.2.2.2.1 p]
    exact hB p hp)
  refine ⟨min δ ρ, lt_min hδ hρ, min_le_right _ _, ?_⟩
  intro p hp v hv
  exact hU ⟨hAU hp, hv.trans_le (min_le_left _ _)⟩


end ExponentialLift
end HolomorphicAnosov
