import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.glue_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_tube_laws
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_inverse_totalSpace

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

/-- The centered lift is `C^r` on the preimage of the inverse domain under
`z ↦ (f z.proj, f (riemannianExponential g z))` within the exponential domain.
(Hirsch–Pugh–Shub, p. 62) -/
theorem contMDiffOn_centered_totalSpace
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : M → M) (r : ℕ∞) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
    (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞)
    (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
    (hinv : ∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
      ⟨y.val.1, L y.val.1 y.val.2⟩) :
    ContMDiffOn (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)).tangent r
      (fun z : TangentBundle 𝓘(ℝ, E) M ↦
        (⟨f z.proj, centeredLift g f L z.proj z.snd⟩ : TangentBundle 𝓘(ℝ, E) M))
      (riemannianExpDomain g ∩
        (fun z : TangentBundle 𝓘(ℝ, E) M ↦
          (f z.proj, f (riemannianExp g z.proj z.snd))) ⁻¹' (B : Set _)) := by
  have horder : (r : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (show r ≤ (⊤ : ℕ∞) from le_top)
  have hexp := ((riemannian_exponential_local_addition g).2.2.1).of_le horder
  have hT : ContMDiffOn (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) r
      (fun z : TangentBundle 𝓘(ℝ, E) M ↦ (f z.proj, f (riemannianExponential g z)))
      (riemannianExpDomain g) :=
    (hf.comp (Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, E)))).contMDiffOn.prodMk
      (hf.comp_contMDiffOn hexp)
  exact ((contMDiffOn_inverse_totalSpace O B Φ L hinv).of_le horder).comp
    (hT.mono inter_subset_left) inter_subset_right


end ExponentialLift
end HolomorphicAnosov
