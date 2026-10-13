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
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_radius
import HolomorphicAnosov.Geometry.UniformExponentialLift.vertical_jet_restriction
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuousOn_vertical_jets
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuousOn_manifold_vertical_jets
import HolomorphicAnosov.Geometry.UniformExponentialLift.tangent_frame_self

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

/-- The centered lift has fiberwise `C^r` regularity and jointly continuous vertical jets
on metric disks contained in its domain. (Hirsch–Pugh–Shub, p. 62) -/
theorem centered_vertical_jets
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (f : M → M) (r : ℕ∞) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
    (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞)
    (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
    (hinv : ∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
      ⟨y.val.1, L y.val.1 y.val.2⟩) (R : ℝ)
    (hdomain : ∀ p ∈ A, ∀ v : TangentSpace 𝓘(ℝ, E) p, metricNorm g p v < R →
      (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExpDomain g ∧
        (f p, f (riemannianExp g p v)) ∈ B) :
    HasContinuousVerticalJetsOn A f r (fun p ↦ centeredLift g f L p)
      (fun p ↦ {v | metricNorm g p v < R}) := by
  constructor
  · intro p
    have hQ := contMDiffOn_centered_frame g f r hf O B Φ L hinv (p : M) (f p)
    have hfixed := hQ.comp (contMDiffOn_const.prodMk contMDiffOn_id)
      (s := (tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm ⁻¹'
        {v | metricNorm g (p : M) v < R}) (fun u hu ↦ by
          refine ⟨mem_chart_source E (p : M), mem_chart_source E (f p), ?_⟩
          simpa only [(tangent_frame_self (p : M)).1, id_eq,
            ContinuousLinearEquiv.coe_coe] using
            hdomain p p.property _ hu)
    simpa only [Function.comp_def, id_eq,
      (tangent_frame_self (p : M)).1, (tangent_frame_self (f p)).2,
      ContinuousLinearEquiv.coe_coe]
      using hfixed.contDiffOn
  · intro s t j hj
    have hQ := contMDiffOn_centered_frame g f r hf O B Φ L hinv s t
    have hopen := isOpen_centered_frame_domain g f hf.continuous B s t
    have hjet := continuousOn_manifold_vertical_jets _ _ hopen r hQ j hj
    have hmap : MapsTo (fun z : A × E ↦ ((z.1 : M), z.2))
        {z | (z.1 : M) ∈ (chartAt E s).source ∧ f z.1 ∈ (chartAt E t).source ∧
          (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) z.2 ∈
            {v | metricNorm g (z.1 : M) v < R}}
        {z : M × E | z.1 ∈ (chartAt E s).source ∧ f z.1 ∈ (chartAt E t).source ∧
          (⟨z.1, (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ z.1 z.2⟩ :
            TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExpDomain g ∧
          (f z.1, f (riemannianExp g z.1
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ z.1 z.2))) ∈ B} := by
      intro z hz
      exact ⟨hz.1, hz.2.1, hdomain z.1 z.1.property _ hz.2.2⟩
    change ContinuousOn (fun z : A × E ↦ iteratedFDeriv ℝ j
      (fun u ↦ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).continuousLinearMapAt ℝ (f z.1)
        (centeredLift g f L z.1
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) u))) z.2) _
    have hc : Continuous (fun z : A × E ↦ ((z.1 : M), z.2)) :=
      continuous_fst.subtype_val.prodMk continuous_snd
    have h := hjet.comp hc.continuousOn hmap
    simpa only [Function.comp_def] using h


end ExponentialLift
end HolomorphicAnosov
