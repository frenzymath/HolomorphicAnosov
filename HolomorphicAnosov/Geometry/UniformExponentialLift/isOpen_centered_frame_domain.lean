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

/-- The domain of the centered lift in tangent-frame coordinates is open.
(Hirsch–Pugh–Shub, p. 62) -/
theorem isOpen_centered_frame_domain
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : M → M) (hf : Continuous f) (B : Opens (M × M)) (s t : M) :
    let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    let e' := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
    let Z : M × E → TangentBundle 𝓘(ℝ, E) M :=
      fun z ↦ ⟨z.1, e.symmL ℝ z.1 z.2⟩
    IsOpen {z : M × E | z.1 ∈ e.baseSet ∧ f z.1 ∈ e'.baseSet ∧
      Z z ∈ riemannianExpDomain g ∧
        (f z.1, f (riemannianExp g z.1 (e.symmL ℝ z.1 z.2))) ∈ B} := by
  dsimp only
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
  let e' := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
  let T : TangentBundle 𝓘(ℝ, E) M → M × M :=
    fun z ↦ (f z.proj, f (riemannianExponential g z))
  let Ω := riemannianExpDomain g ∩ T ⁻¹' (B : Set _)
  have hexp := riemannian_exponential_local_addition g
  have hT : ContinuousOn T (riemannianExpDomain g) :=
    (hf.comp (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E)))).continuousOn.prodMk
      (hf.comp_continuousOn hexp.2.2.1.continuousOn)
  have hΩ : IsOpen Ω := hT.isOpen_inter_preimage hexp.1 B.isOpen
  have hopen := (e.toOpenPartialHomeomorph.continuousOn_symm.isOpen_inter_preimage
    e.open_target hΩ).inter (e'.open_baseSet.preimage (hf.comp continuous_fst))
  convert hopen using 1
  ext z
  by_cases hz : z.1 ∈ e.baseSet
  · have hez : e.toOpenPartialHomeomorph.symm z =
        (⟨z.1, e.symmL ℝ z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) M) := by
      rw [e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) z.1 hz]
      simp only [Trivialization.symmL_apply, hz,
        Trivialization.continuousLinearEquivAt_symm_apply]
    simp only [Set.mem_inter_iff, Set.mem_preimage, e.mem_target, hz, true_and,
      Ω, T, hez, riemannianExp, Set.mem_ofPred_eq]
    tauto
  · have hz' : z.1 ∉ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).baseSet := hz
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, e.mem_target,
      hz, false_and, iff_false]
    exact fun h ↦ hz' h.1


end ExponentialLift
end HolomorphicAnosov
