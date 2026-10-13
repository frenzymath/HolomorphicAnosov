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
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_vertical_jets

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

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The inclusion of a fixed tangent fiber into the tangent bundle is smooth.
(Andrews, 8.11.4) -/
theorem fixed_fibre_contMDiff (p : M) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun v : E ↦ (⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩ :
        TangentBundle 𝓘(ℝ, E) M)) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_const, ?_⟩
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) p
  let K : E →L[ℝ] E := (e.continuousLinearMapAt ℝ p).comp
    (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap
  have hK : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ K := K.contDiff.contMDiff
  convert hK.contMDiffAt using 1
  ext w
  exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e
    (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) p) _).symm


end ExponentialLift
end HolomorphicAnosov
