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
/-- The preferred tangent trivialization at its center agrees with the tangent-space identification
with the model space, in both directions. (HPS, p. 62) -/
theorem tangent_frame_self (p : M) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).symmL ℝ p =
      (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap ∧
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ p =
      (tangentSpaceCastModel 𝓘(ℝ, E) p).toContinuousLinearMap := by
  constructor
  · rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source E p)]
    ext v
    exact tangentCoordChange_self (I := 𝓘(ℝ, E)) (mem_extChartAt_source p)
  · rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (mem_chart_source E p)]
    ext v
    exact tangentCoordChange_self (I := 𝓘(ℝ, E)) (mem_extChartAt_source p)


end ExponentialLift
end HolomorphicAnosov
