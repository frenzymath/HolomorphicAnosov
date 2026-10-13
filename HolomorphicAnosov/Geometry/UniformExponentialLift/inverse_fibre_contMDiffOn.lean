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
import HolomorphicAnosov.Geometry.UniformExponentialLift.fixed_fibre_contMDiff

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
/-- The fixed-base inverse exponential map is smooth on its slice of the inverse
domain. (Andrews, 8.11.5) -/
theorem inverse_fibre_contMDiffOn
    (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
    (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞)
    (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
    (hinv : ∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
      ⟨y.val.1, L y.val.1 y.val.2⟩) (q : M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun w ↦ tangentSpaceCastModel 𝓘(ℝ, E) q (L q w)) {w | (q, w) ∈ B} := by
  have hH := (contMDiffOn_inverse_totalSpace O B Φ L hinv).comp
    (contMDiffOn_const.prodMk contMDiffOn_id)
    (s := {w | (q, w) ∈ B}) (fun w hw ↦ hw)
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) q
  have hcoord := (e.contMDiffOn_iff (fun w hw ↦ e.mem_source.mpr
    (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) q))).mp hH
  apply hcoord.2.congr
  intro w hw
  change tangentSpaceCastModel 𝓘(ℝ, E) q (L q w) = (e ⟨q, L q w⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e
    (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) q)]
  rw [(tangent_frame_self q).2]
  rfl


end ExponentialLift
end HolomorphicAnosov
