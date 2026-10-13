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

omit [FiniteDimensional ℝ E] in
/-- A `C^r` map on an open product domain has jointly continuous vertical jets through
order `r`, including order zero. (Hirsch–Pugh–Shub, p. 62) -/
theorem continuousOn_vertical_jets
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Q : F × E → G) (D : Set (F × E)) (hD : IsOpen D)
    (n : ℕ∞ω) (hQ : ContDiffOn ℝ n Q D) (j : ℕ) (hj : j ≤ n) :
    ContinuousOn (fun z : F × E ↦ iteratedFDeriv ℝ j (fun u ↦ Q (z.1, u)) z.2) D := by
  have htotal : ContinuousOn (iteratedFDeriv ℝ j Q) D :=
    (hQ.continuousOn_iteratedFDerivWithin hj hD.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen j hD).symm
  have hrestricted :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin j ↦ ContinuousLinearMap.inr ℝ F E) (F := G)).continuous.comp_continuousOn htotal
  exact hrestricted.congr (fun z hz ↦ vertical_jet_restriction Q D hD n hQ z.1 z.2 hz j hj)


end ExponentialLift
end HolomorphicAnosov
