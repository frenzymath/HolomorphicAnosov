import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.GhysTangentTransport.TransportedDistribution
import HolomorphicAnosov.GhysTangentTransport.TransportedSubbundle
import HolomorphicAnosov.GhysTangentTransport.SubbundleTopology

open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.GhysTangentTransport
noncomputable section
universe u v
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  (e : Diffeomorph I J M N ∞)

attribute [local instance] subbundleTopology

@[local simp] theorem transportedSubbundle_distribution (P : ContinuousRealTangentSubbundle I M)
    (y : N) :
    (transportedSubbundle e P).toDistribution y = transportedDistribution e P.toDistribution y :=
  rfl


end
end HolomorphicAnosov.GhysTangentTransport
