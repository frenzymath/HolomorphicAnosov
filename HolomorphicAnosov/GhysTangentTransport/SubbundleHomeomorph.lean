import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.GhysTangentTransport.TransportedDistribution
import HolomorphicAnosov.GhysTangentTransport.TangentHomeomorph
import HolomorphicAnosov.GhysTangentTransport.SubbundleSubtypeHomeomorph
import HolomorphicAnosov.GhysTangentTransport.TangentHomeomorphMem
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

/-- A homeomorphism of total spaces transports the original subbundle to its image under the derivative. -/
def subbundleHomeomorph (G : Type*) (P : (x : M) → Submodule ℝ (TangentSpace I x)) :
    Bundle.TotalSpace G (fun x ↦ ↥(P x)) ≃ₜ
      Bundle.TotalSpace G (fun y ↦ ↥(transportedDistribution e P y)) :=
  ((subbundleSubtypeHomeomorph G P).trans
    ((tangentHomeomorph e).subtype (tangentHomeomorph_mem e P))).trans
      (subbundleSubtypeHomeomorph G (transportedDistribution e P)).symm


end
end HolomorphicAnosov.GhysTangentTransport
