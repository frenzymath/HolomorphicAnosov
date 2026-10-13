import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.GhysTangentTransport.TransportedDistribution
import HolomorphicAnosov.GhysTangentTransport.TransportedTrivialization
import HolomorphicAnosov.GhysTangentTransport.TransportedTrivializationLinear
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

/-- Transport a continuous tangent subbundle along a smooth equivalence and its derivative. (Zhang, p. 1; Theorem 1.2) -/
def transportedSubbundle (P : ContinuousRealTangentSubbundle I M) :
    ContinuousRealTangentSubbundle J N where
  toDistribution := transportedDistribution e P.toDistribution
  locally_trivial y := by
    obtain ⟨r, t, ht, hlinear⟩ := P.locally_trivial (e.symm y)
    refine ⟨r, transportedTrivialization e (Fin r → ℝ) P.toDistribution t, ?_, ?_⟩
    · exact ht
    · let := hlinear
      exact transportedTrivialization_linear e (Fin r → ℝ) P.toDistribution t


end
end HolomorphicAnosov.GhysTangentTransport
