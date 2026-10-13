import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped ContDiff Manifold Topology _root_.Topology
open TopologicalSpace Set

universe u
namespace HolomorphicAnosov

/-- The original native leaf is path connected in its supplied intrinsic topology. -/
theorem covering_conjugacy_native_paths_g15
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M ≃ₜ M) (D : RealTangentDistribution 𝓘(ℝ, E) M) (x : M)
    (native : NativeAsymptoticLeafDatum 𝓘(ℝ, E) f D x) :
    letI := native.topology
    PathConnectedSpace (StableAsymptoticLeaf f x) ∧
      Continuous (Subtype.val : StableAsymptoticLeaf f x → M) := by
  let := native.topology
  let := native.charts
  let := native.connected
  let : LocallyPathConnectedSpace (StableAsymptoticLeaf f x) :=
    ChartedSpace.locallyPathConnectedSpace (Fin native.rank → ℝ) _
  exact ⟨PathConnectedSpace.of_locallyPathConnectedSpace, native.inclusion_smooth.continuous⟩


end HolomorphicAnosov
