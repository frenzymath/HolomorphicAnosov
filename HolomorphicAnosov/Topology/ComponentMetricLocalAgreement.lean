import HolomorphicAnosov.Topology.UniformLocalDistanceAgreement
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Basic

open Set
open scoped ENNReal
namespace HolomorphicAnosov

/-- A componentwise distance metric and a locally matching compatible metric
agree uniformly near the diagonal on a compact locally connected space.

Agent-written bridge in the Hirsch–Pugh construction. Intersect each supplied
local agreement neighborhood with its open connected component. Any two points
of this intersection lie in the same component, so both real distances have
the same extended-real value. Their nonnegativity converts this equality back
to real distances. Apply the public compact uniform-local-agreement theorem.
The topology and connected components in the hypotheses are the original ones.
No global equality between the two metrics is asserted. -/
theorem component_metric_local_agreement
    {X : Type*} [t : TopologicalSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    (d old : MetricSpace X)
    (hd : d.toUniformSpace.toTopologicalSpace = t)
    (ρ : X → X → ℝ≥0∞)
    (hcomp : ∀ x y : X, y ∈ @connectedComponent X t x →
      ENNReal.ofReal (d.dist x y) = ρ x y)
    (hlocal : ∀ x : X, ∃ V : Set X, @IsOpen X t V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V,
        ENNReal.ofReal (@dist X old.toPseudoMetricSpace.toDist y z) = ρ y z) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : X,
      @dist X d.toPseudoMetricSpace.toDist x y ≤ r →
        @dist X d.toPseudoMetricSpace.toDist x y = @dist X old.toPseudoMetricSpace.toDist x y := by
  let : MetricSpace X := d.replaceTopology hd.symm
  apply uniform_local_distance_agreement (@dist X old.toPseudoMetricSpace.toDist)
  intro x
  obtain ⟨V, hV, hxV, hVeq⟩ := hlocal x
  refine ⟨V ∩ connectedComponent x, hV.inter isOpen_connectedComponent,
    ⟨hxV, mem_connectedComponent⟩, ?_⟩
  intro y hy z hz
  have hzy : z ∈ connectedComponent y := by
    rw [← connectedComponent_eq hy.2]
    exact hz.2
  have heq := (hcomp y z hzy).trans (hVeq y hy.1 z hz.1).symm
  simpa only [ENNReal.toReal_ofReal (@dist_nonneg X d.toPseudoMetricSpace y z),
    ENNReal.toReal_ofReal (@dist_nonneg X old.toPseudoMetricSpace y z)] using
      congrArg ENNReal.toReal heq

end HolomorphicAnosov
