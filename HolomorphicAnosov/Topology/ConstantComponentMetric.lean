import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CappedMetric
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompactFiniteEdistBound
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FiniteEdistConnectedComponent

open Set
open scoped ENNReal
namespace HolomorphicAnosov
open Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

/-- A compact extended metric whose finite-distance classes are connected has
a compatible finite metric preserving every component distance and taking one
positive value between different components.

This agent-written assembly is the constant-component step in the Hirsch–Pugh
adapted metric construction. The public compact finite-distance bound gives a
positive cap R. The public capped metric retains the original topology. Within
a connected component, extended distance is finite and at most R, so capping
does not change it. Outside a component the given implication forces infinite
extended distance, which is replaced by exactly R. Empty spaces are included.
The original and resulting metric structures remain explicit in the statement. -/
theorem exists_constant_component_metric
    {X : Type*} [e : EMetricSpace X] [CompactSpace X]
    (hconnected : ∀ x y : X, edist x y ≠ ⊤ → y ∈ connectedComponent x) :
    ∃ (d : MetricSpace X) (D : ℝ), 0 < D ∧
      d.toUniformSpace.toTopologicalSpace = e.toUniformSpace.toTopologicalSpace ∧
      (∀ x y : X, y ∈ @connectedComponent X e.toUniformSpace.toTopologicalSpace x →
        ENNReal.ofReal (d.dist x y) = @edist X e.toPseudoEMetricSpace.toEDist x y) ∧
      (∀ x y : X, y ∉ @connectedComponent X e.toUniformSpace.toTopologicalSpace x →
        d.dist x y = D) := by
  obtain ⟨R, hR, hbound⟩ := compact_finite_edist_bound (X := X)
  let d : MetricSpace X := cappedMetric (ENNReal.ofReal R) (by positivity) ENNReal.ofReal_ne_top
  have hed (x y : X) :
      @edist X d.toPseudoMetricSpace.toPseudoEMetricSpace.toEDist x y =
        min (ENNReal.ofReal R) (@edist X e.toPseudoEMetricSpace.toEDist x y) := rfl
  refine ⟨d, R, hR, rfl, ?_, ?_⟩
  · intro x y hy
    have hxy := @finite_edist_of_mem_connectedComponent X e.toPseudoEMetricSpace x y hy
    rw [← @edist_dist X d.toPseudoMetricSpace x y, hed]
    apply min_eq_right
    rw [← ENNReal.ofReal_toReal hxy]
    exact ENNReal.ofReal_le_ofReal (hbound x y hxy)
  · intro x y hy
    have hxy : @edist X e.toPseudoEMetricSpace.toEDist x y = ⊤ := by
      by_contra hfinite
      exact hy (hconnected x y hfinite)
    have heq : ENNReal.ofReal (d.dist x y) = ENNReal.ofReal R := by
      rw [← @edist_dist X d.toPseudoMetricSpace x y, hed, hxy, min_eq_left le_top]
    simpa only [ENNReal.toReal_ofReal (@dist_nonneg X d.toPseudoMetricSpace x y),
      ENNReal.toReal_ofReal hR.le] using congrArg ENNReal.toReal heq

end HolomorphicAnosov
