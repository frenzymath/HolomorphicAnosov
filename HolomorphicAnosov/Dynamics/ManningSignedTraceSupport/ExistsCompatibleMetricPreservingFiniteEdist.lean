import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompactFiniteEdistBound
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CappedMetric

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Choose the uniform bound as cap. Every originally finite distance is unchanged and every infinite distance becomes the cap. Old and new structures are explicit in the statement, avoiding any local-instance tautology. -/
theorem exists_compatible_metric_preserving_finite_edist {X : Type*}
    [e : EMetricSpace X] [CompactSpace X] :
    ∃ g : MetricSpace X,
      g.toUniformSpace.toTopologicalSpace = e.toUniformSpace.toTopologicalSpace ∧
      ∀ x y : X, @edist X e.toPseudoEMetricSpace.toEDist x y ≠ ⊤ →
        @edist X g.toPseudoMetricSpace.toPseudoEMetricSpace.toEDist x y =
          @edist X e.toPseudoEMetricSpace.toEDist x y := by
  obtain ⟨R, hR, hbound⟩ := compact_finite_edist_bound (X := X)
  refine ⟨cappedMetric (ENNReal.ofReal R) (by positivity) (by simp), rfl, ?_⟩
  intro x y hxy
  change min (ENNReal.ofReal R) (edist x y) = edist x y
  apply min_eq_right
  rw [← ENNReal.ofReal_toReal hxy]
  exact ENNReal.ofReal_le_ofReal (hbound x y hxy)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
