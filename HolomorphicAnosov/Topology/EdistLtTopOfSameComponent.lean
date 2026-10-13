import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Connected.Clopen

namespace HolomorphicAnosov

open Set

/-- Finite-distance balls are clopen. Therefore two points in one connected
component always have finite extended distance. -/
theorem edist_lt_top_of_same_component {X : Type*} [EMetricSpace X]
    {x y : X} (hy : y ∈ connectedComponent x) : edist x y < ⊤ := by
  have hc : IsClopen (Metric.eball x ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hm : x ∈ Metric.eball x ⊤ := by simp
  have hy' := hc.connectedComponent_subset hm hy
  simpa only [Metric.mem_eball, edist_comm] using hy'

end HolomorphicAnosov
