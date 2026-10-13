import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Connected.Clopen

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped ENNReal Classical
noncomputable section

/-- The radius-infinity extended ball is clopen and contains x, hence contains the connected component of x. Its points are at finite distance from x. -/
theorem finite_edist_of_mem_connectedComponent {X : Type*} [PseudoEMetricSpace X]
    {x y : X} (hy : y ∈ connectedComponent x) : edist x y ≠ ⊤ := by
  have hc : IsClopen (Metric.eball x ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hx : x ∈ Metric.eball x ⊤ := by simp
  have hyball := hc.connectedComponent_subset hx hy
  have h : edist y x < ⊤ := hyball
  simpa only [edist_comm] using h.ne



end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
