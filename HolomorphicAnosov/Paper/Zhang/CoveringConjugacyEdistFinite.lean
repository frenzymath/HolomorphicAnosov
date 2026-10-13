import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Connected.Clopen

open Set
open scoped Topology _root_.Topology

universe u
namespace HolomorphicAnosov

/-- An extended metric on a connected space is finite: its finite-distance class through any point is both open and closed. -/
theorem covering_conjugacy_edist_finite_g15
    {M : Type u} [EMetricSpace M] [PreconnectedSpace M] (x y : M) :
    edist x y ≠ ⊤ := by
  have heq : Metric.eball x ⊤ = Set.univ :=
    (show IsClopen (Metric.eball x ⊤) from
      ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩).eq_univ
        ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [heq]; trivial
  exact ne_top_of_lt (by simpa only [Metric.mem_eball, edist_comm] using hy)


end HolomorphicAnosov
