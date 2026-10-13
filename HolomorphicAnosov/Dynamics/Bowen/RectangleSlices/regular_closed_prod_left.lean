import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem regular_closed_prod_left {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (S : Set Y) (T : Set Z) (hS : IsClosed S) (hT : T.Nonempty)
    (hr : S ×ˢ T = closure (interior (S ×ˢ T))) : S = closure (interior S) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := hT
    have hp : (x, y) ∈ closure (interior (S ×ˢ T)) := hr ▸ ⟨hx, hy⟩
    rw [interior_prod_eq, closure_prod_eq] at hp
    exact hp.1
  · exact closure_minimal interior_subset hS

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
