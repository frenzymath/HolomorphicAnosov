import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem regular_closed_prod_right {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (S : Set Y) (T : Set Z) (hT : IsClosed T) (hS : S.Nonempty)
    (hr : S ×ˢ T = closure (interior (S ×ˢ T))) : T = closure (interior T) := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨x, hx⟩ := hS
    have hp : (x, y) ∈ closure (interior (S ×ˢ T)) := hr ▸ ⟨hx, hy⟩
    rw [interior_prod_eq, closure_prod_eq] at hp
    exact hp.2
  · exact closure_minimal interior_subset hT

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
