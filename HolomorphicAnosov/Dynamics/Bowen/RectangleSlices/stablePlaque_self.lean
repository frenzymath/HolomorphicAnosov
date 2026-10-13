import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem stablePlaque_self {X : Type*} [MetricSpace X]
    (f : Homeomorph X X) {γ : ℝ} (hγ : 0 ≤ γ) (x : X) :
    x ∈ stablePlaque f γ x := by
  intro n
  simpa using hγ

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
