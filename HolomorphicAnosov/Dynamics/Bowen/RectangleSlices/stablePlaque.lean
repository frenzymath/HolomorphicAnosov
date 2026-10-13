import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

/-- Bowen Fact 1, p. 727: closed stable orbit-distance plaque. -/
def stablePlaque {X : Type*} [PseudoMetricSpace X]
    (f : Homeomorph X X) (γ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f ^ n) y) ((f ^ n) x) ≤ γ}

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
