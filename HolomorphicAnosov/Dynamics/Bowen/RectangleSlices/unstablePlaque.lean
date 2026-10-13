import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

/-- Bowen Fact 1, p. 727: closed unstable orbit-distance plaque. -/
def unstablePlaque {X : Type*} [PseudoMetricSpace X]
    (f : Homeomorph X X) (γ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f.symm ^ n) y) ((f.symm ^ n) x) ≤ γ}

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
