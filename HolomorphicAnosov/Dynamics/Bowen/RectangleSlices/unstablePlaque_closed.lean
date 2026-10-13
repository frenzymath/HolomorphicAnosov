import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque_closed

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem unstablePlaque_closed {X : Type*} [MetricSpace X]
    (f : Homeomorph X X) (γ : ℝ) (x : X) : IsClosed (unstablePlaque f γ x) :=
  stablePlaque_closed f.symm γ x

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
