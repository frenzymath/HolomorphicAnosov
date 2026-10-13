import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque_self

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem unstablePlaque_self {X : Type*} [MetricSpace X]
    (f : Homeomorph X X) {γ : ℝ} (hγ : 0 ≤ γ) (x : X) :
    x ∈ unstablePlaque f γ x :=
  stablePlaque_self f.symm hγ x

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
