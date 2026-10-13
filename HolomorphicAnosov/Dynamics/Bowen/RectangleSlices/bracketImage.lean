import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

/-- Bowen Lemma 9, pp. 729–730: image of the two slices under the bracket. -/
def bracketImage {X : Type*} (bracket : X → X → X)
    (C D : Set X) : Set X := {z | ∃ c ∈ C, ∃ d ∈ D, bracket c d = z}

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
