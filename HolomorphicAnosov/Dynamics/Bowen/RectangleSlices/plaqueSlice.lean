import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

/-- Bowen Lemma 9, pp. 729–730: the slice in the full plaque with its subspace topology. -/
def plaqueSlice {X : Type*} (P S : Set X) : Set P :=
  Subtype.val ⁻¹' S

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
