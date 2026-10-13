import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.plaqueSlice

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

/-- Bowen Lemma 9, pp. 729–730: the full-plaque frontier included in the original space. -/
def plaqueBoundary {X : Type*} [TopologicalSpace X] (P S : Set X) : Set X :=
  Subtype.val '' frontier (plaqueSlice P S)

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
