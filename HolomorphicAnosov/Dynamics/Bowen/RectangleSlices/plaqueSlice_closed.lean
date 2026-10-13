import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.plaqueSlice

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem plaqueSlice_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) (P : Set X) : IsClosed (plaqueSlice P A) :=
  hA.preimage continuous_subtype_val

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
