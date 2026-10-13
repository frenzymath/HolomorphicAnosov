import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.plaqueSlice

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem plaqueSlice_inter {X : Type*} (P A : Set X) :
    plaqueSlice P (A ∩ P) = plaqueSlice P A := by
  ext x
  simp [plaqueSlice]

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
