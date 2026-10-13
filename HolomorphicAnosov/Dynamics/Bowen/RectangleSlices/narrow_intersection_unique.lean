import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque_self
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque_self

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem narrow_intersection_unique {X : Type*} [MetricSpace X]
    (f : Homeomorph X X) (γ ε r r' s s' : ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hr : r + r' ≤ γ) (hs : s + s' ≤ γ)
    (bracket : X → X → X)
    (hu : ∀ {x y z : X}, dist x y ≤ ε →
      z ∈ stablePlaque f γ x ∩ unstablePlaque f γ y → z = bracket x y)
    (a b z w : X) (hzs : z ∈ stablePlaque f r a) (hws : w ∈ stablePlaque f r' a)
    (hzu : z ∈ unstablePlaque f s b) (hwu : w ∈ unstablePlaque f s' b) : z = w := by
  have hz : z ∈ stablePlaque f γ w ∩ unstablePlaque f γ w := by
    constructor <;> intro n
    · exact ((dist_triangle _ _ _).trans (add_le_add (hzs n)
        (by simpa only [dist_comm] using hws n))).trans hr
    · exact ((dist_triangle _ _ _).trans (add_le_add (hzu n)
        (by simpa only [dist_comm] using hwu n))).trans hs
  have he : dist w w ≤ ε := by simpa using hε.le
  exact (hu he hz).trans (hu he
    ⟨stablePlaque_self f hγ.le w, unstablePlaque_self f hγ.le w⟩).symm

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
