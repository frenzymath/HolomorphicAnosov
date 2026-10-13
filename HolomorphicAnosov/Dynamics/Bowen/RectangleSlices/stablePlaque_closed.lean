import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem stablePlaque_closed {X : Type*} [MetricSpace X]
    (f : Homeomorph X X) (γ : ℝ) (x : X) : IsClosed (stablePlaque f γ x) := by
  change IsClosed {y | ∀ n : ℕ, dist ((f ^ n) y) ((f ^ n) x) ≤ γ}
  simp only [ofPred_forall]
  exact isClosed_iInter fun n ↦ isClosed_le
    (((f ^ n).continuous).dist continuous_const) continuous_const

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
