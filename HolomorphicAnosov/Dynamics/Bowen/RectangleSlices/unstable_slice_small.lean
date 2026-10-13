import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stable_slice_small

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem unstable_slice_small {X : Type*} [MetricSpace X]
    (f : Homeomorph X X) (lam γ r : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hγ : 0 ≤ γ)
    (hc : ∀ {x y z : X}, y ∈ unstablePlaque f γ x → z ∈ unstablePlaque f γ x →
      ∀ n : ℕ, dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    {A : Set X} (hA : IsCompact A) (hr : Metric.diam A ≤ r) {q : X} (hq : q ∈ A) :
    A ∩ unstablePlaque f γ q ⊆ unstablePlaque f r q :=
  stable_slice_small f.symm lam γ r hlam hlam1 hγ hc hA hr hq

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
