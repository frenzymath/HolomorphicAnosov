import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque_self

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem stable_slice_small {X : Type*} [MetricSpace X]
    (f : Homeomorph X X) (lam γ r : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hγ : 0 ≤ γ)
    (hc : ∀ {x y z : X}, y ∈ stablePlaque f γ x → z ∈ stablePlaque f γ x →
      ∀ n : ℕ, dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    {A : Set X} (hA : IsCompact A) (hr : Metric.diam A ≤ r) {q : X} (hq : q ∈ A) :
    A ∩ stablePlaque f γ q ⊆ stablePlaque f r q := by
  intro z hz n
  have hd : dist z q ≤ r :=
    (Metric.dist_le_diam_of_mem hA.isBounded hz.1 hq).trans hr
  exact (hc hz.2 (stablePlaque_self f hγ q) n).trans
    ((mul_le_mul_of_nonneg_right (pow_le_one₀ hlam hlam1) dist_nonneg).trans
      (by simpa using hd))

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
