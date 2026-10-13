import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov

/-- Transfer an actual all-time orbit-core contraction between locally agreeing
metrics. This agent-written scalar metric step applies to any self-map.

A point whose new orbit remains within γ of its center has the same old orbit
distances, since γ≤r, and therefore belongs to the old radius-R core. Two such
orbits remain within 2γ≤r of each other by the new triangle inequality. Their
mutual distances, including at time zero, are thus unchanged. Substitute these
equalities in the given old-metric contraction. No continuity, sign condition
on λ, or assumption of global equality of the two metrics is used. -/
theorem orbit_core_contraction_metric_transfer
    {X : Type*} (f : X → X) (d old : MetricSpace X)
    {r γ R lam : ℝ} (hγ : 0 ≤ γ) (hsmall : 2 * γ ≤ r) (hR : γ ≤ R)
    (hagree : ∀ x y : X, d.dist x y ≤ r → d.dist x y = old.dist x y)
    (hcontract : ∀ x y z : X,
      (∀ n : ℕ, old.dist (f^[n] y) (f^[n] x) ≤ R) →
      (∀ n : ℕ, old.dist (f^[n] z) (f^[n] x) ≤ R) →
      ∀ n : ℕ, old.dist (f^[n] y) (f^[n] z) ≤ lam ^ n * old.dist y z) :
    ∀ x y z : X,
      (∀ n : ℕ, d.dist (f^[n] y) (f^[n] x) ≤ γ) →
      (∀ n : ℕ, d.dist (f^[n] z) (f^[n] x) ≤ γ) →
      ∀ n : ℕ, d.dist (f^[n] y) (f^[n] z) ≤ lam ^ n * d.dist y z := by
  intro x y z hy hz n
  have hγr : γ ≤ r := by linarith
  have hyold : ∀ n : ℕ, old.dist (f^[n] y) (f^[n] x) ≤ R := by
    intro n
    rw [← hagree _ _ ((hy n).trans hγr)]
    exact (hy n).trans hR
  have hzold : ∀ n : ℕ, old.dist (f^[n] z) (f^[n] x) ≤ R := by
    intro n
    rw [← hagree _ _ ((hz n).trans hγr)]
    exact (hz n).trans hR
  have hpair (k : ℕ) : d.dist (f^[k] y) (f^[k] z) ≤ r := by
    have htri := @dist_triangle X d.toPseudoMetricSpace (f^[k] y) (f^[k] x) (f^[k] z)
    rw [@dist_comm X d.toPseudoMetricSpace (f^[k] x) (f^[k] z)] at htri
    exact (htri.trans (add_le_add (hy k) (hz k))).trans (by linarith)
  rw [hagree _ _ (hpair n), hagree y z (by simpa using hpair 0)]
  exact hcontract x y z hyold hzold n

end HolomorphicAnosov
