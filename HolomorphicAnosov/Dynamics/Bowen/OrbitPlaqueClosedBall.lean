import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Logic.Function.Iterate

namespace HolomorphicAnosov

/-- A smaller contracting orbit plaque is the larger plaque cut by a closed ball.

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), Lemma 2(c),
p.727, with the larger radius equal to γ. Membership in the smaller plaque
implies both conditions on the right, using the zeroth iterate for the ball.
Conversely, the center belongs to its γ-plaque. Pairwise contraction bounds
all subsequent distances by λⁿ times the zeroth distance, which is at most r.
This applies to forward or backward iterates; no continuity is needed.
DAG node: `dynamics.bowen_orbit_plaque_closed_ball_g15`. -/
theorem bowen_orbit_plaque_eq_inter_closedBall {X : Type*} [MetricSpace X]
    (f : X → X) {lam γ r : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hγ : 0 ≤ γ) (hrγ : r ≤ γ)
    (hc : ∀ (x y z : X) (n : ℕ),
      (∀ k : ℕ, dist (f^[k] y) (f^[k] x) ≤ γ) →
      (∀ k : ℕ, dist (f^[k] z) (f^[k] x) ≤ γ) →
      dist (f^[n] y) (f^[n] z) ≤ lam ^ n * dist y z) (x : X) :
    {y | ∀ n : ℕ, dist (f^[n] y) (f^[n] x) ≤ r} =
      {y | ∀ n : ℕ, dist (f^[n] y) (f^[n] x) ≤ γ} ∩ Metric.closedBall x r := by
  ext y
  constructor
  · intro hy
    exact ⟨fun n ↦ (hy n).trans hrγ, hy 0⟩
  · rintro ⟨hy, hd⟩ n
    have hx : ∀ k : ℕ, dist (f^[k] x) (f^[k] x) ≤ γ := by
      intro k
      simpa only [dist_self] using hγ
    exact (hc x y x n hy hx).trans
      ((mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam hlam1)).trans hd)

end HolomorphicAnosov
