import HolomorphicAnosov.Dynamics.Bowen.OrbitPlaqueClosedBall
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov

/-- Contracting orbit plaques admit relatively open collars between distinct radii.

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), p.735,
the choice W_(α₃/3)(x) ⊆ W ⊆ W_(2α₃/3)(x) immediately before the complementary
factors, using Lemma 2(c), p.727. Intersect the full γ-plaque with the open ball
of midpoint radius (r+R)/2. The zeroth orbit condition gives the inner inclusion;
Lemma 2(c) gives the outer inclusion. The collar is relatively open by continuity
of the subtype inclusion. The construction includes r=0 and singleton plaques.
DAG node: `dynamics.bowen_orbit_plaque_open_collar_g15`. -/
theorem bowen_orbit_plaque_open_collar {X : Type*} [MetricSpace X]
    (f : X → X) {lam γ r R : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hr : 0 ≤ r) (hrR : r < R) (hRγ : R ≤ γ)
    (hc : ∀ (x y z : X) (n : ℕ),
      (∀ k : ℕ, dist (f^[k] y) (f^[k] x) ≤ γ) →
      (∀ k : ℕ, dist (f^[k] z) (f^[k] x) ≤ γ) →
      dist (f^[n] y) (f^[n] z) ≤ lam ^ n * dist y z) (x : X) :
    let W := fun s ↦ {y | ∀ n : ℕ, dist (f^[n] y) (f^[n] x) ≤ s}
    ∃ E : Set X, E ⊆ W γ ∧
      IsOpen ((Subtype.val : W γ → X) ⁻¹' E) ∧ W r ⊆ E ∧ E ⊆ W R := by
  dsimp only
  let S : Set X := {y | ∀ n : ℕ, dist (f^[n] y) (f^[n] x) ≤ γ}
  refine ⟨S ∩ Metric.ball x ((r + R) / 2), Set.inter_subset_left, ?_, ?_, ?_⟩
  · have heq : (Subtype.val : S → X) ⁻¹' (S ∩ Metric.ball x ((r + R) / 2)) =
        (Subtype.val : S → X) ⁻¹' Metric.ball x ((r + R) / 2) := by
      ext y
      exact and_iff_right y.property
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  · intro y hy
    refine ⟨fun n ↦ (hy n).trans (hrR.le.trans hRγ), ?_⟩
    have hd : dist y x ≤ r := hy 0
    change dist y x < (r + R) / 2
    linarith
  · intro y hy
    rw [bowen_orbit_plaque_eq_inter_closedBall f hlam hlam1
      (hr.trans (hrR.le.trans hRγ)) hRγ hc x]
    refine ⟨hy.1, ?_⟩
    have hd : dist y x < (r + R) / 2 := hy.2
    change dist y x ≤ R
    linarith

end HolomorphicAnosov
