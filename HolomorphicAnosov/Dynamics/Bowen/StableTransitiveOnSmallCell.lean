import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData
import Mathlib.Tactic.Ring

/-!
# Closed-overlap ingredients for Bowen Markov rectangles

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Fact 1 pp.726–727, Lemma 11(a) pp.730–731 and Lemma 25 pp.739–740.
All distances, orbit plaques, bracket guards and compact cells are unchanged.
-/

namespace HolomorphicAnosov.BowenBasicSetCoding
open Set
variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Small-cell stable transitivity is justified by the actual pairwise plaque
contraction and 2*diam≤γ; the full γ relation is not silently declared transitive. -/
theorem stable_transitive_on_small_cell (F : X ≃ₜ X) (γ lam : ℝ)
    (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (R : Set X) (hc : IsCompact R) (hd : 2 * Metric.diam R ≤ γ)
    {p q r : X} (hp : p ∈ R) (hq : q ∈ R) (hr : r ∈ R)
    (hpq : q ∈ Dynamics.relativeClosedStablePlaque F γ p)
    (hqr : r ∈ Dynamics.relativeClosedStablePlaque F γ q) :
    r ∈ Dynamics.relativeClosedStablePlaque F γ p := by
  intro n
  have hpow : lam ^ n ≤ 1 := pow_le_one₀ H.lambda_pos.le H.lambda_lt_one.le
  have h1 := H.stable_contraction q r q hqr (fun n ↦ by simpa using H.gamma_pos.le) n
  have h2 := H.stable_contraction p q p hpq (fun n ↦ by simpa using H.gamma_pos.le) n
  have hd1 := Metric.dist_le_diam_of_mem hc.isBounded hr hq
  have hd2 := Metric.dist_le_diam_of_mem hc.isBounded hq hp
  have hbound1 : dist ((F : X → X)^[n] r) ((F : X → X)^[n] q) ≤ Metric.diam R :=
    h1.trans ((mul_le_mul_of_nonneg_right hpow (dist_nonneg : 0 ≤ dist r q)).trans
      (by simpa using hd1))
  have hbound2 : dist ((F : X → X)^[n] q) ((F : X → X)^[n] p) ≤ Metric.diam R :=
    h2.trans ((mul_le_mul_of_nonneg_right hpow (dist_nonneg : 0 ≤ dist q p)).trans
      (by simpa using hd2))
  calc
    dist ((F : X → X)^[n] r) ((F : X → X)^[n] p) ≤
        dist ((F : X → X)^[n] r) ((F : X → X)^[n] q) +
          dist ((F : X → X)^[n] q) ((F : X → X)^[n] p) := dist_triangle _ _ _
    _ ≤ Metric.diam R + Metric.diam R := add_le_add hbound1 hbound2
    _ = 2 * Metric.diam R := by ring
    _ ≤ γ := hd



end HolomorphicAnosov.BowenBasicSetCoding
