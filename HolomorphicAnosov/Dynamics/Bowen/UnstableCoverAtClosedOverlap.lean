import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData
import HolomorphicAnosov.Dynamics.Bowen.BracketCovarianceOfGuards
import HolomorphicAnosov.Dynamics.Bowen.StableTransitiveOnSmallCell

/-!
# Closed-overlap ingredients for Bowen Markov rectangles

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Fact 1 pp.726–727, Lemma 11(a) pp.730–731 and Lemma 25 pp.739–740.
All distances, orbit plaques, bracket guards and compact cells are unchanged.
-/

namespace HolomorphicAnosov.BowenBasicSetCoding
open Set
variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Bowen Lemma25 unstable covering at a CLOSED overlap. Transport the target point
to the interior witness, use only its witnessed cover, then rebase the actual preimage.
Small-cell stable transitivity replaces the source's compressed absorption calculation. -/
theorem unstable_cover_at_closed_overlap (F : X ≃ₜ X) (γ lam : ℝ)
    (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (E T : Set X) (hEc : IsCompact E) (hTc : IsCompact T)
    (hEd : Metric.diam E ≤ H.closeRadius) (hTd : Metric.diam T ≤ H.closeRadius)
    (hTsmall : 2 * Metric.diam T ≤ γ)
    (hEb : ∀ p ∈ E, ∀ q ∈ E, H.bracket p q ∈ E)
    (hTb : ∀ p ∈ T, ∀ q ∈ T, H.bracket p q ∈ T)
    (hzero : ∀ p ∈ E, ∀ q ∈ E, F p ∈ T → F q ∈ T →
      dist (F (H.bracket p q)) (F q) ≤ γ)
    (w : X) (_hw : w ∈ E) (hfw : F w ∈ T)
    (hcover : T ∩ Dynamics.relativeClosedUnstablePlaque F γ (F w) ⊆
      F '' (E ∩ Dynamics.relativeClosedUnstablePlaque F γ w))
    (x : X) (hx : x ∈ E) (hfx : F x ∈ T) :
    T ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
      F '' (E ∩ Dynamics.relativeClosedUnstablePlaque F γ x) := by
  intro t ht
  let r := H.bracket t (F w)
  have hcloseT : ∀ a ∈ T, ∀ b ∈ T, dist a b ≤ H.closeRadius :=
    fun a ha b hb ↦ (Metric.dist_le_diam_of_mem hTc.isBounded ha hb).trans hTd
  have hrT : r ∈ T := hTb t ht.1 (F w) hfw
  have hrplaques := H.bracket_mem t (F w) (hcloseT t ht.1 (F w) hfw)
  obtain ⟨q, hq, hfq⟩ := hcover ⟨hrT, hrplaques.2⟩
  let v := H.bracket q x
  have hqx : dist q x ≤ H.closeRadius :=
    (Metric.dist_le_diam_of_mem hEc.isBounded hq.1 hx).trans hEd
  have hvE : v ∈ E := hEb q hq.1 x hx
  have hvplaques := H.bracket_mem q x hqx
  have hcov : F v = H.bracket (F q) (F x) :=
    Dynamics.Bowen.bracket_covariance_of_guards F γ lam H hqx
      (hcloseT (F q) (hfq ▸ hrT) (F x) hfx)
      (hzero q hq.1 x hx (hfq ▸ hrT) hfx)
  let u := H.bracket r (F x)
  have huT : u ∈ T := hTb r hrT (F x) hfx
  have huplaques := H.bracket_mem r (F x) (hcloseT r hrT (F x) hfx)
  have huStable : u ∈ Dynamics.relativeClosedStablePlaque F γ t :=
    stable_transitive_on_small_cell F γ lam H T hTc hTsmall
      ht.1 hrT huT hrplaques.1 huplaques.1
  have hut : u = t := by
    have heq1 := H.bracket_unique t (F x) u (hcloseT t ht.1 (F x) hfx)
      ⟨huStable, huplaques.2⟩
    have heq2 := H.bracket_unique t (F x) t (hcloseT t ht.1 (F x) hfx)
      ⟨(fun n ↦ by simpa using H.gamma_pos.le), ht.2⟩
    exact heq1.trans heq2.symm
  refine ⟨v, ⟨hvE, hvplaques.2⟩, ?_⟩
  rw [hfq] at hcov
  exact hcov.trans hut



end HolomorphicAnosov.BowenBasicSetCoding
