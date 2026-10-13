import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NoCrossTransition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

open Set
open BowenBasicSetCoding
noncomputable section

/-- Within a rigid coding fibre, an admissible successor label is forced.
Realize the target label by a code in the same fibre. If that code differed from
the source code, the public no-cross theorem would exclude the alleged edge.
Thus their codes, and hence their next labels, agree. This is Manning's Lemma 2
applied to a label witness; rigidity is only needed on this one fibre. -/
theorem fibre_edge_target_unique {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) {e : ℝ}
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (R i) < e / 2)
    (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j))
    {x : X}
    (hrigid : ∀ a b : CodeSpace B, coding a = x → coding b = x →
      (∃ j : ℤ, a.val j = b.val j) → a = b)
    (hlabel : ∀ j i, (F ^ j) x ∈ R i →
      ∃ a : CodeSpace B, coding a = x ∧ a.val j = i)
    {a : CodeSpace B} (ha : coding a = x) (j : ℤ) {i : Fin N}
    (hi : (F ^ (j + 1)) x ∈ R i) (hedge : B (a.val j) i) :
    i = a.val (j + 1) := by
  obtain ⟨b, hb, hbi⟩ := hlabel (j + 1) i hi
  have hab : a = b := by
    by_contra hne
    exact no_cross_transition F R B coding hexp hsmall horbit hrigid ha hb hne j
      (hbi.symm ▸ hedge)
  simpa only [← hab] using hbi.symm


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
