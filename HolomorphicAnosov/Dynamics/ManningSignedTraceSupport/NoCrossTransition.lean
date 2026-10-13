import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SpliceAt
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RelatedCodesSameImage

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal ContDiff Manifold Bundle Classical
noncomputable section
open BowenBasicSetCoding

/-- Related codes with distinct labels cannot realize a transition between those labels. (Manning, Lemma 2, p. 217) -/
theorem no_cross_transition {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) {e : ℝ}
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (R i) < e / 2)
    (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j))
    {x : X}
    (hrigid : ∀ a b : CodeSpace B, coding a = x → coding b = x →
      (∃ j : ℤ, a.val j = b.val j) → a = b)
    {a b : CodeSpace B} (ha : coding a = x) (hb : coding b = x)
    (hne : a ≠ b) (j : ℤ) : ¬ B (a.val j) (b.val (j + 1)) := by
  intro hcross
  let c := spliceAt a b j hcross
  have hca : coding c = coding a := by
    apply related_codes_same_image F R B coding hexp hsmall horbit
    intro k
    refine ⟨(F ^ k) x, ?_, ?_⟩
    · by_cases hk : k ≤ j
      · simpa only [c, spliceAt, ite_eq_left hk, ha] using horbit a k
      · simpa only [c, spliceAt, ite_eq_right hk, hb] using horbit b k
    · simpa only [ha] using horbit a k
  have hceq : c = a := hrigid c a (hca.trans ha) ha
    ⟨j, by simp [c, spliceAt]⟩
  apply hne
  apply hrigid a b ha hb
  refine ⟨j + 1, ?_⟩
  have hnext := congrArg (fun d : CodeSpace B ↦ d.val (j + 1)) hceq
  simpa [c, spliceAt] using hnext.symm


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
