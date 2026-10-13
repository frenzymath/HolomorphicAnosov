import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordFibreCardBound
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FibreEdgeTargetUnique
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
open Set BowenBasicSetCoding
open scoped Classical
noncomputable section

/-- The number of tuple words supported on one physical point is bounded by `(q+1)^q` when each orbit label has a unique legal successor. (Manning, Lemma 2, p. 217; pp. 218–219) -/
theorem periodicWord_fibre_bound_of_coding {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) (T : Matrix (Fin N) (Fin N) ℤ)
    (hT : ∀ i k, T i k = 1 ↔ B i k) {e : ℝ}
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (R i) < e / 2)
    (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j))
    {r m : ℕ} (c : Composition r) (hm : 0 < m) (hr : r ≤ overlapMultiplicity R) (x : X)
    (hrigid : ((F : X → X)^[m]) x = x →
      ∀ a b : CodeSpace B, coding a = x → coding b = x →
        (∃ j : ℤ, a.val j = b.val j) → a = b)
    (hlabel : ∀ j i, (F ^ j) x ∈ R i →
      ∃ a : CodeSpace B, coding a = x ∧ a.val j = i) :
    Nat.card {w : PeriodicWord R T c hm // x ∈ periodicPhysicalPoints R T c F hm w} ≤
      (overlapMultiplicity R + 1) ^ overlapMultiplicity R := by
  by_cases hper : ((F : X → X)^[m]) x = x
  · apply periodicWord_fibre_card_bound F R T c hm hr x
    intro n i j k hi hj hk hij hik
    have hi' : (F ^ (n : ℤ)) x ∈ R i := by
      simpa only [zpow_natCast, CarrierAdapter.homeomorph_pow_coe] using hi
    have hj' : (F ^ ((n : ℤ) + 1)) x ∈ R j := by
      simpa only [← Nat.cast_add_one, zpow_natCast, CarrierAdapter.homeomorph_pow_coe] using hj
    have hk' : (F ^ ((n : ℤ) + 1)) x ∈ R k := by
      simpa only [← Nat.cast_add_one, zpow_natCast, CarrierAdapter.homeomorph_pow_coe] using hk
    obtain ⟨a, ha, hai⟩ := hlabel (n : ℤ) i hi'
    have hjEq := fibre_edge_target_unique F R B coding hexp hsmall horbit
      (hrigid hper) hlabel ha (n : ℤ) hj' (hai.symm ▸ (hT i j).mp hij)
    have hkEq := fibre_edge_target_unique F R B coding hexp hsmall horbit
      (hrigid hper) hlabel ha (n : ℤ) hk' (hai.symm ▸ (hT i k).mp hik)
    exact hjEq.trans hkEq.symm
  · let : IsEmpty {w : PeriodicWord R T c hm //
        x ∈ periodicPhysicalPoints R T c F hm w} := ⟨fun w ↦ hper w.property.1⟩
    simp

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
