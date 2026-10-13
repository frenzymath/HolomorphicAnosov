import Mathlib.Dynamics.PeriodicPts.Defs
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatchingUniqueOfFibre
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPoints
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

open Set
open BowenBasicSetCoding
noncomputable section

/-- A periodic tuple word with a physical image has unique block matchings when the coding is rigid over that image. (Manning, Lemma 2, p. 217; pp. 218–219) -/
theorem periodicWord_matching_unique {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) (T : Matrix (Fin N) (Fin N) ℤ)
    (hT : ∀ i k, T i k = 1 ↔ B i k) {e : ℝ}
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (R i) < e / 2)
    (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j))
    {r m : ℕ} (c : Composition r) (hm : 0 < m)
    (w : PeriodicWord R T c hm) {x : X}
    (hx : x ∈ periodicPhysicalPoints R T c F hm w)
    (hrigid : ∀ a b : CodeSpace B, coding a = x → coding b = x →
      (∃ j : ℤ, a.val j = b.val j) → a = b)
    (hlabel : ∀ j i, (F ^ j) x ∈ R i →
      ∃ a : CodeSpace B, coding a = x ∧ a.val j = i)
    (t : Fin m) (k : Fin c.length) :
    ∃! a : ↥((w.val t).val k) ≃ ↥((w.val (nextTime hm t)).val k),
      ∀ i, T i.val (a i).val = 1 := by
  apply blockMatching_unique_of_fibre F R B coding T hT hexp hsmall horbit hrigid hlabel
    (t.val : ℤ) _ _ (w.property t k)
  · intro i hi
    simpa only [zpow_natCast, CarrierAdapter.homeomorph_pow_coe] using hx.2 t k i hi
  · intro i hi
    have hper : Function.IsPeriodicPt (F : X → X) m x := hx.1
    have hnext := hx.2 (nextTime hm t) k i hi
    rw [show (nextTime hm t).val = (t.val + 1) % m from rfl,
      hper.iterate_mod_apply] at hnext
    simpa only [← Nat.cast_add_one, zpow_natCast,
      CarrierAdapter.homeomorph_pow_coe] using hnext


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
