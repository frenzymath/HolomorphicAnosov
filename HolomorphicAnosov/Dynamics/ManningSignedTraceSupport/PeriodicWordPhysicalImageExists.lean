import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatchedBlocksCommonImage
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeNatCast
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeSucc
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimePeriod
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPoints
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
open Set BowenBasicSetCoding
open scoped Classical
noncomputable section

/-- Every positive-size periodic tuple word has a periodic physical image. (de Jong, §3.2, pp. 2464–2465; Manning, pp. 216–219) -/
theorem periodicWord_physical_image_exists {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) (T : Matrix (Fin N) (Fin N) ℤ)
    (hT : ∀ i k, T i k = 1 ↔ B i k) {e : ℝ} (he : 0 < e)
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (R i) < e / 2)
    (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j))
    {r m : ℕ} (c : Composition (r + 1)) (hm : 0 < m)
    (w : PeriodicWord R T c hm) :
    ∃ x : X, x ∈ periodicPhysicalPoints R T c F hm w := by
  let k₀ : Fin c.length := ⟨0, c.length_pos_of_pos (Nat.succ_pos r)⟩
  let : Nonempty (Fin c.length) := ⟨k₀⟩
  have hcast := integerPeriodicTime_natCast hm
  have hnext := integerPeriodicTime_succ hm
  have hperiod := integerPeriodicTime_period hm
  let S : ℤ → Fin c.length → Finset (Fin N) := fun j k ↦ (w.val (integerPeriodicTime hm j)).val k
  obtain ⟨x, hx⟩ := matched_blocks_common_image F R B coding T hT hexp hsmall horbit S
    (fun j k ↦ (w.val (integerPeriodicTime hm j)).property.1 k)
    (fun j ↦ (w.val (integerPeriodicTime hm j)).property.2.2.2)
    (by
      intro j k
      simpa only [S, hnext] using w.property (integerPeriodicTime hm j) k)
  have hfix : (F ^ (m : ℤ)) x = x := by
    apply hexp
    intro j
    obtain ⟨i, hi⟩ := (w.val (integerPeriodicTime hm j)).property.1 k₀
    have hxi := hx j k₀ i hi
    have hmi := hx (j + m) k₀ i (by simpa only [S, hperiod] using hi)
    have hd := Metric.dist_le_diam_of_mem
      (Metric.isBounded_of_compactSpace (s := R i)) hmi hxi
    have he' : Metric.diam (R i) ≤ e := (hsmall i).le.trans (half_le_self he.le)
    simpa only [zpow_add, Homeomorph.mul_apply] using hd.trans he'
  refine ⟨x, ?_, ?_⟩
  · simpa only [zpow_natCast, CarrierAdapter.homeomorph_pow_coe] using hfix
  · intro t k i hi
    have h := hx (t.val : ℤ) k i (by simpa only [S, hcast] using hi)
    simpa only [zpow_natCast, CarrierAdapter.homeomorph_pow_coe] using h

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
