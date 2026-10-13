import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricContractingBracket
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowNegCoe
import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
open Set
open scoped _root_.HolomorphicAnosov.Topology _root_.Topology Classical
noncomputable section

/-- Contracting compact product data supplies a continuous unique bracket in any
compatible metric at any positive plaque radius bounded by half an expansive
constant. Restrict the same product bracket and use its pairwise contractions
with the endpoint itself. The general compatible-metric bracket theorem then
supplies the original close-pair radius and uniqueness. -/
theorem compact_product_original_bracket {X : Type*} [new : MetricSpace X]
    [CompactSpace X] (F : X ≃ₜ X) {κ γ : ℝ}
    (prod : Bowen.CompactLocalProductData F γ κ) (old : MetricSpace X)
    (ht : old.toUniformSpace.toTopologicalSpace = new.toUniformSpace.toTopologicalSpace)
    {e b : ℝ} (hb : 0 < b) (hbe : 2 * b ≤ e)
    (hexp : ∀ x y : X, (∀ j : ℤ, old.dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y) :
    letI : MetricSpace X := new
    ∃ ε > 0, ∃ B : {p : X × X // old.dist p.1 p.2 ≤ ε} → X,
      Continuous B ∧
      (∀ p, (∀ n : ℕ, old.dist ((F ^ (n : ℤ)) (B p)) ((F ^ (n : ℤ)) p.val.1) ≤ b) ∧
        (∀ n : ℕ, old.dist ((F ^ (-(n : ℤ))) (B p)) ((F ^ (-(n : ℤ))) p.val.2) ≤ b)) ∧
      (∀ p z, (∀ n : ℕ, old.dist ((F ^ (n : ℤ)) z) ((F ^ (n : ℤ)) p.val.1) ≤ b) →
        (∀ n : ℕ, old.dist ((F ^ (-(n : ℤ))) z) ((F ^ (-(n : ℤ))) p.val.2) ≤ b) →
        z = B p) := by
  let : MetricSpace X := new
  let B : {p : X × X // dist p.1 p.2 ≤ prod.closeRadius} → X :=
    fun p ↦ prod.bracket p.val.1 p.val.2
  have hB : Continuous B := prod.bracket_continuous.domRestrict
  have hdiag : ∀ x : X, B ⟨(x, x), by simpa using prod.closeRadius_pos.le⟩ = x := by
    intro x
    apply Eq.symm
    apply prod.bracket_unique x x x (by simpa using prod.closeRadius_pos.le)
    constructor <;> intro n <;> simpa using prod.gamma_pos.le
  have hs : ∀ p, ∀ n : ℕ,
      dist ((F ^ (n : ℤ)) (B p)) ((F ^ (n : ℤ)) p.val.1) ≤
        κ ^ n * dist (B p) p.val.1 := by
    intro p n
    have hm := (prod.bracket_mem p.val.1 p.val.2 p.property).1
    have hself : p.val.1 ∈ relativeClosedStablePlaque F γ p.val.1 := by
      intro k
      simpa using prod.gamma_pos.le
    simpa only [zpow_natCast, CarrierAdapter.homeomorph_pow_coe] using
      prod.stable_contraction p.val.1 (B p) p.val.1 hm hself n
  have hu : ∀ p, ∀ n : ℕ,
      dist ((F ^ (-(n : ℤ))) (B p)) ((F ^ (-(n : ℤ))) p.val.2) ≤
        κ ^ n * dist (B p) p.val.2 := by
    intro p n
    have hm := (prod.bracket_mem p.val.1 p.val.2 p.property).2
    have hself : p.val.2 ∈ relativeClosedUnstablePlaque F γ p.val.2 := by
      intro k
      simpa using prod.gamma_pos.le
    simpa only [CarrierAdapter.homeomorph_zpow_neg_coe] using
      prod.unstable_contraction p.val.2 (B p) p.val.2 hm hself n
  exact MetricAdapter.compatible_metric_contracting_bracket F prod.closeRadius_pos
    prod.lambda_pos.le prod.lambda_lt_one.le B hB hdiag hs hu old ht hb hbe hexp

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
