import Mathlib.Topology.Path
import Mathlib.Tactic.Linarith

open Set
namespace HolomorphicAnosov

/-- Contact order is preserved when two consistently oriented paths are concatenated.

Source: Cairns (1951), §3(D,E), pp.862–863, assembly of the two half-fronts at the
first perpendicular contact. On either half, the concatenation parameter is a
strictly increasing affine rescaling, so the asserted order is the given half
order. Across the join, the first half's contacts precede the common contact
and the second half's contacts follow it. In the reverse cross case an ordered
pair would force the second half's parameter to be zero, contradicting its
strict location after the join. This argument concerns only parameter order;
it uses no planar separation or contact-exhaustion assertion. -/
theorem path_trans_contact_order {X : Type*} [TopologicalSpace X]
    (μ : unitInterval → X) (k : unitInterval)
    (a : Path (μ 0) (μ k)) (b : Path (μ k) (μ 1))
    (ha : ∀ s t u v : unitInterval, a s = μ u → a t = μ v →
      (u ≤ v ↔ s ≤ t))
    (hb : ∀ s t u v : unitInterval, b s = μ u → b t = μ v →
      (u ≤ v ↔ s ≤ t)) :
    ∀ s t u v : unitInterval, (a.trans b) s = μ u → (a.trans b) t = μ v →
      (u ≤ v ↔ s ≤ t) := by
  intro s t u v hs ht
  rw [Path.trans_apply] at hs ht
  split_ifs at hs ht with hsHalf htHalf htHalf
  · have ho := ha _ _ _ _ hs ht
    constructor
    · intro huv
      have hst := ho.mp huv
      change (2 : ℝ) * s ≤ 2 * t at hst
      exact_mod_cast (show (s : ℝ) ≤ t by linarith)
    · intro hst
      apply ho.mpr
      change (2 : ℝ) * s ≤ 2 * t
      exact mul_le_mul_of_nonneg_left hst (by norm_num)
  · have huk : u ≤ k := (ha _ 1 u k hs a.target).mpr (by exact le_top)
    have hkv : k ≤ v := (hb 0 _ k v b.source ht).mpr (by exact bot_le)
    exact iff_of_true (huk.trans hkv) (by change (s : ℝ) ≤ t; linarith)
  · have hvk : v ≤ k := (ha _ 1 v k ht a.target).mpr (by exact le_top)
    constructor
    · intro huv
      have hs0 := (hb _ 0 u k hs b.source).mp (huv.trans hvk)
      change (2 : ℝ) * s - 1 ≤ 0 at hs0
      exfalso
      linarith
    · intro hst
      change (s : ℝ) ≤ t at hst
      exfalso
      linarith
  · have ho := hb _ _ _ _ hs ht
    constructor
    · intro huv
      have hst := ho.mp huv
      change (2 : ℝ) * s - 1 ≤ 2 * t - 1 at hst
      exact_mod_cast (show (s : ℝ) ≤ t by linarith)
    · intro hst
      apply ho.mpr
      change (2 : ℝ) * s - 1 ≤ 2 * t - 1
      have hh : (s : ℝ) ≤ t := hst
      linarith

end HolomorphicAnosov
