import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The numerical inside-modulus squeeze

Source: Lehto–Virtanen (1973), Chapter I, Lemma 4.3, p.26, equation (4.15).
-/

namespace HolomorphicAnosov
open Filter Set _root_.Topology

/-- The Rengel bounds from arbitrarily narrow boundary strips force convergence to the
ambient rectangle modulus. Source: Lehto–Virtanen I.Lemma 4.3, p.26, equation (4.15).

Proof: both bounding rational functions of the strip width converge to `M` as the width
tends to zero through positive values. Given a strict lower threshold below `M`, choose
a sufficiently small positive width so that the lower bound exceeds it, then use the
eventual lower estimate. For an upper threshold above `M`, use the upper bound in the
same way. The two eventual inequalities are the order-topology criterion for convergence.
No nesting, positivity of individual terms, or a uniform choice of the eventual index
across all strip widths is assumed. -/
theorem qc_inside_modulus_squeeze {m : ℕ → ℝ} {M : ℝ} (hM : 0 < M)
    (hBound : ∀ ε : ℝ, 0 < ε → ε < min (M / 2) (1 / 2) →
      ∀ᶠ n in atTop, (M - 2 * ε) ^ 2 / M ≤ m n ∧ m n ≤ M / (1 - 2 * ε) ^ 2) :
    Tendsto m atTop (𝓝 M) := by
  have hcap : 0 < min (M / 2) (1 / 2 : ℝ) := lt_min (half_pos hM) (by norm_num)
  have hlower : Tendsto (fun ε : ℝ ↦ (M - 2 * ε) ^ 2 / M) (𝓝[>] 0) (𝓝 M) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ (M - 2 * ε) ^ 2 / M) 0 := by fun_prop
    simpa [pow_two, hM.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun ε : ℝ ↦ M / (1 - 2 * ε) ^ 2) (𝓝[>] 0) (𝓝 M) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ M / (1 - 2 * ε) ^ 2) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < min (M / 2) (1 / 2) :=
    (eventually_lt_nhds hcap).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨ε, hε, hεcap, hεa⟩ :=
      (hpos.and (hsmall.and ((tendsto_order.1 hlower).1 a ha))).exists
    exact (hBound ε hε hεcap).mono (fun n hn ↦ hεa.trans_le hn.1)
  · intro b hb
    obtain ⟨ε, hε, hεcap, hεb⟩ :=
      (hpos.and (hsmall.and ((tendsto_order.1 hupper).2 b hb))).exists
    exact (hBound ε hε hεcap).mono (fun n hn ↦ hn.2.trans_lt hεb)

end HolomorphicAnosov
