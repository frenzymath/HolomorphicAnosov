import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Topology.EMetricSpace.BoundedVariation

open Set MeasureTheory
open scoped ENNReal

namespace HolomorphicAnosov.Analysis

/-- Interior length estimate in Tao, 246C Notes 2 (2018), Theorem 20 proof,
`literature/Tao-246C-Notes2-2018.txt`, lines 263–267; this formalizes the
triangle-inequality/chain-rule passage to rectifiability. Restrict C¹ regularity
to each compact partition segment. The fundamental theorem bounds each chord
by the lower integral of the ordinary derivative norm. Replace closed segments
by half-open ones using Lebesgue-null endpoints, add the adjacent integrals,
and bound their union by the whole open interval. Finally take the supremum
over all monotone finite partitions. Repeated partition points contribute zero.
No derivative or regularity at the two endpoints is assumed. -/
theorem eVariationOn_Ioo_le_lintegral_deriv_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hf : ContDiffOn ℝ 1 f (Ioo a b)) :
    eVariationOn f (Ioo a b) ≤ ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
        ∫⁻ x in Ioc (u 0) (u n), ‖deriv f x‖ₑ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : edist (f (u (n + 1))) (f (u n)) ≤
          ∫⁻ x in Ioc (u n) (u (n + 1)), ‖deriv f x‖ₑ := by
        rw [edist_eq_enorm_sub, restrict_Ioc_eq_restrict_Icc]
        exact enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
          (hf.mono (Icc_subset_Ioo (hus n).1 (hus (n + 1)).2))
          (hu (Nat.le_succ n))
      rw [Finset.sum_range_succ]
      calc
        _ ≤ (∫⁻ x in Ioc (u 0) (u n), ‖deriv f x‖ₑ) +
            ∫⁻ x in Ioc (u n) (u (n + 1)), ‖deriv f x‖ₑ := add_le_add ih hstep
        _ = ∫⁻ x in Ioc (u 0) (u (n + 1)), ‖deriv f x‖ₑ := by
          rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
            Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]
  exact (hsum n).trans (lintegral_mono_set (fun x hx ↦
    ⟨(hus 0).1.trans hx.1, hx.2.trans_lt (hus n).2⟩))


end HolomorphicAnosov.Analysis
