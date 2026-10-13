import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

open Set

namespace HolomorphicAnosov.Analysis

/-- The positive-radical substitution of Whittaker–Watson §22.32, p.501.
Put D=1-(1-k²)t² and s=1/√D. Then D≥k² on [0,1], giving continuity
and endpoint values. Differentiation gives s'=(1-k²)t/(√D)³. Squaring
the positive radicals gives √(s²-1)=√(1-k²)t/√D and
√(1-k²s²)=√(1-k²)√(1-t²)/√D; cancellation yields the integrand identity. -/
theorem whittakerWatsonSubstitution (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    let σ := fun t : ℝ ↦ (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2))⁻¹
    let σ' := fun t : ℝ ↦ (1 - k ^ 2) * t /
      (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2)) ^ 3
    ContinuousOn σ (Icc 0 1) ∧ σ 0 = 1 ∧ σ 1 = 1 / k ∧
      (∀ t ∈ Ioo 0 1, HasDerivAt σ (σ' t) t ∧ 0 ≤ σ' t ∧
        1 < σ t ∧ σ t < 1 / k ∧
        (1 / (Real.sqrt ((σ t) ^ 2 - 1) * Real.sqrt (1 - k ^ 2 * (σ t) ^ 2))) *
          σ' t = 1 / (Real.sqrt (1 - t ^ 2) *
            Real.sqrt (1 - (Real.sqrt (1 - k ^ 2)) ^ 2 * t ^ 2))) := by
  dsimp only
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk0
  have hc : 0 < 1 - k ^ 2 := by nlinarith
  have hD : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 - (1 - k ^ 2) * t ^ 2 := by
    intro t ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_le_mul_of_nonneg_left ht2 hc.le]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.inv₀
    · fun_prop
    · exact fun t ht ↦ (Real.sqrt_pos.2 (hD t ht)).ne'
  · simp
  · simp [Real.sqrt_sq hk0.le, one_div]
  · intro t ht
    have ht0 : 0 < t := ht.1
    have hDt := hD t ⟨ht.1.le, ht.2.le⟩
    have hq : 0 < Real.sqrt (1 - (1 - k ^ 2) * t ^ 2) := Real.sqrt_pos.2 hDt
    have hq2 := Real.sq_sqrt hDt.le
    have ht2 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hct : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.2 hc
    have hr : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 ht2
    have hc2 := Real.sq_sqrt hc.le
    have hr2 := Real.sq_sqrt ht2.le
    have hderiv : HasDerivAt (fun x : ℝ ↦ (Real.sqrt (1 - (1 - k ^ 2) * x ^ 2))⁻¹)
        ((1 - k ^ 2) * t / (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2)) ^ 3) t := by
      have hpoly := (hasDerivAt_const t (1 : ℝ)).sub
        (((hasDerivAt_id t).pow 2).const_mul (1 - k ^ 2))
      convert (hpoly.sqrt hDt.ne').inv hq.ne' using 1
      · rfl
      · dsimp
        field_simp
        ring
    have hs1 : 1 < (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2))⁻¹ := by
      apply (one_lt_inv₀ hq).2
      apply (Real.sqrt_lt hDt.le zero_le_one).2
      nlinarith [mul_pos hc (sq_pos_of_pos ht.1)]
    have hsR : (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2))⁻¹ < 1 / k := by
      rw [one_div]
      apply (inv_lt_inv₀ hq hk0).2
      apply (Real.lt_sqrt hk0.le).2
      nlinarith [mul_pos hc ht2]
    refine ⟨hderiv, by positivity, hs1, hsR, ?_⟩
    have hrad1 : Real.sqrt ((Real.sqrt (1 - (1 - k ^ 2) * t ^ 2))⁻¹ ^ 2 - 1) =
        Real.sqrt (1 - k ^ 2) * t / Real.sqrt (1 - (1 - k ^ 2) * t ^ 2) := by
      apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [hs1]) (by positivity)).2
      field_simp
      nlinarith [hq2, hc2]
    have hrad2 : Real.sqrt (1 - k ^ 2 * (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2))⁻¹ ^ 2) =
        Real.sqrt (1 - k ^ 2) * Real.sqrt (1 - t ^ 2) /
          Real.sqrt (1 - (1 - k ^ 2) * t ^ 2) := by
      have hspos : 0 < (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2))⁻¹ := inv_pos.2 hq
      have hsprod : k * (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2))⁻¹ < 1 :=
        by
          have h := (lt_div_iff₀ hk0).1 hsR
          nlinarith
      apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [mul_pos hk0 hspos]) (by positivity)).2
      field_simp
      nlinarith [hq2, hc2, hr2, mul_nonneg hc.le ht2.le]
    rw [hrad1, hrad2, hc2]
    field_simp [ht0.ne', hq.ne', hct.ne', hr.ne']
    nlinarith [hq2, hc2]

end HolomorphicAnosov.Analysis
