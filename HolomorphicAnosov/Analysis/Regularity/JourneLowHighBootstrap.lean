import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
This file develops Journé’s low/high coefficient bootstrap for weighted interpolation estimates (Journé, 1988).
-/ 

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- The total magnitude of the coefficients of degree at most n. (Journé, 1988) -/
def lowCoefficientMagnitude {ι : Type*} [Fintype ι] (d : ι → ℕ) (n : ℕ) (c : ι → ℝ) : ℝ :=
  ∑ i, if d i ≤ n then |c i| else 0

/-- The high coefficients normalized by the desired approximation exponent. (Journé, 1988) -/
def highCoefficientMagnitude {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (n : ℕ) (τ t : ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, if n < d i then |c i| *t^((d i:ℝ)-τ) else 0

/-- A weighted interpolation update controls the low coefficient magnitude. (Journé, 1988) -/
theorem low_coefficient_magnitude_step {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (n : ℕ) (c c' : ι → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    lowCoefficientMagnitude d n c' ≤ lowCoefficientMagnitude d n c+
      (t^n)⁻¹*(∑ i, |c' i-c i| *t^(d i)) := by
  classical
  unfold lowCoefficientMagnitude
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : d i ≤ n
  · simp only [ite_eq_left hi]
    have hp : t^n ≤ t^(d i) := pow_le_pow_of_le_one ht.le ht1 hi
    have he : (t^n)⁻¹*t^n = 1 := inv_mul_cancel₀ (pow_ne_zero _ ht.ne')
    have hw : 1 ≤ (t^n)⁻¹*t^(d i) := by
      rw [← he]
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    have hdiff := norm_sub_le (c' i-c i) (-c i)
    simp only [sub_neg_eq_add,sub_add_cancel,Real.norm_eq_abs,abs_neg] at hdiff
    have hb := mul_le_mul_of_nonneg_left hw (abs_nonneg (c' i-c i))
    nlinarith
  · simp only [ite_eq_right hi,zero_add]
    positivity

/-- A weighted interpolation update controls the high magnitude at its new scale, before comparing that scale with the preceding one. (Journé, 1988) -/
theorem high_coefficient_magnitude_step {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (n : ℕ) (τ : ℝ) (c c' : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    highCoefficientMagnitude d n τ t c' ≤ highCoefficientMagnitude d n τ t c+
      t^(-τ)*(∑ i, |c' i-c i| *t^(d i)) := by
  classical
  unfold highCoefficientMagnitude
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have he : t^(-τ)*t^(d i) = t^((d i:ℝ)-τ) := by
    rw [← Real.rpow_natCast,← Real.rpow_add ht]
    congr 1
    ring
  by_cases hi : n < d i
  · simp only [ite_eq_left hi]
    have hdiff := norm_sub_le (c' i-c i) (-c i)
    simp only [sub_neg_eq_add,sub_add_cancel,Real.norm_eq_abs,abs_neg] at hdiff
    have H := mul_le_mul_of_nonneg_right hdiff (Real.rpow_nonneg ht.le ((d i:ℝ)-τ))
    calc
      |c' i| *t^((d i:ℝ)-τ) ≤ (|c' i-c i|+|c i|)*t^((d i:ℝ)-τ) := H
      _ = _ := by rw [← he]; ring
  · simp only [ite_eq_right hi,zero_add]
    positivity

/-- Passing to the smaller geometric scale contracts the old high terms by at least θ^(1−α), since every high total degree is at least n+1. (Journé, 1988) -/
theorem high_coefficient_scale_contraction {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (n : ℕ) (α : ℝ) (c : ι → ℝ) {t θ : ℝ}
    (ht : 0 < t) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    highCoefficientMagnitude d n ((n:ℝ)+α) (θ*t) c ≤
      θ^(1-α)*highCoefficientMagnitude d n ((n:ℝ)+α) t c := by
  classical
  unfold highCoefficientMagnitude
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : n < d i
  · simp only [ite_eq_left hi,Real.mul_rpow hθ.le ht.le]
    have hd : 1-α ≤ (d i:ℝ)-((n:ℝ)+α) := by
      have : (n:ℝ)+1 ≤ (d i:ℝ) := by exact_mod_cast hi
      linarith
    have H := Real.rpow_le_rpow_of_exponent_ge hθ hθ1 hd
    have H' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left H (abs_nonneg (c i)))
      (Real.rpow_nonneg ht.le ((d i:ℝ)-((n:ℝ)+α)))
    nlinarith
  · simp only [ite_eq_right hi,mul_zero,le_refl]

/-- The actual weighted coefficient increment supplied by interpolation implies the coupled low/high recurrences. (Journé, 1988) -/
theorem weighted_increment_low_high_recurrence {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (n : ℕ) (α : ℝ) (c c' : ι → ℝ) {t θ A δ : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hA : 0 ≤ A) (hδ1 : δ ≤ 1)
    (hstep : ∑ i, |c' i-c i| *(θ*t)^(d i) ≤ A*t^((n:ℝ)+α)*
      (1+lowCoefficientMagnitude d n c+δ*highCoefficientMagnitude d n ((n:ℝ)+α) t c)) :
    (lowCoefficientMagnitude d n c' ≤ lowCoefficientMagnitude d n c+
      (A*(θ^n)⁻¹*t^α)*
        (1+lowCoefficientMagnitude d n c+highCoefficientMagnitude d n ((n:ℝ)+α) t c)) ∧
    (highCoefficientMagnitude d n ((n:ℝ)+α) (θ*t) c' ≤
      (θ^(1-α)+A*θ^(-((n:ℝ)+α))*δ)*highCoefficientMagnitude d n ((n:ℝ)+α) t c+
        (A*θ^(-((n:ℝ)+α)))*(1+lowCoefficientMagnitude d n c)) := by
  have hts : 0 < θ*t := mul_pos hθ ht
  have hts1 : θ*t ≤ 1 := (mul_le_mul_of_nonneg_right hθ1 ht.le).trans (by simpa using ht1)
  have hH : 0 ≤ highCoefficientMagnitude d n ((n:ℝ)+α) t c := by
    unfold highCoefficientMagnitude
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hlowfactor : ((θ*t)^n)⁻¹*(A*t^((n:ℝ)+α)) = A*(θ^n)⁻¹*t^α := by
    rw [mul_pow,Real.rpow_add ht,Real.rpow_natCast]
    field_simp
  have hhighfactor : (θ*t)^(-((n:ℝ)+α))*(A*t^((n:ℝ)+α)) =
      A*θ^(-((n:ℝ)+α)) := by
    rw [Real.mul_rpow hθ.le ht.le]
    have he : t^(-((n:ℝ)+α))*t^((n:ℝ)+α) = 1 := by
      rw [← Real.rpow_add ht,neg_add_cancel,Real.rpow_zero]
    calc
      _ = A*θ^(-((n:ℝ)+α))*(t^(-((n:ℝ)+α))*t^((n:ℝ)+α)) := by ring
      _ = _ := by rw [he,mul_one]
  constructor
  · calc
      lowCoefficientMagnitude d n c' ≤ lowCoefficientMagnitude d n c+
          ((θ*t)^n)⁻¹*(∑ i, |c' i-c i| *(θ*t)^(d i)) :=
        low_coefficient_magnitude_step d n c c' hts hts1
      _ ≤ lowCoefficientMagnitude d n c+((θ*t)^n)⁻¹*
          (A*t^((n:ℝ)+α)*(1+lowCoefficientMagnitude d n c+
            δ*highCoefficientMagnitude d n ((n:ℝ)+α) t c)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep
          (show 0 ≤ ((θ*t)^n)⁻¹ by positivity))
      _ = lowCoefficientMagnitude d n c+(A*(θ^n)⁻¹*t^α)*
          (1+lowCoefficientMagnitude d n c+δ*highCoefficientMagnitude d n ((n:ℝ)+α) t c) := by
        rw [← mul_assoc,hlowfactor]
      _ ≤ _ := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (show 0 ≤ A*(θ^n)⁻¹*t^α by positivity)
        nlinarith
  · calc
      highCoefficientMagnitude d n ((n:ℝ)+α) (θ*t) c' ≤
          highCoefficientMagnitude d n ((n:ℝ)+α) (θ*t) c+
          (θ*t)^(-((n:ℝ)+α))*(∑ i, |c' i-c i| *(θ*t)^(d i)) :=
        high_coefficient_magnitude_step d n _ c c' hts
      _ ≤ θ^(1-α)*highCoefficientMagnitude d n ((n:ℝ)+α) t c+
          (θ*t)^(-((n:ℝ)+α))*(A*t^((n:ℝ)+α)*
            (1+lowCoefficientMagnitude d n c+δ*highCoefficientMagnitude d n ((n:ℝ)+α) t c)) :=
        add_le_add (high_coefficient_scale_contraction d n α c ht hθ hθ1)
          (mul_le_mul_of_nonneg_left hstep (by positivity))
      _ = _ := by rw [← mul_assoc,hhighfactor]; ring


/-- Journé's coefficient bootstrap in low/high form. (Journé, 1988) -/
theorem low_high_coefficient_bootstrap
    (L H : ℕ → ℝ) {ε B q ρ M D : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 1 ≤ M) (hD : 1 ≤ D)
    (hcontract : q*D+3*B ≤ D)
    (hsmall : ε*(3+D)/(1-ρ) ≤ 1)
    (hL0 : L 0 ≤ M) (hH0 : H 0 ≤ D*M)
    (hLstep : ∀ m, L (m+1) ≤ L m+ε*ρ^m*(1+L m+H m))
    (hHstep : ∀ m, H (m+1) ≤ q*H m+B*(1+L m)) :
    ∀ m, L m ≤ 2*M ∧ H m ≤ D*M := by
  have hden : 0 < 1-ρ := by linarith
  have hεD : 0 ≤ ε*(3+D) := by positivity
  have hsum (m : ℕ) : ∑ j ∈ Finset.range m, ρ^j ≤ 1/(1-ρ) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hρ hρ1
  have hlowbound (m : ℕ) :
      M+ε*(3+D)*M*(∑ j ∈ Finset.range m, ρ^j) ≤ 2*M := by
    have h₁ := mul_le_mul_of_nonneg_left (hsum m) (mul_nonneg hεD (by linarith : 0 ≤ M))
    have h₂ := mul_le_mul_of_nonneg_right hsmall (by linarith : 0 ≤ M)
    have heq : ε*(3+D)*M*(1/(1-ρ)) = (ε*(3+D)/(1-ρ))*M := by ring
    rw [heq] at h₁
    linarith
  have Hstrong (m : ℕ) :
      L m ≤ M+ε*(3+D)*M*(∑ j ∈ Finset.range m, ρ^j) ∧ H m ≤ D*M := by
    induction m with
    | zero => simpa using And.intro hL0 hH0
    | succ m ih =>
      have hLm : L m ≤ 2*M := ih.1.trans (hlowbound m)
      have hbound : 1+L m+H m ≤ (3+D)*M := by nlinarith [ih.2]
      constructor
      · calc
          L (m+1) ≤ L m+ε*ρ^m*(1+L m+H m) := hLstep m
          _ ≤ (M+ε*(3+D)*M*(∑ j ∈ Finset.range m, ρ^j))+
              ε*ρ^m*((3+D)*M) := add_le_add ih.1
                (mul_le_mul_of_nonneg_left hbound (by positivity))
          _ = _ := by rw [Finset.sum_range_succ]; ring
      · calc
          H (m+1) ≤ q*H m+B*(1+L m) := hHstep m
          _ ≤ q*(D*M)+B*(1+2*M) := add_le_add
            (mul_le_mul_of_nonneg_left ih.2 hq)
            (mul_le_mul_of_nonneg_left (by linarith) hB)
          _ ≤ (q*D+3*B)*M := by nlinarith
          _ ≤ D*M := mul_le_mul_of_nonneg_right hcontract (by linarith)
  exact fun m ↦ ⟨(Hstrong m).1.trans (hlowbound m),(Hstrong m).2⟩

end HolomorphicAnosov.JourneLeafPolynomialApproximation
