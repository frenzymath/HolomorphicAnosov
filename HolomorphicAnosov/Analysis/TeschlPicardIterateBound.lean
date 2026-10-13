import Mathlib.Analysis.ODE.ExistUnique
import HolomorphicAnosov.Analysis.TeschlPicardOperatorApply

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

lemma wholeNext_iterate_bound (hab : a ≤ b) (ht0 : t0 ∈ Icc a b)
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x0 : E) (K : ℝ≥0)
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    (α β : C(Icc a b, E)) (m : ℕ) (t : Icc a b) :
    dist ((wholeNext (t0 := t0) hab A hA x0)^[m] α t)
      ((wholeNext (t0 := t0) hab A hA x0)^[m] β t) ≤
      (K * |t.1 - t0|) ^ m / m.factorial * dist α β := by
  induction m generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, wholeNext_apply,
      wholeNext_apply, add_sub_add_left_eq_sub,
      ← integral_sub ((hA.clm_apply
        (((wholeNext (t0 := t0) hab A hA x0)^[m] α).continuous.Icc_extend')).intervalIntegrable _ _)
        ((hA.clm_apply
        (((wholeNext (t0 := t0) hab A hA x0)^[m] β).continuous.Icc_extend')).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ τ in uIoc t0 t.1, K ^ (m + 1) * |τ - t0| ^ m / m.factorial * dist α β := by
        rw [norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro t' ht'
        have ht' : t' ∈ Icc a b :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc ht0 t.2) ht'
        simp only [IccExtend, Function.comp_apply]
        rw [projIcc_of_mem hab ht']
        rw [← map_sub]
        calc
          _ ≤ ‖A t'‖ * ‖_‖ := (A t').le_opNorm _
          _ ≤ K * ((K * |t' - t0|) ^ m / m.factorial * dist α β) :=
            mul_le_mul (hK t' ht') (by simpa [dist_eq_norm] using ih ⟨t', ht'⟩)
              (norm_nonneg _) K.2
          _ = K ^ (m + 1) * |t' - t0| ^ m / m.factorial * dist α β := by
            rw [mul_pow, pow_succ']; ring
      _ ≤ (K * |t.1 - t0|) ^ (m + 1) / (m + 1).factorial * dist α β := by
        apply le_of_abs_le
        rw [← abs_intervalIntegral_eq, intervalIntegral.integral_mul_const, intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          abs_mul, abs_div, abs_mul, abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc,
          abs_div, abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div,
          div_div]
        simp only [Nat.abs_cast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          mul_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m + 1)]
        exact le_rfl

end HolomorphicAnosov
