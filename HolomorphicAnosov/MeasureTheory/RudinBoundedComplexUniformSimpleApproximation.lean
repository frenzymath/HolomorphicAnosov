import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
Uniform approximation of bounded measurable complex functions by simple functions with a dyadic
error bound. (Rudin, Thms 1.17 and 6.16)
-/

namespace HolomorphicAnosov

open Filter MeasureTheory

/-- Every bounded measurable complex function has uniformly convergent simple approximants with
error at most `4 * 2 ^ (-(N + k))` for every initial index `N ≥ 1` bounding its norm. Such an
initial index exists. (Rudin, Thms 1.17 and 6.16) -/
theorem rudin_bounded_complex_uniform_simple_approximation
    {X : Type*} [MeasurableSpace X] (b : X → ℂ) (hb : Measurable b)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x : X, ‖b x‖ ≤ B) :
    (∃ N : ℕ, 1 ≤ N ∧ B ≤ (N : ℝ)) ∧
      ∀ N : ℕ, 1 ≤ N → B ≤ (N : ℝ) →
        ∃ s : ℕ → SimpleFunc X ℂ,
          (∀ (k : ℕ) (x : X),
            ‖s k x - b x‖ ≤ 4 * (2 : ℝ) ^ (-((N + k : ℕ) : ℤ))) ∧
          TendstoUniformly (fun k x ↦ s k x) b atTop := by
  classical
  constructor
  · obtain ⟨m, hm⟩ := exists_nat_gt B
    refine ⟨m + 1, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
    exact hm.le.trans (by exact_mod_cast Nat.le_succ m)
  intro N hN hBN
  let a (j : Fin 4) (x : X) : ℝ :=
    match j.val with
    | 0 => max (b x).re 0
    | 1 => max (-(b x).re) 0
    | 2 => max (b x).im 0
    | _ => max (-(b x).im) 0
  have hameas (j : Fin 4) : Measurable (a j) := by
    fin_cases j <;> dsimp [a]
    · exact (Complex.continuous_re.measurable.comp hb).max measurable_const
    · exact (Complex.continuous_re.measurable.comp hb).neg.max measurable_const
    · exact (Complex.continuous_im.measurable.comp hb).max measurable_const
    · exact (Complex.continuous_im.measurable.comp hb).neg.max measurable_const
  have ha (j : Fin 4) (x : X) : 0 ≤ a j x ∧ a j x ≤ B := by
    have hr := abs_le.mp ((Complex.abs_re_le_norm (b x)).trans (hbound x))
    have hi := abs_le.mp ((Complex.abs_im_le_norm (b x)).trans (hbound x))
    fin_cases j <;> simp only [a] <;> constructor
    all_goals first | exact le_max_right _ _ | exact max_le (by linarith) hB
  
  
  let q (n : ℕ) (j : Fin 4) : SimpleFunc X ℕ :=
    { toFun := fun x ↦ ⌊a j x * (2 : ℝ) ^ n⌋₊
      measurableSet_fiber' := fun k ↦
        ((hameas j).mul_const ((2 : ℝ) ^ n)).nat_floor (measurableSet_singleton k)
      finite_range' := (Set.finite_Iic ⌊B * (2 : ℝ) ^ n⌋₊).subset (by
        rintro k ⟨x, rfl⟩
        exact Nat.floor_mono (mul_le_mul_of_nonneg_right (ha j x).2 (by positivity))) }
  let r (n : ℕ) (j : Fin 4) : SimpleFunc X ℝ :=
    (q n j).map (fun k : ℕ ↦ (k : ℝ) / (2 : ℝ) ^ n)
  have herr (n : ℕ) (j : Fin 4) (x : X) :
      |r n j x - a j x| ≤ ((2 : ℝ) ^ n)⁻¹ := by
    have hp : 0 < (2 : ℝ) ^ n := by positivity
    have hlo := Nat.floor_le (mul_nonneg (ha j x).1 hp.le)
    have hhi := Nat.lt_floor_add_one (a j x * (2 : ℝ) ^ n)
    change |(⌊a j x * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n - a j x| ≤ _
    apply abs_le.mpr
    constructor
    · have ht : a j x - ((2 : ℝ) ^ n)⁻¹ ≤
          (⌊a j x * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n := by
        apply (le_div_iff₀ hp).mpr
        have hid : ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n = 1 := inv_mul_cancel₀ hp.ne'
        nlinarith
      linarith
    · have ht := (div_le_iff₀ hp).mpr hlo
      exact (sub_nonpos.mpr ht).trans (inv_nonneg.mpr hp.le)
  let s (k : ℕ) : SimpleFunc X ℂ :=
    (r (N + k) 0).map Complex.ofReal - (r (N + k) 1).map Complex.ofReal +
      ((r (N + k) 2).map Complex.ofReal - (r (N + k) 3).map Complex.ofReal) *
        SimpleFunc.const X Complex.I
  have hs (k : ℕ) (x : X) :
      ‖s k x - b x‖ ≤ 4 * (2 : ℝ) ^ (-((N + k : ℕ) : ℤ)) := by
    have h0 := abs_le.mp (herr (N + k) 0 x)
    have h1 := abs_le.mp (herr (N + k) 1 x)
    have h2 := abs_le.mp (herr (N + k) 2 x)
    have h3 := abs_le.mp (herr (N + k) 3 x)
    have hr : a 0 x - a 1 x = (b x).re := max_zero_sub_max_neg_zero_eq_self _
    have hi : a 2 x - a 3 x = (b x).im := max_zero_sub_max_neg_zero_eq_self _
    have hreal : |r (N + k) 0 x - r (N + k) 1 x - (b x).re| ≤
        2 * ((2 : ℝ) ^ (N + k))⁻¹ := abs_le.mpr ⟨by linarith, by linarith⟩
    have himag : |r (N + k) 2 x - r (N + k) 3 x - (b x).im| ≤
        2 * ((2 : ℝ) ^ (N + k))⁻¹ := abs_le.mpr ⟨by linarith, by linarith⟩
    have hn := Complex.norm_le_abs_re_add_abs_im (s k x - b x)
    simp only [s, SimpleFunc.coe_add, SimpleFunc.coe_sub, SimpleFunc.coe_mul,
      SimpleFunc.map_apply, SimpleFunc.const_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
      sub_zero, mul_zero, mul_one, zero_add, add_zero] at hn
    rw [zpow_neg, zpow_natCast]
    exact hn.trans (by linarith)
  refine ⟨s, hs, ?_⟩
  have hdecay : Tendsto (fun k : ℕ ↦ 4 * (2 : ℝ) ^ (-((N + k : ℕ) : ℤ)))
      atTop (nhds 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul
        (4 * ((2 : ℝ) ^ N)⁻¹)
    simp only [zpow_neg, zpow_natCast]
    simpa only [pow_add, mul_inv_rev, inv_pow, mul_assoc,
      mul_left_comm, mul_comm, mul_zero, zero_mul] using ht
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hdecay.eventually (gt_mem_nhds hε)] with k hk x
  rw [dist_eq_norm, norm_sub_rev]
  exact (hs k x).trans_lt hk

end HolomorphicAnosov
