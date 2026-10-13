import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace HolomorphicAnosov
noncomputable section
open Filter MeasureTheory in
open scoped Topology in
/-- An eventual geometric square bound by Jacobians of fixed integral implies eventual square-
integrability and convergence of the squared L² integrals to zero. (Zhang, Lemma 4.3, (30)–(31)) -/
theorem zhang_jacobian_dominated_square_decay
    {M : Type*} [MeasurableSpace M] (ν : Measure M)
    (b J : ℕ → M → ℝ) (C lam : ℝ) (hlam : 1 < lam)
    (hb : ∀ n, AEStronglyMeasurable (b n) ν)
    (hJ : ∀ n, Integrable (J n) ν)
    (hmass : ∀ n, (∫ x, J n x ∂ν) = (ν Set.univ).toReal)
    (hbound : ∀ᶠ n in atTop, ∀ᵐ x ∂ν,
      (b n x) ^ 2 ≤ (C * ((lam ^ n)⁻¹) ^ 2) * J n x) :
    (∀ᶠ n in atTop, Integrable (fun x ↦ (b n x) ^ 2) ν) ∧
      Tendsto (fun n ↦ ∫ x, (b n x) ^ 2 ∂ν) atTop (𝓝 0) := by
  have htail : ∀ᶠ n in atTop,
      Integrable (fun x ↦ (b n x) ^ 2) ν ∧
        (∫ x, (b n x) ^ 2 ∂ν) ≤ (C * ((lam ^ n)⁻¹) ^ 2) * (ν Set.univ).toReal := by
    filter_upwards [hbound] with n hn
    have hg := (hJ n).const_mul (C * ((lam ^ n)⁻¹) ^ 2)
    have hbi : Integrable (fun x ↦ (b n x) ^ 2) ν :=
      hg.mono_nonneg ((hb n).pow 2) (Eventually.of_forall fun x ↦ sq_nonneg _) hn
    refine ⟨hbi, ?_⟩
    calc
      _ ≤ ∫ x, (C * ((lam ^ n)⁻¹) ^ 2) * J n x ∂ν := integral_mono_ae hbi hg hn
      _ = (C * ((lam ^ n)⁻¹) ^ 2) * (ν Set.univ).toReal := by
        rw [integral_const_mul, hmass]
  refine ⟨htail.mono fun n hn ↦ hn.1, ?_⟩
  have hp : Tendsto (fun n : ℕ ↦ (lam⁻¹) ^ n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr (by linarith)) (inv_lt_one_of_one_lt₀ hlam)
  have hdecay : Tendsto (fun n : ℕ ↦
      (C * ((lam ^ n)⁻¹) ^ 2) * (ν Set.univ).toReal) atTop (𝓝 0) := by
    simpa only [inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using
      ((hp.pow 2).const_mul C).mul_const (ν Set.univ).toReal
  exact squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg fun x ↦ sq_nonneg _)
    (htail.mono fun n hn ↦ hn.2) hdecay

end
end HolomorphicAnosov

