import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- Stability of a bounded interpolation inverse under an operator perturbation. (Journé, 1988) -/
theorem perturbed_interpolation_inverse
    {V D : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    (E₀ : V ≃L[ℝ] D) (E : V →L[ℝ] D)
    (hsmall : ‖(1 : D →L[ℝ] D) - E.comp E₀.symm.toContinuousLinearMap‖ ≤ 1 / 2) :
    ∃ T : D →L[ℝ] V,
      E.comp T = ContinuousLinearMap.id ℝ D ∧
      T.comp E = ContinuousLinearMap.id ℝ V ∧
      ‖T‖ ≤ 2 * ‖E₀.symm.toContinuousLinearMap‖ := by
  let G : D →L[ℝ] D := 1 - E.comp E₀.symm.toContinuousLinearMap
  have hG : ‖G‖ < 1 := lt_of_le_of_lt hsmall (by norm_num)
  let K : D →L[ℝ] D := ∑' m : ℕ, G ^ m
  have hright : (E.comp E₀.symm.toContinuousLinearMap) * K = 1 := by
    simpa only [G, sub_sub_cancel] using mul_neg_geom_series G hG
  have hleft : K * (E.comp E₀.symm.toContinuousLinearMap) = 1 := by
    simpa only [G, sub_sub_cancel] using geom_series_mul_neg G hG
  have hK : ‖K‖ ≤ 2 := by
    have h := tsum_geometric_le_of_norm_lt_one G hG
    have hid : ‖(1 : D →L[ℝ] D)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hden : 1 / 2 ≤ 1 - ‖G‖ := by change ‖G‖ ≤ 1 / 2 at hsmall; linarith
    have hi : (1 - ‖G‖)⁻¹ ≤ (2 : ℝ) := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      norm_num
      exact hden
    change ‖K‖ ≤ _ at h
    linarith
  refine ⟨E₀.symm.toContinuousLinearMap.comp K, ?_, ?_, ?_⟩
  · ext x
    exact congrArg (fun L : D →L[ℝ] D ↦ L x) hright
  · ext x
    have h := congrArg (fun L : D →L[ℝ] D ↦ L (E₀ x)) hleft
    have h' : K (E x) = E₀ x := by simpa using h
    change E₀.symm (K (E x)) = x
    rw [h', E₀.symm_apply_apply]
  · calc
      _ ≤ ‖E₀.symm.toContinuousLinearMap‖ * ‖K‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖E₀.symm.toContinuousLinearMap‖ * 2 :=
        mul_le_mul_of_nonneg_left hK (norm_nonneg _)
      _ = _ := mul_comm _ _

/-- The finite matrix evaluation operator, linear in its entries. -/
def finiteEvaluationMatrix {ι κ : Type*} [Fintype ι] [Fintype κ] :
    (κ → ι → ℝ) →ₗ[ℝ] ((ι → ℝ) →L[ℝ] (κ → ℝ)) where
  toFun A := (show (ι → ℝ) →ₗ[ℝ] (κ → ℝ) from
    { toFun := fun c k ↦ ∑ i, c i * A k i
      map_add' := by intro c d; ext k; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro r c; ext k; simp [mul_assoc, Finset.mul_sum] }).toContinuousLinearMap
  map_add' A B := by ext c k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r A := by ext c k; simp [Finset.mul_sum]; congr 1; funext i; ring

/-- Moving finitely many sample points a sufficiently small common distance preserves invertibility of evaluation, with inverse norm at most twice the original one. (Journé, 1988) -/
theorem finite_sampling_stable {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (a : κ → X)
    (E₀ : (ι → ℝ) ≃L[ℝ] (κ → ℝ))
    (hE₀ : ∀ c k, E₀ c k = ∑ i, c i * f i (a k)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : κ → X, ‖b-a‖ < δ →
      ∃ T : (κ → ℝ) →L[ℝ] (ι → ℝ),
        (∀ d k, (∑ i, T d i * f i (b k)) = d k) ∧
        (∀ c, T (fun k ↦ ∑ i, c i * f i (b k)) = c) ∧
        ‖T‖ ≤ 2 * ‖E₀.symm.toContinuousLinearMap‖ := by
  classical
  let E : (κ → X) → ((ι → ℝ) →L[ℝ] (κ → ℝ)) :=
    fun b ↦ finiteEvaluationMatrix (fun k i ↦ f i (b k))
  have hcont : Continuous E :=
    finiteEvaluationMatrix.continuous_of_finiteDimensional.comp
      (continuous_pi fun k ↦ continuous_pi fun i ↦ (hf i).comp (continuous_apply k))
  have hEa : E a = E₀.toContinuousLinearMap := by ext c k; exact (hE₀ c k).symm
  have hcomp : Continuous (fun b ↦ (1 : (κ → ℝ) →L[ℝ] (κ → ℝ)) -
      (E b).comp E₀.symm.toContinuousLinearMap) :=
    continuous_const.sub (hcont.clm_comp_const E₀.symm.toContinuousLinearMap)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hcomp.continuousAt (1/2) (by norm_num)
  refine ⟨δ,hδ,fun b hb ↦ ?_⟩
  have hsmall : ‖(1 : (κ → ℝ) →L[ℝ] (κ → ℝ)) -
      (E b).comp E₀.symm.toContinuousLinearMap‖ ≤ 1/2 := by
    have ht := hnear (show dist b a < δ by simpa [dist_eq_norm] using hb)
    simpa [hEa, ContinuousLinearEquiv.comp_coe, ContinuousLinearMap.one_def, dist_eq_norm] using ht.le
  obtain ⟨T, hright, hleft, hnorm⟩ := perturbed_interpolation_inverse E₀ (E b) hsmall
  refine ⟨T, ?_, ?_, hnorm⟩
  · intro d k
    exact congrArg (fun L : (κ → ℝ) →L[ℝ] (κ → ℝ) ↦ L d k) hright
  · intro c
    exact congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) ↦ L c) hleft

end HolomorphicAnosov.JourneLeafPolynomialApproximation
