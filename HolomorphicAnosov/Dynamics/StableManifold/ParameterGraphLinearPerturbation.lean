import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov

/-- HPS pp.55–58: the horizontal inverse estimate for a linear perturbation.
If L differs from the isomorphism T by operator norm at most δ and
‖T⁻¹‖≤a with aδ<1, L is a continuous linear equivalence with inverse norm
at most a/(1−aδ). The global small-Lipschitz-perturbation theorem gives the
actual homeomorphism. Its linearity is inherited from L. For x=J⁻¹u,
the identity Tx=u−(L−T)x gives ‖x‖≤a(‖u‖+δ‖x‖); absorb aδ‖x‖ and
take the operator norm. The zero-space guard avoids division by ‖T⁻¹‖=0. -/
theorem parameter_graph_linear_perturbation
    {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (T : X ≃L[ℝ] U) (L : X →L[ℝ] U) (a δ : NNReal)
    (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hδ : ‖L - T.toContinuousLinearMap‖ ≤ δ)
    (hsmall : (a : ℝ) * δ < 1) :
    ∃ J : X ≃L[ℝ] U, J.toContinuousLinearMap = L ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ (a : ℝ) / (1 - (a : ℝ) * δ) := by
  have happrox : ApproximatesLinearOn L T.toContinuousLinearMap Set.univ δ := by
    intro x hx y hy
    change ‖L x - L y - T (x-y)‖ ≤ (δ : ℝ) * ‖x-y‖
    rw [← L.map_sub]
    exact ((L-T.toContinuousLinearMap).le_opNorm (x-y)).trans
      (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))
  have hguard : Subsingleton X ∨ δ < ‖T.symm.toContinuousLinearMap‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial X with hX | hX
    · exact Or.inl hX
    · right
      have hpos := T.norm_symm_pos
      have hlt : (δ : ℝ) < ‖T.symm.toContinuousLinearMap‖⁻¹ := by
        rw [inv_eq_one_div]
        apply (lt_div_iff₀ hpos).2
        exact (mul_le_mul_of_nonneg_left ha δ.2).trans_lt
          (by rw [mul_comm]; exact hsmall)
      exact_mod_cast hlt
  let H : X ≃ₜ U := happrox.toHomeomorph L hguard
  let J : X ≃L[ℝ] U :=
    { H.toEquiv with
      map_add' := L.map_add
      map_smul' := L.map_smul
      continuous_toFun := H.continuous
      continuous_invFun := H.symm.continuous }
  have hJ : J.toContinuousLinearMap = L := rfl
  refine ⟨J,hJ,?_⟩
  have hden : 0 < 1 - (a : ℝ) * δ := sub_pos.mpr hsmall
  apply J.symm.toContinuousLinearMap.opNorm_le_bound (div_nonneg a.2 hden.le)
  intro u
  have he : T (J.symm u) = u - (L-T.toContinuousLinearMap) (J.symm u) := by
    have hlu : L (J.symm u) = u := J.apply_symm_apply u
    simp only [sub_apply, hlu, ContinuousLinearEquiv.coe_coe]
    abel
  have hbound : ‖J.symm u‖ ≤ (a : ℝ) * (‖u‖ + (δ : ℝ) * ‖J.symm u‖) := calc
    _ = ‖T.symm (T (J.symm u))‖ := by rw [T.symm_apply_apply]
    _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (J.symm u)‖ :=
      T.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ (a : ℝ) * ‖T (J.symm u)‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ a.2
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl
        (((L-T.toContinuousLinearMap).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))))
  change ‖J.symm u‖ ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  calc
    _ = ‖J.symm u‖ - (a : ℝ) * ((δ : ℝ) * ‖J.symm u‖) := by ring
    _ ≤ (a : ℝ) * ‖u‖ := by
      apply sub_le_iff_le_add.mpr
      convert hbound using 1
      ring

end HolomorphicAnosov
