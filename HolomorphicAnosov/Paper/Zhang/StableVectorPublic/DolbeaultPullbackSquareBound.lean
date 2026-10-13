import HolomorphicAnosov.Analysis.InnerProductSpace.JacobianSingularValues

noncomputable section
namespace HolomorphicAnosov

/-- When the unstable map has conorm at least one, the Dolbeault pullback has squared norm bounded
by `(A * K * B) ^ 2 * ((lam ^ n)⁻¹) ^ 2 * J` under the given operator and Jacobian bounds.
(Zhang, (26)–(30)) -/
theorem dolbeault_pullback_square_bound
    {E E' V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (r : ℕ) (hr : 0 < r) (hV : Module.finrank ℂ V = r) (hW : Module.finrank ℂ W = r)
    (U : V ≃L[ℂ] W) (D : E' →L⋆[ℂ] W) (F : E →L[ℂ] E')
    (μ : ℂ) (n : ℕ) (A K B lam J : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hlam : 0 < lam)
    (hconorm : 1 ≤ sInf ((fun v : V ↦ ‖U v‖) '' {v : V | ‖v‖ = 1}))
    (hinv : ‖U.symm.toContinuousLinearMap‖ ≤ A * (lam ^ n)⁻¹)
    (hD : ‖D‖ ≤ K) (hF : ‖F‖ ≤ B * ‖U.toContinuousLinearMap‖)
    (hJ : J = ‖μ‖ ^ (2 * n) * U.toLinearMap.normDet ^ 2) :
    ‖μ ^ n • ((U.symm.toContinuousLinearMap.comp D).comp F)‖ ^ 2 ≤
      (A * K * B) ^ 2 * ((lam ^ n)⁻¹) ^ 2 * J := by
  have hdet : ‖U.toContinuousLinearMap‖ ≤ U.toLinearMap.normDet :=
    (jacobian_singular_values r hr hV hW U).2.2.2.2.1 hconorm
  have hF' : ‖F‖ ≤ B * U.toLinearMap.normDet :=
    hF.trans (mul_le_mul_of_nonneg_left hdet hB)
  have hcomp : ‖(U.symm.toContinuousLinearMap.comp D).comp F‖ ≤
      ‖U.symm.toContinuousLinearMap‖ * ‖D‖ * ‖F‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg F))
  have hbound : ‖μ ^ n • ((U.symm.toContinuousLinearMap.comp D).comp F)‖ ≤
      ‖μ‖ ^ n * ((A * (lam ^ n)⁻¹) * K * (B * U.toLinearMap.normDet)) := by
    rw [norm_smul, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg μ) n)
    apply hcomp.trans
    exact mul_le_mul
      (mul_le_mul hinv hD (norm_nonneg D) (mul_nonneg hA (inv_nonneg.mpr (pow_nonneg hlam.le n))))
      hF' (norm_nonneg F) (mul_nonneg (mul_nonneg hA (inv_nonneg.mpr
        (pow_nonneg hlam.le n))) hK)
  calc
    _ ≤ (‖μ‖ ^ n * ((A * (lam ^ n)⁻¹) * K * (B * U.toLinearMap.normDet))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = (A * K * B) ^ 2 * ((lam ^ n)⁻¹) ^ 2 * J := by
      rw [hJ, pow_mul]
      ring



end HolomorphicAnosov
