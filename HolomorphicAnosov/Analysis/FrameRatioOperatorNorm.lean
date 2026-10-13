import Mathlib.Analysis.Normed.Operator.Basic

open Set Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- The operator norm is the supremum of norm ratios on any real linear frame unit sphere.
Normalize the frame preimage of each nonzero domain vector to obtain one inequality; the
operator bound gives the other. Real supremum conventions also cover a zero dimensional
model (whose unit sphere is empty). This is an explicit consequence of Mathlib operator
norm bounds, used for the continuous Finsler norm setting of HPS, Invariant Manifolds, p.8. -/
lemma frame_ratio_norm {V E F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : V ≃L[ℝ] E) (L : E →L[ℝ] F) :
    ‖L‖ = sSup ((fun u : Metric.sphere (0 : V) 1 ↦ ‖L (j u)‖ / ‖j u‖) '' univ) := by
  let S := (fun u : Metric.sphere (0 : V) 1 ↦ ‖L (j u)‖ / ‖j u‖) '' univ
  have hb : BddAbove S := ⟨‖L‖, by rintro _ ⟨u, _, rfl⟩; exact L.ratio_le_opNorm _⟩
  apply le_antisymm
  · apply L.opNorm_le_bound (Real.sSup_nonneg (by
      rintro _ ⟨u, _, rfl⟩; exact div_nonneg (norm_nonneg _) (norm_nonneg _)))
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let w := j.symm v
    have hw : w ≠ 0 := by simpa [w] using hv
    let u : Metric.sphere (0 : V) 1 := ⟨‖w‖⁻¹ • w, by
      simp [norm_smul, norm_ne_zero_iff.mpr hw]⟩
    have hu : ‖L (j u)‖ / ‖j u‖ ≤ sSup S := le_csSup hb ⟨u, mem_univ _, rfl⟩
    have heq : ‖L (j u)‖ / ‖j u‖ = ‖L v‖ / ‖v‖ := by
      simp only [u, map_smul, w, ContinuousLinearEquiv.apply_symm_apply, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_norm]
      exact mul_div_mul_left _ _ (inv_ne_zero (norm_ne_zero_iff.mpr hw))
    rw [heq] at hu
    exact (div_le_iff₀ (norm_pos_iff.mpr hv)).mp hu
  · apply Real.sSup_le _ (norm_nonneg _)
    rintro _ ⟨u, _, rfl⟩
    exact L.ratio_le_opNorm _

end
end HolomorphicAnosov
