import Mathlib.Analysis.Distribution.TestFunction

open Set TopologicalSpace
open scoped ContDiff ENNReal

namespace HolomorphicAnosov.Analysis.Distribution

/-- The translated and dilated mollifier is a genuine complex test function
whenever its closed support ball lies inside the domain.
Source: Demailly, Complex Analytic and Differential Geometry, I §2.D.3,
(2.23), p.19. The dilation and translation preserve smoothness. Outside the
closed ε-ball the rescaled argument has norm greater than one, so the kernel
vanishes. The support is therefore closed in that compact ball and contained
in the prescribed open set. -/
theorem exists_scaled_mollifier_test {m : ℕ}
    (U : Opens (EuclideanSpace ℝ (Fin m)))
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρ_support : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆
      Metric.closedBall 0 1)
    (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin m))
    (hx : ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)) :
    ∃ κ : TestFunction U ℂ ⊤, ∀ y,
      κ y = (((ε⁻¹) ^ m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (x - y)) : ℝ) : ℂ) := by
  let f : EuclideanSpace ℝ (Fin m) → ℂ :=
    fun y ↦ (((ε⁻¹) ^ m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (x - y)) : ℝ) : ℂ)
  have hzero : ∀ y ∉ Metric.closedBall x ε, f y = 0 := by
    intro y hy
    have hnorm : ε < ‖x - y‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] using hy
    have hnot : ε⁻¹ • (x - y) ∉ tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) := by
      intro h
      have hle := hρ_support h
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hε)] at hle
      have : ‖x - y‖ ≤ ε := by
        have := (mul_le_mul_of_nonneg_left hle hε.le)
        simpa only [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_one] using this
      exact (not_le.mpr hnorm) this
    simp [f, image_eq_zero_of_notMem_tsupport hnot]
  have hsupp : tsupport f ⊆ Metric.closedBall x ε := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    by_contra hn
    exact hy (hzero y hn)
  have hinside : Metric.closedBall x ε ⊆ U := by
    intro y hy
    by_contra hn
    have hdist : edist x y ≤ ENNReal.ofReal ε := by
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Metric.mem_closedBall, dist_comm] using hy
    exact (not_le.mpr hx) ((Metric.infEDist_le_edist_of_mem hn).trans hdist)
  have hcont : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f := by
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (ρ.contDiff.comp ((contDiff_const.sub contDiff_id).const_smul ε⁻¹)))
  refine ⟨⟨f, hcont, ?_, hsupp.trans hinside⟩, fun _ ↦ rfl⟩
  exact (isCompact_closedBall x ε).of_isClosed_subset (isClosed_tsupport f) hsupp

end HolomorphicAnosov.Analysis.Distribution
