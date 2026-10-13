import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped ContDiff Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
namespace StableFoliationsSupport

/-- The unit sublevel set of a positive definite continuous bilinear form on a finite-dimensional
real normed space is bounded. (Lee, Lemma 11.19, pp.278–279) -/
theorem positive_form_unit_sublevel_bounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hp : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E | B v v < 1} := by
  apply (NormedSpace.isVonNBounded_iff ℝ).2
  apply isBounded_iff_forall_norm_le.2
  have hcont : Continuous (fun v : E ↦ B v v) := B.continuous.clm_apply continuous_id
  by_cases hne : (Metric.sphere (0 : E) 1).Nonempty
  · obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hcont.continuousOn
    have hn₀ : ‖v₀‖ = 1 := by simpa using hv₀
    have ha : 0 < B v₀ v₀ := hp v₀ (by intro hv; simp [hv] at hn₀)
    refine ⟨max 1 (1 / (B v₀ v₀)), ?_⟩
    intro v hv
    by_cases hz : v = 0
    · simp [hz]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
    have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
      exact inv_mul_cancel₀ hn.ne'
    have hm := hmin (by simpa using hu : (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : E) 1)
    have hm' : B v₀ v₀ * ‖v‖ ^ 2 ≤ B v v := by
      change B v₀ v₀ ≤ B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at hm
      simp only [map_smul, smul_apply, smul_eq_mul] at hm
      have hm2 := (le_mul_inv_iff₀ (sq_pos_of_pos hn)).mp (by
        simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hm : B v₀ v₀ ≤ B v v * (‖v‖ ^ 2)⁻¹)
      exact hm2
    have hv' : B v v < 1 := hv
    by_contra hbound
    have h1 : 1 < ‖v‖ := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hbound)
    have h2 : 1 / (B v₀ v₀) < ‖v‖ := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hbound)
    have h3 : 1 < ‖v‖ * (B v₀ v₀) := (div_lt_iff₀ ha).mp h2
    nlinarith
  · refine ⟨0, ?_⟩
    intro v _
    by_cases hz : v = 0
    · simp [hz]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
    have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
      exact inv_mul_cancel₀ hn.ne'
    exact (hne ⟨_, by simpa using hu⟩).elim

end StableFoliationsSupport
end HolomorphicAnosov
