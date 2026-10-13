import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp

namespace HolomorphicAnosov

/-- A positive definite continuous bilinear form on a finite-dimensional real normed space has a
positive quadratic lower bound in the given norm. (Petersen, Thm 5.3.8, pp.148–149) -/
theorem exists_pos_quadratic_lower_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ B v v := by
  have hcont : Continuous (fun v : V ↦ B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨c, hc, hbound⟩ := (isCompact_sphere (0 : V) 1).exists_forall_le'
    hcont.continuousOn (a := 0) (fun v hv ↦ hpos v (by
      intro heq
      simp [heq] at hv))
  refine ⟨c, hc, fun v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hs : (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : V) 1 := by
    simp [norm_smul, hn]
  have hb := mul_le_mul_of_nonneg_right (hbound _ hs) (sq_nonneg ‖v‖)
  convert hb using 1
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp

end HolomorphicAnosov

