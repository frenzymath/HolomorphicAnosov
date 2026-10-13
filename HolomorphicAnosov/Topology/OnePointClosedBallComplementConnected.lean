import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

open Set Metric
open scoped OnePoint
namespace HolomorphicAnosov

/-- The complement of a closed complex ball in the one-point compactification is connected. (Ahlfors–Sario, III §4, 12D) -/
theorem onePoint_closedBall_complement_connected {R : ℝ} (hR : 0 ≤ R) :
    IsConnected ((OnePoint.some '' closedBall (0 : ℂ) R)ᶜ) := by
  refine ⟨⟨∞, by simp⟩, isPreconnected_of_forall ∞ ?_⟩
  intro y hy
  cases y using OnePoint.rec with
  | infty =>
    exact ⟨{∞}, by simpa only [singleton_subset_iff] using hy, by simp, by simp, isPreconnected_singleton⟩
  | coe z =>
    have hz : R < ‖z‖ := by simpa [mem_closedBall, dist_zero_right] using hy
    have hzpos : 0 < ‖z‖ := hR.trans_lt hz
    let A : Set ℂ := (fun t : ℝ ↦ t • z) '' Ici 1
    have hA : IsPreconnected A :=
      isPreconnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn
    have hAext : A ⊆ (closedBall (0 : ℂ) R)ᶜ := by
      rintro w ⟨t, ht, rfl⟩
      change 1 ≤ t at ht
      have htpos : 0 ≤ t := le_trans (by norm_num) ht
      have hnorm : ‖t • z‖ = t * ‖z‖ := by simp [Real.norm_eq_abs, abs_of_nonneg htpos]
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hnorm]
      nlinarith
    have hinfty : (∞ : OnePoint ℂ) ∈ closure (OnePoint.some '' A) := by
      by_contra hnot
      have hc := ((OnePoint.isClosed_iff_of_notMem hnot).mp isClosed_closure).2
      obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
      let t := max 1 (M / ‖z‖ + 1)
      have ht : 1 ≤ t := le_max_left _ _
      have htpos : 0 ≤ t := le_trans (by norm_num) ht
      have hw : t • z ∈ A := ⟨t, ht, rfl⟩
      have hb := hM (t • z) (subset_closure ⟨t • z, hw, rfl⟩)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htpos] at hb
      have ht' : M / ‖z‖ + 1 ≤ t := le_max_right _ _
      have hdiv : M / ‖z‖ * ‖z‖ = M := div_mul_cancel₀ _ hzpos.ne'
      nlinarith
    refine ⟨insert ∞ (OnePoint.some '' A), ?_, by simp, ?_, ?_⟩
    · intro w hw
      rcases hw with rfl | ⟨a, ha, rfl⟩
      · simp
      · simpa using hAext ha
    · apply mem_insert_of_mem
      refine ⟨z, ?_, rfl⟩
      exact ⟨(1 : ℝ), by simp, by simp⟩
    · exact (hA.image _ OnePoint.continuous_coe.continuousOn).subset_closure
        (subset_insert _ _) (insert_subset hinfty subset_closure)

end HolomorphicAnosov
