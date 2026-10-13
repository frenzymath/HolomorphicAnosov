import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions

open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- The complementary-coordinate estimate puts the base vector in the range of `Id - Γ` on the original open ball; Picard iteration gives existence and contraction gives uniqueness there. (Wells, p. 290 and Remark, p. 291) -/
theorem hps_complementary_picard_range
    {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
    (Γ : X → X) (b : X) (s Q : ℝ) (hb : ‖b‖ < s)
    (hQ : 0 ≤ Q) (hQ1 : Q < 1)
    (hLip : ∀ x ∈ Metric.ball (0 : X) s, ∀ y ∈ Metric.ball (0 : X) s,
      ‖Γ x - Γ y‖ ≤ Q * ‖x - y‖)
    (hmax : ∀ w, ‖w‖ ≤ ‖b‖ → ‖b + Γ w‖ ≤ max ‖b‖ (Q * ‖w‖)) :
    ∃ w : X, ‖w‖ ≤ ‖b‖ ∧ w - Γ w = b ∧
      ∀ z ∈ Metric.ball (0 : X) s, z - Γ z = b → z = w := by
  let D := Metric.closedBall (0 : X) ‖b‖
  let : CompleteSpace D := Metric.isClosed_closedBall.isComplete.completeSpace_coe
  have hball (x : D) : x.val ∈ Metric.ball (0 : X) s := by
    exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using
      (show ‖x.val‖ ≤ ‖b‖ by simpa only [D, Metric.mem_closedBall, dist_zero_right] using x.property).trans_lt hb)
  have hself (x : D) : b + Γ x ∈ D := by
    have hx : ‖x.val‖ ≤ ‖b‖ := by simpa only [D, Metric.mem_closedBall, dist_zero_right] using x.property
    have hQx : Q * ‖x.val‖ ≤ ‖b‖ :=
      (mul_le_mul_of_nonneg_left hx hQ).trans (mul_le_of_le_one_left (norm_nonneg b) hQ1.le)
    simpa [D] using (hmax x hx).trans (max_le le_rfl hQx)
  let T : D → D := fun x ↦ ⟨b + Γ x, hself x⟩
  have hT : ContractingWith (⟨Q, hQ⟩ : NNReal) T := by
    refine ⟨hQ1, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (b + Γ x.val) (b + Γ y.val) ≤ Q * dist x.val y.val
    simpa only [dist_eq_norm, add_sub_add_left_eq_sub] using
      hLip x (hball x) y (hball y)
  obtain ⟨w, hw, _, _⟩ := hT.exists_fixedPoint
    (⟨0, by simp [D]⟩ : D) (edist_ne_top _ _)
  have hwfix : b + Γ w = w := congrArg Subtype.val hw.eq
  refine ⟨w, (by simpa only [D, Metric.mem_closedBall, dist_zero_right] using w.property), ?_, ?_⟩
  · exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hwfix.symm)
  · intro z hz heq
    have hzfix : b + Γ z = z := (sub_eq_iff_eq_add.mp heq).symm
    have hnorm : ‖z - w.val‖ ≤ Q * ‖z - w.val‖ := by
      calc
        ‖z - w.val‖ = ‖(b + Γ z) - (b + Γ w.val)‖ :=
          congrArg norm (congrArg₂ (fun x y : X ↦ x - y) hzfix.symm hwfix.symm)
        _ = ‖Γ z - Γ w.val‖ := by rw [add_sub_add_left_eq_sub]
        _ ≤ _ := hLip z hz w (hball w)
    have hz0 : ‖z - w.val‖ = 0 := by nlinarith [norm_nonneg (z - w.val)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz0)

end HolomorphicAnosov
