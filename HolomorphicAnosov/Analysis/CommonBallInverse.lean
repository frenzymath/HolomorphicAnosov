import HolomorphicAnosov.Analysis.ContinuousContractingFixedPoint
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# A continuous inverse on a common ball

Source: Fisher–Hasselblatt, *Hyperbolic flows* (author text, 2018),
Proposition 12.1.3 and residual estimate (12.1.2), pp.578–579, applied to
`v ↦ v + z - H p v` on one complete closed ball. The residual argument uses
only continuity at a fixed state, so the parameter space may have any topology.
-/

namespace HolomorphicAnosov.Analysis

open scoped _root_.Topology NNReal

/-- A family uniformly within one half of the identity on a closed ball has a
continuous inverse on a common smaller target ball. This is the closed-ball
contraction construction in Fisher–Hasselblatt 12.1.3 pp.578–579 applied to
`v ↦ v + z - H p v`. The source ball and uniqueness carrier are fixed for all
parameters.

Proof: on the complete closed `r`-ball, the half-identity error estimate makes
`Q v = v + z - H p v` a contraction of constant `1/2`. The estimate at zero
gives `‖Q v‖ ≤ ‖v‖/2 + ‖z‖ + ‖H p 0‖ < 3*r/4 < r`, so this is a self-map
of that same ball for every parameter. Its unique fixed point solves
`H p v = z`. Fixed-state continuity of `H` implies fixed-state continuity of
`Q`, and the parameter-dependent contraction theorem gives continuity of its
fixed point. The residual estimate at zero gives
`‖v‖ ≤ 2*‖z - H p 0‖ < r/2`. Every other preimage in the closed ball is a
fixed point of `Q`, hence equals this one. This also covers the zero group
and an empty parameter space. -/
theorem common_ball_inverse_of_half_identity
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [CompleteSpace E]
    (H : P → E → E) (r : ℝ) (hr : 0 < r)
    (hc : ∀ v ∈ Metric.closedBall (0 : E) r, Continuous (fun p ↦ H p v))
    (hcenter : ∀ p, ‖H p 0‖ < r / 8)
    (happrox : ∀ p, ∀ v ∈ Metric.closedBall (0 : E) r,
      ∀ w ∈ Metric.closedBall (0 : E) r,
      ‖H p v - H p w - (v - w)‖ ≤ (1 / 2 : ℝ) * ‖v - w‖) :
    ∃ v : P × Metric.ball (0 : E) (r / 8) → E, Continuous v ∧
      ∀ z, ‖v z‖ < r / 2 ∧ H z.1 (v z) = z.2.val ∧
        ∀ w ∈ Metric.closedBall (0 : E) r, H z.1 w = z.2.val → w = v z := by
  let C := Metric.closedBall (0 : E) r
  have hzero : (0 : E) ∈ C := Metric.mem_closedBall_self hr.le
  let : Nonempty C := ⟨⟨0, hzero⟩⟩
  let : CompleteSpace C := Metric.isClosed_closedBall.completeSpace_coe
  let Z := P × Metric.ball (0 : E) (r / 8)
  have hQbound (z : Z) (v : C) : ‖v.val + z.2.val - H z.1 v.val‖ < r := by
    have he := happrox z.1 v v.property 0 hzero
    have hz : ‖z.2.val‖ < r / 8 := by simpa only [Metric.mem_ball, dist_zero_right] using z.2.property
    have hv : ‖v.val‖ ≤ r := by simpa only [C, Metric.mem_closedBall, dist_zero_right] using v.property
    have hd : ‖v.val - H z.1 v.val + H z.1 0‖ ≤ (1 / 2 : ℝ) * ‖v.val‖ := by
      convert he using 1 <;> simp only [sub_zero]
      rw [show v.val - H z.1 v.val + H z.1 0 = -(H z.1 v.val - H z.1 0 - v.val) by abel, norm_neg]
    calc
      ‖v.val + z.2.val - H z.1 v.val‖ =
          ‖(v.val - H z.1 v.val + H z.1 0) + (z.2.val - H z.1 0)‖ := by congr 1; abel
      _ ≤ ‖v.val - H z.1 v.val + H z.1 0‖ + ‖z.2.val - H z.1 0‖ := norm_add_le _ _
      _ ≤ (1 / 2 : ℝ) * ‖v.val‖ + (‖z.2.val‖ + ‖H z.1 0‖) :=
        add_le_add hd (norm_sub_le _ _)
      _ < r := by linarith [hcenter z.1]
  let Q : Z → C → C := fun z v ↦ ⟨v.val + z.2.val - H z.1 v.val,
    by simpa only [C, Metric.mem_closedBall, dist_zero_right] using (hQbound z v).le⟩
  have hQ (z : Z) : ContractingWith (1 / 2) (Q z) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro v w
      change dist (v.val + z.2.val - H z.1 v.val) (w.val + z.2.val - H z.1 w.val) ≤
        ((1 / 2 : ℝ≥0) : ℝ) * dist v.val w.val
      rw [dist_eq_norm, dist_eq_norm]
      simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
      rw [show v.val + z.2.val - H z.1 v.val - (w.val + z.2.val - H z.1 w.val) =
        -(H z.1 v.val - H z.1 w.val - (v.val - w.val)) by abel, norm_neg]
      exact happrox z.1 v v.property w w.property
  have hcQ (v : C) : Continuous (fun z : Z ↦ Q z v) := by
    apply Continuous.subtype_mk
    exact (continuous_const.add (continuous_subtype_val.comp continuous_snd)).sub
      ((hc v v.property).comp continuous_fst)
  let solution (z : Z) : C := (hQ z).fixedPoint (Q z)
  have hfix (z : Z) : Q z (solution z) = solution z := (hQ z).fixedPoint_isFixedPt
  refine ⟨fun z ↦ (solution z).val,
    continuous_subtype_val.comp (continuous_contracting_fixedPoint Q hQ hcQ), ?_⟩
  intro z
  have heq : H z.1 (solution z).val = z.2.val := by
    have he := congrArg Subtype.val (hfix z)
    change (solution z).val + z.2.val - H z.1 (solution z).val = (solution z).val at he
    exact (add_left_cancel (sub_eq_iff_eq_add.mp he)).symm
  refine ⟨?_, heq, ?_⟩
  · have hb := (hQ z).dist_fixedPoint_le (⟨0, hzero⟩ : C)
    change dist (0 : E) (solution z).val ≤ dist (0 : E) (0 + z.2.val - H z.1 0) /
      (1 - ((1 / 2 : ℝ≥0) : ℝ)) at hb
    simp only [dist_zero_left, zero_add, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hb
    have hz : ‖z.2.val‖ < r / 8 := by simpa only [Metric.mem_ball, dist_zero_right] using z.2.property
    have ht := norm_sub_le z.2.val (H z.1 0)
    norm_num at hb
    linarith [hcenter z.1]
  · intro w hw hew
    have hfw : Function.IsFixedPt (Q z) (⟨w, hw⟩ : C) := by
      apply Subtype.ext
      change w + z.2.val - H z.1 w = w
      rw [hew, add_sub_cancel_right]
    exact congrArg Subtype.val ((hQ z).fixedPoint_unique hfw)

end HolomorphicAnosov.Analysis
