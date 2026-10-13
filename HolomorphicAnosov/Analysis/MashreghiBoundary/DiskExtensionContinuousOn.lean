import Mathlib.Topology.UniformSpace.UniformApproximation
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialRadius
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundary
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundaryTail
import HolomorphicAnosov.Analysis.MashreghiBoundary.DiskExtension

/-!
Public DAG node: `analysis.mashreghi_disk_extension_continuous_on_g3` (statement).
Agent origin: completes the omitted arbitrary-approach continuity argument in the final sentence after Mashreghi (4.7), printed p.443. Parent: analysis.mashreghi_disk_derivative_holder_boundary_g3. Uniform-circle convergence and normalization are both inside this proof; it depends only on source-backed radial estimates/definitions and Mathlib, with no agent-origin prerequisite.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.MashreghiRadial
/-- Continuity of the explicit extension on the whole closed disk.
Agent-written completion of the final continuity sentence after Mashreghi
Theorem 4.3 equation (4.7), printed p.443.
Parent: analysis.mashreghi_disk_derivative_holder_boundary_g3.
Proof: the radial tail bound makes η↦F(r_nη) converge uniformly to the boundary
values on the unit circle. Each approximant is continuous there, hence their
uniform limit is continuous. At a unit point z0, nonzero nearby z have unit
direction z/‖z‖ tending to z0. The difference between the extension at z and
the boundary value at its direction is at most (C/α)(1−‖z‖)^α on the closed
disk, including radius one, where it vanishes. This tends to zero, while circle
continuity controls the directional boundary term. At interior points the
extension locally equals F. Both continuity steps are inside this theorem;
there is no dependency on another agent-origin theorem. -/
theorem diskExtension_continuousOn
    (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1)) :
    ContinuousOn (diskExtension F) {z : ℂ | ‖z‖ ≤ 1} := by
  have normalized_norm {z : ℂ} (hz : z ≠ 0) : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    exact div_self (norm_ne_zero_iff.mpr hz)
  have diskExtension_radial_bound
      (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
      (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
      (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
      (z : ℂ) (hz : z ≠ 0) (hclosed : ‖z‖ ≤ 1) :
      ‖diskExtension F z - radialBoundary F (z / (‖z‖ : ℂ))‖ ≤
        (C / α) * (1 - ‖z‖)^α := by
    rcases lt_or_eq_of_le hclosed with hi | he
    · have ht := radialBoundary_tail α C hα hα_one hC F hF hderiv
        (z / (‖z‖ : ℂ)) (normalized_norm hz) ‖z‖ (norm_nonneg z) hi
      have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
      have hid : (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z := by field_simp
      rw [hid] at ht
      simpa only [diskExtension, ite_eq_left hi, norm_sub_rev] using ht
    · simp [diskExtension, he, Real.zero_rpow hα.ne']
  have diskExtension_eq_boundary (F : ℂ → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
      diskExtension F z = radialBoundary F z := by simp [diskExtension, hz]
  have radialRadius_nonneg (n : ℕ) : 0 ≤ radialRadius n := by
    unfold radialRadius
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hi : 1 / ((n : ℝ) + 2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have radialRadius_lt_one (n : ℕ) : radialRadius n < 1 := by
    unfold radialRadius
    have hi : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have radialRadius_tendsto : Tendsto radialRadius atTop (𝓝 1) := by
    have hi : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        ((tendsto_add_atTop_iff_nat 2).2
          (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
    unfold radialRadius
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hi
  have radialBoundary_continuousOn_circle
      (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
      (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
      (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1)) :
      ContinuousOn (radialBoundary F) {η : ℂ | ‖η‖ = 1} := by
    have hu : TendstoUniformlyOn (fun n η ↦ F ((radialRadius n : ℂ) * η))
        (radialBoundary F) atTop {η : ℂ | ‖η‖ = 1} := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      have hr : Tendsto (fun n : ℕ ↦ 1 - radialRadius n) atTop (𝓝 (0 : ℝ)) := by
        simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub radialRadius_tendsto
      have hp := ((Real.continuous_rpow_const hα.le).tendsto 0).comp hr
      have hb : Tendsto (fun n : ℕ ↦ (C / α) * (1 - radialRadius n)^α) atTop (𝓝 0) := by
        simpa only [Real.zero_rpow hα.ne', mul_zero, Function.comp_def] using
          (tendsto_const_nhds (x := C / α)).mul hp
      filter_upwards [hb.eventually (gt_mem_nhds hε)] with n hn η hη
      rw [dist_eq_norm]
      exact (radialBoundary_tail α C hα hα_one hC F hF hderiv η hη
        (radialRadius n) (radialRadius_nonneg n) (radialRadius_lt_one n)).trans_lt hn
    apply hu.continuousOn
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    apply hF.continuousOn.comp (continuous_const.mul continuous_id).continuousOn
    intro η hη
    change ‖η‖ = 1 at hη
    change ‖(radialRadius n : ℂ) * η‖ < 1
    simpa only [norm_mul, hη, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (radialRadius_nonneg n)] using radialRadius_lt_one n

  intro z hz
  change ‖z‖ ≤ 1 at hz
  rcases lt_or_eq_of_le hz with hi | he
  · have hf := (hF.differentiableAt
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hi)).continuousAt
    apply (hf.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hi] with w hw
    exact ite_eq_left hw
  · have hz0 : z ≠ 0 := by intro h; simp [h] at he
    have hn0 : (‖z‖ : ℂ) ≠ 0 := by simp [he]
    have hnorm : ContinuousAt (fun w : ℂ ↦ w / (‖w‖ : ℂ)) z :=
      continuousAt_id.div (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt) hn0
    have hnormz : z / (‖z‖ : ℂ) = z := by simp [he]
    have hbn := (radialBoundary_continuousOn_circle α C hα hα_one hC F hF hderiv) z he
    have hbnlim : Tendsto (fun w : ℂ ↦ radialBoundary F (w / (‖w‖ : ℂ)))
        (𝓝[{w : ℂ | ‖w‖ ≤ 1}] z) (𝓝 (radialBoundary F z)) := by
      apply hbn.tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [hnormz] using hnorm.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [(nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz0) :
          ∀ᶠ w in 𝓝[{w : ℂ | ‖w‖ ≤ 1}] z, w ≠ 0)] with w hw
        exact normalized_norm hw
    have htail : Tendsto (fun w : ℂ ↦ diskExtension F w -
        radialBoundary F (w / (‖w‖ : ℂ))) (𝓝[{w : ℂ | ‖w‖ ≤ 1}] z) (𝓝 0) := by
      apply squeeze_zero_norm'
      · filter_upwards [self_mem_nhdsWithin,
          (nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz0) :
            ∀ᶠ w in 𝓝[{w : ℂ | ‖w‖ ≤ 1}] z, w ≠ 0)] with w hw hw0
        exact diskExtension_radial_bound α C hα hα_one hC F hF hderiv w hw0 hw
      · have hr := ((continuous_const.sub continuous_norm).continuousAt.tendsto :
          Tendsto (fun w : ℂ ↦ 1 - ‖w‖) (𝓝 z) (𝓝 (1 - ‖z‖)))
        have hp := ((Real.continuous_rpow_const hα.le).tendsto (1 - ‖z‖)).comp hr
        simpa only [he, sub_self, Real.zero_rpow hα.ne', mul_zero, Function.comp_def, Pi.sub_apply] using
          ((tendsto_const_nhds (x := C / α)).mul hp).mono_left nhdsWithin_le_nhds
    have hsum := htail.add hbnlim
    change Tendsto (diskExtension F) _ (𝓝 (diskExtension F z))
    rw [diskExtension_eq_boundary F he]
    simpa only [sub_add_cancel, zero_add] using hsum
end HolomorphicAnosov.MashreghiRadial
