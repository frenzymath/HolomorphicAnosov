import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import HolomorphicAnosov.Analysis.MashreghiBoundary.FiniteRadialEstimate
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialRadius

/-!
Public DAG node: `analysis.mashreghi_radial_values_cauchy_g3` (statement).
Source origin: radial-limit existence in Mashreghi Theorem 4.3 forward proof, printed p.442 before (4.6). Cauchy/completeness details make its integrable-tail argument explicit.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.MashreghiRadial
/-- Cauchy radial values for each unit direction.
Source: Mashreghi Theorem 4.3, printed p.442, the finite radial limit obtained
from the integrable radial majorant. Proof: the chosen radii increase to one.
For n≤m the finite radial estimate bounds the displacement by
(C/α)(1-r_n)^α. Continuity of the positive power at zero makes this bound tend
to zero. The metric Cauchy criterion applies, uniformly in the unit direction. -/
theorem radial_values_cauchy
    (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
    (η : ℂ) (hη : ‖η‖ = 1) :
    CauchySeq (fun n : ℕ ↦ F ((radialRadius n : ℂ) * η)) := by
  have radialRadius_nonneg (n : ℕ) : 0 ≤ radialRadius n := by
    unfold radialRadius
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hi : 1 / ((n : ℝ) + 2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have radialRadius_mono : Monotone radialRadius := by
    intro n m hnm
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hm : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hnm 2
    have hi := one_div_le_one_div_of_le hn hm
    unfold radialRadius
    linarith
  have finite_radial_tail
      (α C : ℝ) (hα : 0 < α) (hC : 0 ≤ C)
      (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
      (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
      (η : ℂ) (hη : ‖η‖ = 1) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1) :
      ‖F ((v : ℂ) * η) - F ((u : ℂ) * η)‖ ≤ (C / α) * (1 - u) ^ α := by
    apply (finite_radial_estimate α C hα hC F hF hderiv η hη u v hu huv hv).trans
    exact mul_le_mul_of_nonneg_left
      (sub_le_self _ (Real.rpow_nonneg (by linarith) _)) (div_nonneg hC hα.le)
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

  apply cauchySeq_of_le_tendsto_0' (fun n : ℕ ↦ (C / α) * (1 - radialRadius n) ^ α)
  · intro n m hnm
    rw [dist_comm, dist_eq_norm]
    exact finite_radial_tail α C hα hC F hF hderiv η hη
      (radialRadius n) (radialRadius m) (radialRadius_nonneg n)
      (radialRadius_mono hnm) (radialRadius_lt_one m)
  · have hr : Tendsto (fun n : ℕ ↦ 1 - radialRadius n) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub radialRadius_tendsto
    have hp := ((Real.continuous_rpow_const hα.le).tendsto 0).comp hr
    simpa only [Real.zero_rpow hα.ne', mul_zero, Function.comp_def] using
      (tendsto_const_nhds (x := C / α)).mul hp
end HolomorphicAnosov.MashreghiRadial
