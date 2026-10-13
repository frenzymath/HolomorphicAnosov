import HolomorphicAnosov.Analysis.MashreghiBoundary.FiniteRadialEstimate
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialRadius
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialValuesCauchy
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundary

/-!
Public DAG node: `analysis.mashreghi_radial_boundary_tail_g3` (statement).
Source origin: Mashreghi Theorem 4.3 equation (4.6), printed p.442, with the constant-exponent integral evaluated exactly.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.MashreghiRadial
/-- Exact radial tail estimate for the constructed limit.
Source: Mashreghi Theorem 4.3, equation (4.6), printed p.442.
Proof: the radial sequence converges by completeness, and its radii eventually
exceed any fixed 0≤ρ<1. The finite radial estimate bounds every such displacement
by (C/α)(1−ρ)^α. Passing to the limit under subtraction and norm gives the
claim. The fixed constant is obtained by evaluating the constant-exponent integral. -/
theorem radialBoundary_tail
    (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
    (η : ℂ) (hη : ‖η‖ = 1) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ_one : ρ < 1) :
    ‖radialBoundary F η - F ((ρ : ℂ) * η)‖ ≤ (C / α) * (1 - ρ) ^ α := by
  have radial_values_tendsto
      (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
      (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
      (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
      (η : ℂ) (hη : ‖η‖ = 1) :
      Tendsto (fun n : ℕ ↦ F ((radialRadius n : ℂ) * η)) atTop
        (𝓝 (radialBoundary F η)) :=
    (radial_values_cauchy α C hα hα_one hC F hF hderiv η hη).tendsto_limUnder
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

  have ht := ((radial_values_tendsto α C hα hα_one hC F hF hderiv η hη).sub
    (tendsto_const_nhds (x := F ((ρ : ℂ) * η)))).norm
  apply le_of_tendsto ht
  filter_upwards [radialRadius_tendsto.eventually (lt_mem_nhds hρ_one)] with n hn
  exact finite_radial_tail α C hα hC F hF hderiv η hη
    ρ (radialRadius n) hρ hn.le (radialRadius_lt_one n)
end HolomorphicAnosov.MashreghiRadial
