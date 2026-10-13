import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import HolomorphicAnosov.Analysis.MashreghiBoundary.AnglePoint

/-!
Public DAG node: `analysis.mashreghi_inner_arc_estimate_g3` (statement).
Source origin: inner arc term in Mashreghi Theorem 4.3 equation (4.7), printed p.443; only interior derivatives are used.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.MashreghiRadial
/-- The common-radius inner arc estimate.
Source: Mashreghi Theorem 4.3, inner-arc term in (4.7), printed p.443.
Proof: the path t↦ρexp(it) has derivative of norm ρ and lies strictly inside
the unit disk. The scalar-tower chain rule bounds the derivative of its
composition with F by Cρ(1−ρ)^(α−1). Apply the norm-versus-integral inequality
on [θ,φ] and integrate this constant. Radius zero is allowed. -/
lemma inner_arc_estimate
    (α C : ℝ) (_hC : 0 ≤ C)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ_one : ρ < 1) (θ φ : ℝ) (hθφ : θ ≤ φ) :
    ‖F ((ρ : ℂ) * anglePoint φ) - F ((ρ : ℂ) * anglePoint θ)‖ ≤
      (C * ρ * (1 - ρ) ^ (α - 1)) * (φ - θ) := by
  have anglePoint_norm (θ : ℝ) : ‖anglePoint θ‖ = 1 := by
    simp [anglePoint, Complex.norm_exp]
  have anglePoint_deriv (θ : ℝ) :
      HasDerivAt anglePoint (Complex.I * anglePoint θ) θ := by
    have h := (((hasDerivAt_id (θ : ℂ)).const_mul Complex.I).cexp).comp_ofReal
    unfold anglePoint
    simpa only [mul_one, mul_comm, id_eq] using! h

  have hnorm (t : ℝ) : ‖(ρ : ℂ) * anglePoint t‖ = ρ := by
    simp [anglePoint_norm, abs_of_nonneg hρ]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ F ((ρ : ℂ) * anglePoint s))
      (((ρ : ℂ) * (Complex.I * anglePoint t)) * deriv F ((ρ : ℂ) * anglePoint t)) t := by
    have hinside : ‖(ρ : ℂ) * anglePoint t‖ < 1 := by rw [hnorm]; exact hρ_one
    have hf := (hF.differentiableAt
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hinside)).hasDerivAt
    simpa only [Function.comp_def, smul_eq_mul] using
      hf.scomp t ((anglePoint_deriv t).const_mul (ρ : ℂ))
  have hb (t : ℝ) :
      ‖deriv (fun s : ℝ ↦ F ((ρ : ℂ) * anglePoint s)) t‖ ≤
        C * ρ * (1 - ρ) ^ (α - 1) := by
    rw [(hd t).deriv]
    simp only [norm_mul, Complex.norm_I, anglePoint_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
    have hi : ‖(ρ : ℂ) * anglePoint t‖ < 1 := by rw [hnorm]; exact hρ_one
    have h := mul_le_mul_of_nonneg_left (hderiv _ hi) hρ
    rw [hnorm] at h
    nlinarith
  have hi : IntervalIntegrable (fun _ : ℝ ↦ C * ρ * (1 - ρ) ^ (α - 1))
      volume θ φ := intervalIntegrable_const
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hθφ
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall (fun t _ ↦ hb t)) hi
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
end HolomorphicAnosov.MashreghiRadial
