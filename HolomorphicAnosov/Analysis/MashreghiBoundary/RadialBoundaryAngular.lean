import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundary
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundaryTail
import HolomorphicAnosov.Analysis.MashreghiBoundary.AnglePoint
import HolomorphicAnosov.Analysis.MashreghiBoundary.InnerArcEstimate

/-!
Public DAG node: `analysis.mashreghi_radial_boundary_angular_g3` (statement).
Source origin: Mashreghi Theorem 4.3 equation (4.7), printed p.443, with explicit constant C*(2/alpha+1) and equal/reversed angles.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.MashreghiRadial
/-- Local angular Hölder estimate for the constructed boundary values.
Source: Mashreghi Theorem 4.3, equation (4.7), printed p.443.
Proof: for h=φ−θ∈(0,1), choose ρ=1−h. The triangle inequality decomposes the
boundary increment into two radial tails and the common-radius inner arc.
The tails contribute 2(C/α)h^α; the arc contributes at most Ch^α since ρ≤1.
Exchange angles when h<0, and use 0^α=0 for equal angles. This derives the
explicit constant C(2/α+1) without changing the global constant hypothesis. -/
theorem radialBoundary_angular
    (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
    (θ φ : ℝ) (hsmall : |φ - θ| < 1) :
    ‖radialBoundary F (Complex.exp (Complex.I * (φ : ℂ))) -
      radialBoundary F (Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
      C * (2 / α + 1) * |φ - θ| ^ α := by
  have anglePoint_norm (θ : ℝ) : ‖anglePoint θ‖ = 1 := by
    simp [anglePoint, Complex.norm_exp]
  have radialBoundary_angular_pos
      (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
      (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
      (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
      (θ φ : ℝ) (hpos : θ < φ) (hsmall : φ - θ < 1) :
      ‖radialBoundary F (anglePoint φ) - radialBoundary F (anglePoint θ)‖ ≤
        C * (2 / α + 1) * (φ - θ) ^ α := by
    let h := φ - θ
    let ρ := 1 - h
    have hh : 0 < h := sub_pos.mpr hpos
    have hρ : 0 ≤ ρ := by dsimp [ρ, h]; linarith
    have hρ_one : ρ < 1 := by dsimp [ρ]; linarith
    have hcomp : 1 - ρ = h := by dsimp [ρ]; ring
    have htφ := radialBoundary_tail α C hα hα_one hC F hF hderiv
      (anglePoint φ) (anglePoint_norm φ) ρ hρ hρ_one
    have htθ := radialBoundary_tail α C hα hα_one hC F hF hderiv
      (anglePoint θ) (anglePoint_norm θ) ρ hρ hρ_one
    have ha := inner_arc_estimate α C hC F hF hderiv ρ hρ hρ_one θ φ hpos.le
    rw [hcomp] at htφ htθ ha
    have harc : ‖F ((ρ : ℂ) * anglePoint φ) - F ((ρ : ℂ) * anglePoint θ)‖ ≤
        C * h ^ α := by
      apply ha.trans
      change C * ρ * h ^ (α - 1) * h ≤ C * h ^ α
      rw [Real.rpow_sub_one hh.ne']
      have he : C * ρ * (h ^ α / h) * h = ρ * (C * h ^ α) := by
        field_simp
      rw [he]
      exact mul_le_of_le_one_left (mul_nonneg hC (Real.rpow_nonneg hh.le _)) hρ_one.le
    calc
      ‖radialBoundary F (anglePoint φ) - radialBoundary F (anglePoint θ)‖ ≤
          ‖radialBoundary F (anglePoint φ) - F ((ρ : ℂ) * anglePoint φ)‖ +
          ‖F ((ρ : ℂ) * anglePoint φ) - F ((ρ : ℂ) * anglePoint θ)‖ +
          ‖F ((ρ : ℂ) * anglePoint θ) - radialBoundary F (anglePoint θ)‖ := by
        exact (norm_sub_le_norm_sub_add_norm_sub _ (F ((ρ : ℂ) * anglePoint θ)) _).trans
          (add_le_add (norm_sub_le_norm_sub_add_norm_sub _ (F ((ρ : ℂ) * anglePoint φ)) _) le_rfl)
      _ ≤ (C / α) * h ^ α + C * h ^ α + (C / α) * h ^ α := by
        rw [norm_sub_rev (F _) (radialBoundary _ _)]
        exact add_le_add (add_le_add htφ harc) htθ
      _ = C * (2 / α + 1) * (φ - θ) ^ α := by dsimp [h]; ring

  rcases lt_trichotomy θ φ with hlt | rfl | hgt
  · rw [abs_of_pos (sub_pos.mpr hlt)] at hsmall ⊢
    exact radialBoundary_angular_pos α C hα hα_one hC F hF hderiv θ φ hlt hsmall
  · simp [Real.zero_rpow hα.ne']
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hgt)] at hsmall ⊢
    rw [norm_sub_rev]
    exact radialBoundary_angular_pos α C hα hα_one hC F hF hderiv φ θ hgt hsmall
end HolomorphicAnosov.MashreghiRadial
