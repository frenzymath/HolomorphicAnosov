import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import HolomorphicAnosov.Analysis.Regularity.ApproximationPolynomialDifferenceBound
import HolomorphicAnosov.Analysis.Regularity.ApproximationPolynomialJetComparison
import HolomorphicAnosov.Analysis.Regularity.ApproximationRemainderFDerivAt
import HolomorphicAnosov.Analysis.Regularity.PolynomialFirstJet
import HolomorphicAnosov.Analysis.Regularity.PolynomialFirstJetSingle
import HolomorphicAnosov.Analysis.Regularity.PolynomialTranslateDerivatives
import HolomorphicAnosov.Analysis.Regularity.HolderOnWithNormBound
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualCoordinate
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualNorm
import HolomorphicAnosov.Analysis.Regularity.IteratedFDerivSuccDifferenceBound
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_degree_zero_local_bound {N : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin N))} {α : ℝ} (hα : 0 < α)
    (h : EuclideanSpace ℝ (Fin N) → ℝ)
    (happrox : ∀ a₀ ∈ Ω,
      ∃ V : Set (EuclideanSpace ℝ (Fin N)), IsOpen V ∧ a₀ ∈ V ∧
        ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
          ∀ a ∈ V, ∃ P : MvPolynomial (Fin N) ℝ,
            P.totalDegree ≤ 0 ∧ Metric.ball a r ⊆ Ω ∧
              ∀ y ∈ Metric.ball a r,
                |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤ C * ‖y - a‖ ^ α) :
    ∀ a₀ ∈ Ω, ∃ V : Set (EuclideanSpace ℝ (Fin N)),
      IsOpen V ∧ a₀ ∈ V ∧ V ⊆ Ω ∧ ∃ C : ℝ, 0 < C ∧
        ∀ a ∈ V, ∀ b ∈ V, |h b - h a| ≤ C * ‖b - a‖ ^ α := by
  intro a₀ ha₀
  obtain ⟨V, hV, haV, C, hC, r, hr, happ⟩ := happrox a₀ ha₀
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV a₀ haV
  let R : ℝ := min (δ / 4) (r / 4)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRδ : R ≤ δ / 4 := min_le_left _ _
  have hRr : R ≤ r / 4 := min_le_right _ _
  have hWV : Metric.ball a₀ R ⊆ V := by
    intro a ha
    apply hδV
    apply Metric.mem_ball.mpr
    have he := Metric.mem_ball.mp ha
    linarith
  have hWΩ : Metric.ball a₀ R ⊆ Ω := by
    intro a ha
    obtain ⟨P, _hdeg, hball, _he⟩ := happ a (hWV ha)
    exact hball (Metric.mem_ball_self hr)
  refine ⟨Metric.ball a₀ R, Metric.isOpen_ball, Metric.mem_ball_self hR, hWΩ, C, hC, ?_⟩
  intro a ha b hb
  obtain ⟨P, hdeg, _hball, he⟩ := happ a (hWV ha)
  have hPconst : P = MvPolynomial.C (P.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
  have hea := he a (Metric.mem_ball_self hr)
  rw [hPconst, MvPolynomial.eval_C] at hea
  simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hea
  have haeq : h a = P.coeff 0 := sub_eq_zero.mp (abs_nonpos_iff.mp hea)
  have hbar : b ∈ Metric.ball a r := by
    apply Metric.mem_ball.mpr
    have ha' := Metric.mem_ball.mp ha
    have hb' := Metric.mem_ball.mp hb
    have ht := dist_triangle b a₀ a
    rw [dist_comm a₀ a] at ht
    linarith
  have heb := he b hbar
  rw [hPconst, MvPolynomial.eval_C] at heb
  rw [← haeq] at heb
  exact heb

end HolomorphicAnosov
