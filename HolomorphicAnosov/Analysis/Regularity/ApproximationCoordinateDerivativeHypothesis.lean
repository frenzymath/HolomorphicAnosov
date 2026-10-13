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
import HolomorphicAnosov.Analysis.Regularity.ApproximationCoordinateDerivativeError

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_coordinate_derivative_hypothesis {N n : ℕ} (hN : 1 ≤ N)
    {Ω : Set (EuclideanSpace ℝ (Fin N))} {α : ℝ} (hα : 0 < α)
    (h : EuclideanSpace ℝ (Fin N) → ℝ)
    (happrox : ∀ a₀ ∈ Ω,
      ∃ V : Set (EuclideanSpace ℝ (Fin N)), IsOpen V ∧ a₀ ∈ V ∧
        ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
          ∀ a ∈ V, ∃ P : MvPolynomial (Fin N) ℝ,
            P.totalDegree ≤ n + 1 ∧ Metric.ball a r ⊆ Ω ∧
              ∀ y ∈ Metric.ball a r,
                |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤
                  C * ‖y - a‖ ^ ((n + 1 : ℕ) + α))
    (i : Fin N) :
    ∀ a₀ ∈ Ω,
      ∃ V : Set (EuclideanSpace ℝ (Fin N)), IsOpen V ∧ a₀ ∈ V ∧
        ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
          ∀ a ∈ V, ∃ P : MvPolynomial (Fin N) ℝ,
            P.totalDegree ≤ n ∧ Metric.ball a r ⊆ Ω ∧
              ∀ y ∈ Metric.ball a r,
                |fderiv ℝ h y (PiLp.single 2 i (1 : ℝ)) -
                  MvPolynomial.eval (fun j ↦ y j) P| ≤ C * ‖y - a‖ ^ ((n : ℝ) + α) := by
  intro a₀ ha₀
  obtain ⟨V, hV, haV, C, hC, r, hr, happ⟩ := happrox a₀ ha₀
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV a₀ haV
  have hs : 1 < ((n + 1 : ℕ) : ℝ) + α := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨D, hD, hest⟩ := approximation_coordinate_derivative_error N (n + 1)
    hN (by omega) (((n + 1 : ℕ) : ℝ) + α) hs
  let R : ℝ := min (δ / 4) (r / 4)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRδ : R ≤ δ / 4 := min_le_left _ _
  have hRr : R ≤ r / 4 := min_le_right _ _
  refine ⟨Metric.ball a₀ (δ / 4), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    D * C, mul_pos hD hC, R, hR, ?_⟩
  intro a ha
  have haV' : a ∈ V := hδV (Metric.mem_ball.mpr (by
    have he := Metric.mem_ball.mp ha
    linarith))
  obtain ⟨P, hPdeg, hball, hP⟩ := happ a haV'
  refine ⟨MvPolynomial.pderiv i P, polynomial_pderiv_degree P hPdeg i,
    (Metric.ball_subset_ball (by linarith : R ≤ r)).trans hball, ?_⟩
  intro b hb
  have hbV : b ∈ V := by
    apply hδV
    apply Metric.mem_ball.mpr
    have hba := Metric.mem_ball.mp hb
    have ha₀ := Metric.mem_ball.mp ha
    have ht := dist_triangle b a a₀
    linarith
  obtain ⟨Q, hQdeg, _hQball, hQ⟩ := happ b hbV
  have hdist : dist b a < r / 2 := by
    have he := Metric.mem_ball.mp hb
    linarith
  have hexp : ((n + 1 : ℕ) : ℝ) + α - 1 = (n : ℝ) + α := by
    push_cast
    ring
  simpa only [hexp] using hest h P Q a b C r hPdeg hQdeg hC.le hr hdist hP hQ i

end HolomorphicAnosov
