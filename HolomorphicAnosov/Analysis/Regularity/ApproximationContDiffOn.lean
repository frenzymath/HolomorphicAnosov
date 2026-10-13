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
import HolomorphicAnosov.Analysis.Regularity.ApproximationFirstJetHasFDerivAt
import HolomorphicAnosov.Analysis.Regularity.ApproximationContinuousFDerivAt
import HolomorphicAnosov.Analysis.Regularity.ApproximationCoordinateDerivativeHypothesis
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualCoordinate

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_contDiffOn {N n : ℕ} (hN : 1 ≤ N)
    {Ω : Set (EuclideanSpace ℝ (Fin N))} (hΩ : IsOpen Ω)
    {α : ℝ} (hα : 0 < α)
    (h : EuclideanSpace ℝ (Fin N) → ℝ) (hh : ContinuousOn h Ω)
    (happrox : ∀ a₀ ∈ Ω,
      ∃ V : Set (EuclideanSpace ℝ (Fin N)), IsOpen V ∧ a₀ ∈ V ∧
        ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
          ∀ a ∈ V, ∃ P : MvPolynomial (Fin N) ℝ,
            P.totalDegree ≤ n ∧ Metric.ball a r ⊆ Ω ∧
              ∀ y ∈ Metric.ball a r,
                |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤
                  C * ‖y - a‖ ^ ((n : ℝ) + α)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) h Ω := by
  induction n generalizing h with
  | zero => exact contDiffOn_zero.mpr hh
  | succ n ih =>
    have hs : 1 < ((n + 1 : ℕ) : ℝ) + α := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hd : DifferentiableOn ℝ h Ω := by
      intro a ha
      obtain ⟨V, _hV, haV, C, hC, r, hr, happ⟩ := happrox a ha
      obtain ⟨P, _hP, _hball, herror⟩ := happ a haV
      exact (approximation_firstJet_hasFDerivAt h P a C r _ hC.le hr hs herror).differentiableAt.differentiableWithinAt
    have hc : ContinuousOn (fderiv ℝ h) Ω := by
      intro a ha
      obtain ⟨V, hV, haV, C, hC, r, hr, happ⟩ := happrox a ha
      exact (approximation_continuous_fderiv_at hN (Nat.succ_pos n) h V hV a haV
        C r _ hC.le hr hs (fun b hb ↦ by
          obtain ⟨P, hdeg, _hball, he⟩ := happ b hb
          exact ⟨P, hdeg, he⟩)).continuousWithinAt
    have hcoord : ∀ i : Fin N, ContDiffOn ℝ (n : WithTop ℕ∞)
        (fun a ↦ fderiv ℝ h a (PiLp.single 2 i (1 : ℝ))) Ω := by
      intro i
      exact ih _ (hc.clm_apply continuousOn_const)
        (approximation_coordinate_derivative_hypothesis hN hα h happrox i)
    have hderiv : ContDiffOn ℝ (n : WithTop ℕ∞) (fderiv ℝ h) Ω := by
      have heq : fderiv ℝ h = fun a ↦ ∑ i : Fin N,
          fderiv ℝ h a (PiLp.single 2 i (1 : ℝ)) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i) := by
        funext a
        exact euclidean_dual_coordinate_sum _
      rw [heq]
      exact ContDiffOn.sum (fun i _ ↦ (hcoord i).smul contDiffOn_const)
    rw [Nat.cast_add, Nat.cast_one]
    exact (contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mpr
      ⟨hd, by simp, hderiv⟩

end HolomorphicAnosov
