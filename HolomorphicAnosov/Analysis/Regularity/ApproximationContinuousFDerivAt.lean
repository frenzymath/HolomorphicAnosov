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
import HolomorphicAnosov.Analysis.Regularity.ApproximationFirstJetComparison

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_continuous_fderiv_at {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n)
    (h : EuclideanSpace ℝ (Fin N) → ℝ) (V : Set (EuclideanSpace ℝ (Fin N)))
    (hV : IsOpen V) (a : EuclideanSpace ℝ (Fin N)) (haV : a ∈ V)
    (C r s : ℝ) (hC : 0 ≤ C) (hr : 0 < r) (hs : 1 < s)
    (happ : ∀ b ∈ V, ∃ P : MvPolynomial (Fin N) ℝ, P.totalDegree ≤ n ∧
      ∀ y ∈ Metric.ball b r,
        |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤ C * ‖y - b‖ ^ s) :
    ContinuousAt (fderiv ℝ h) a := by
  obtain ⟨P, hPdeg, hP⟩ := happ a haV
  have haeq : fderiv ℝ h a = polynomialFirstJet P a :=
    (approximation_firstJet_hasFDerivAt h P a C r s hC hr hs hP).fderiv
  obtain ⟨D, _hD, hest⟩ := approximation_firstJet_comparison N n hN hn s (by linarith)
  have hbound : ∀ᶠ b in 𝓝 a,
      ‖fderiv ℝ h b - polynomialFirstJet P b‖ ≤ D * C * ‖b - a‖ ^ (s - 1) := by
    filter_upwards [hV.mem_nhds haV, Metric.ball_mem_nhds a (half_pos hr)] with b hbV hbball
    by_cases hba : b = a
    · subst b
      simp only [haeq, sub_self, norm_zero, Real.zero_rpow (by linarith : s - 1 ≠ 0),
        mul_zero, le_refl]
    have hρ : 0 < dist b a := dist_pos.mpr hba
    have hρr : 2 * dist b a < r := by
      have he := Metric.mem_ball.mp hbball
      linarith
    obtain ⟨Q, hQdeg, hQ⟩ := happ b hbV
    have hbeq : fderiv ℝ h b = polynomialFirstJet Q b :=
      (approximation_firstJet_hasFDerivAt h Q b C r s hC hr hs hQ).fderiv
    rw [hbeq, norm_sub_rev]
    simpa only [dist_eq_norm] using
      hest h Q P b a C (dist b a) hQdeg hPdeg hC hρ le_rfl
        (fun y hy ↦ hQ y ((Metric.ball_subset_ball hρr.le) hy))
        (fun y hy ↦ hP y ((Metric.ball_subset_ball hρr.le) hy))
  have ht : Tendsto (fun b : EuclideanSpace ℝ (Fin N) ↦
      D * C * ‖b - a‖ ^ (s - 1)) (𝓝 a) (𝓝 0) := by
    have hpow := (Real.continuousAt_rpow_const 0 (s - 1) (Or.inr (by linarith))).tendsto.comp
      (tendsto_norm_sub_self a)
    simpa only [Function.comp_def, Real.zero_rpow (by linarith : s - 1 ≠ 0), mul_zero] using
      hpow.const_mul (D * C)
  have he := (squeeze_zero_norm' hbound ht).add
    (polynomialFirstJet_continuous P).continuousAt.tendsto
  have hfun : (fun b ↦ fderiv ℝ h b - polynomialFirstJet P b + polynomialFirstJet P b) =
      fderiv ℝ h := by
    funext b
    exact sub_add_cancel _ _
  rw [hfun, zero_add, ← haeq] at he
  exact he

end HolomorphicAnosov
