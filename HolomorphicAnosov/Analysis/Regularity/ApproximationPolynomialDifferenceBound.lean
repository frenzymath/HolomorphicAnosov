import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
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

lemma approximation_polynomial_difference_bound {N : ℕ}
    (h : EuclideanSpace ℝ (Fin N) → ℝ) (P Q : MvPolynomial (Fin N) ℝ)
    (a b : EuclideanSpace ℝ (Fin N)) (C ρ s : ℝ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hs : 0 ≤ s) (hab : dist a b ≤ ρ)
    (hP : ∀ y ∈ Metric.ball a (2 * ρ),
      |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤ C * ‖y - a‖ ^ s)
    (hQ : ∀ y ∈ Metric.ball b (2 * ρ),
      |h y - MvPolynomial.eval (fun i ↦ y i) Q| ≤ C * ‖y - b‖ ^ s) :
    ∀ y ∈ Metric.ball a ρ,
      |MvPolynomial.eval (fun i ↦ y i) (Q - P)| ≤ 2 * C * (2 * ρ) ^ s := by
  intro y hy
  have hya : dist y a < ρ := Metric.mem_ball.mp hy
  have hyb : dist y b < 2 * ρ := by
    calc
      dist y b ≤ dist y a + dist a b := dist_triangle _ _ _
      _ < 2 * ρ := by linarith
  have hya' : dist y a < 2 * ρ := by linarith
  have hp := hP y (Metric.mem_ball.mpr hya')
  have hq := hQ y (Metric.mem_ball.mpr hyb)
  have hp' := Real.rpow_le_rpow (norm_nonneg (y - a)) hya'.le hs
  have hq' := Real.rpow_le_rpow (norm_nonneg (y - b)) hyb.le hs
  rw [map_sub]
  calc
    |MvPolynomial.eval (fun i ↦ y i) Q - MvPolynomial.eval (fun i ↦ y i) P| ≤
        |h y - MvPolynomial.eval (fun i ↦ y i) Q| +
          |h y - MvPolynomial.eval (fun i ↦ y i) P| := by
      have he := abs_add_le (-(h y - MvPolynomial.eval (fun i ↦ y i) Q))
        (h y - MvPolynomial.eval (fun i ↦ y i) P)
      have hid : -(h y - MvPolynomial.eval (fun i ↦ y i) Q) +
          (h y - MvPolynomial.eval (fun i ↦ y i) P) =
            MvPolynomial.eval (fun i ↦ y i) Q - MvPolynomial.eval (fun i ↦ y i) P := by ring
      rwa [hid, abs_neg] at he
    _ ≤ C * (2 * ρ) ^ s + C * (2 * ρ) ^ s :=
      add_le_add (hq.trans (mul_le_mul_of_nonneg_left hq' hC))
        (hp.trans (mul_le_mul_of_nonneg_left hp' hC))
    _ = 2 * C * (2 * ρ) ^ s := by ring



-- Campanato's two-centre coefficient estimate, with the original unnormalized partials.


end HolomorphicAnosov
