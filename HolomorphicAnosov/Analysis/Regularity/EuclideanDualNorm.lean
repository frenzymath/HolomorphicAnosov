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
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualCoordinate

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma euclidean_dual_norm_le_sum {N : ℕ}
    (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin N, ‖L (PiLp.single 2 i (1 : ℝ))‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  intro v
  conv_lhs => rw [euclidean_dual_coordinate_sum L]
  simp only [sum_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
  calc
    ‖∑ i, L (PiLp.single 2 i (1 : ℝ)) * v i‖ ≤
        ∑ i, ‖L (PiLp.single 2 i (1 : ℝ)) * v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖L (PiLp.single 2 i (1 : ℝ))‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i, ‖L (PiLp.single 2 i (1 : ℝ))‖) * ‖v‖ := (Finset.sum_mul ..).symm


end HolomorphicAnosov
