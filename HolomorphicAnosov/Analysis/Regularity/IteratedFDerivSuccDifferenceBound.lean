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
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualNorm

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma iteratedFDeriv_succ_difference_bound {N n : ℕ}
    (h : EuclideanSpace ℝ (Fin N) → ℝ) (a b : EuclideanSpace ℝ (Fin N))
    (ha : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ h) a)
    (hb : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ h) b) :
    ‖iteratedFDeriv ℝ (n + 1) h a - iteratedFDeriv ℝ (n + 1) h b‖ ≤
      ∑ i : Fin N, ‖iteratedFDeriv ℝ n
        (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) a -
          iteratedFDeriv ℝ n
        (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) b‖ := by
  classical
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  calc
    ‖(iteratedFDeriv ℝ n (fderiv ℝ h) a - iteratedFDeriv ℝ n (fderiv ℝ h) b) v‖ ≤
        ∑ i : Fin N, ‖(iteratedFDeriv ℝ n (fderiv ℝ h) a -
          iteratedFDeriv ℝ n (fderiv ℝ h) b) v (PiLp.single 2 i (1 : ℝ))‖ :=
      euclidean_dual_norm_le_sum _
    _ ≤ (∑ i : Fin N, ‖iteratedFDeriv ℝ n
        (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) a -
          iteratedFDeriv ℝ n
        (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) b‖) * ∏ j, ‖v j‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      let ev := ContinuousLinearMap.apply ℝ ℝ
        (PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ (Fin N))
      have hea := ev.iteratedFDeriv_comp_left ha (i := n) le_rfl
      have heb := ev.iteratedFDeriv_comp_left hb (i := n) le_rfl
      change iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) a = _ at hea
      change iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) b = _ at heb
      have hval : (iteratedFDeriv ℝ n (fderiv ℝ h) a - iteratedFDeriv ℝ n (fderiv ℝ h) b) v
          (PiLp.single 2 i (1 : ℝ)) =
          (iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) a -
            iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) b) v := by
        rw [hea, heb]
        rfl
      rw [hval]
      exact ContinuousMultilinearMap.le_opNorm _ _


end HolomorphicAnosov
