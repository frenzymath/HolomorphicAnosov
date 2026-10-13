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
import HolomorphicAnosov.Analysis.Regularity.ApproximationDegreeZeroLocalBound
import HolomorphicAnosov.Analysis.Regularity.ApproximationContDiffOn
import HolomorphicAnosov.Analysis.Regularity.ApproximationCoordinateDerivativeHypothesis
import HolomorphicAnosov.Analysis.Regularity.IteratedFDerivSuccDifferenceBound

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_iteratedFDeriv_local_bound {N n : ℕ} (hN : 1 ≤ N)
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
    ∀ a₀ ∈ Ω, ∃ V : Set (EuclideanSpace ℝ (Fin N)),
      IsOpen V ∧ a₀ ∈ V ∧ V ⊆ Ω ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ a ∈ V, ∀ b ∈ V,
          ‖iteratedFDeriv ℝ n h a - iteratedFDeriv ℝ n h b‖ ≤ C * ‖a - b‖ ^ α := by
  classical
  induction n generalizing h with
  | zero =>
    intro a₀ ha₀
    have happ0 := happrox
    simp only [Nat.cast_zero, zero_add] at happ0
    obtain ⟨V, hV, haV, hVΩ, C, hC, he⟩ :=
      approximation_degree_zero_local_bound hα h happ0 a₀ ha₀
    refine ⟨V, hV, haV, hVΩ, C, hC.le, ?_⟩
    intro a ha b hb
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact he b hb a ha
  | succ n ih =>
    have hregular : ContDiffOn ℝ (n + 1 : WithTop ℕ∞) h Ω := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        approximation_contDiffOn hN hΩ hα h hh happrox
    have hderiv := ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp hregular).2.2
    have hcoord : ∀ i : Fin N, ∀ a₀ ∈ Ω,
        ∃ V : Set (EuclideanSpace ℝ (Fin N)),
          IsOpen V ∧ a₀ ∈ V ∧ V ⊆ Ω ∧ ∃ C : ℝ, 0 ≤ C ∧
            ∀ a ∈ V, ∀ b ∈ V,
              ‖iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) a -
                iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) b‖ ≤
                  C * ‖a - b‖ ^ α := by
      intro i
      exact ih _ (hderiv.continuousOn.clm_apply continuousOn_const)
        (approximation_coordinate_derivative_hypothesis hN hα h happrox i)
    intro a₀ ha₀
    choose V hV haV hVΩ C hC hbound using fun i ↦ hcoord i a₀ ha₀
    refine ⟨Ω ∩ ⋂ i, V i, hΩ.inter (isOpen_iInter_of_finite hV),
      ⟨ha₀, Set.mem_iInter.mpr haV⟩, Set.inter_subset_left, ∑ i, C i,
      Finset.sum_nonneg (fun i _ ↦ hC i), ?_⟩
    intro a ha b hb
    calc
      ‖iteratedFDeriv ℝ (n + 1) h a - iteratedFDeriv ℝ (n + 1) h b‖ ≤
          ∑ i : Fin N, ‖iteratedFDeriv ℝ n
            (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) a -
              iteratedFDeriv ℝ n
            (fun y ↦ fderiv ℝ h y (PiLp.single 2 i (1 : ℝ))) b‖ :=
        iteratedFDeriv_succ_difference_bound h a b
          (hderiv.contDiffAt (hΩ.mem_nhds ha.1)) (hderiv.contDiffAt (hΩ.mem_nhds hb.1))
      _ ≤ ∑ i : Fin N, C i * ‖a - b‖ ^ α := by
        apply Finset.sum_le_sum
        intro i _
        exact hbound i a (Set.mem_iInter.mp ha.2 i) b (Set.mem_iInter.mp hb.2 i)
      _ = (∑ i : Fin N, C i) * ‖a - b‖ ^ α := (Finset.sum_mul ..).symm

end HolomorphicAnosov
