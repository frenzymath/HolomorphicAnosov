import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_lift (γ : ComplexLoop) (b : ℂ) (hb : ∀ z, γ z ≠ b) :
    ∃ L : C(↑unitInterval, ℂ),
      (∀ t, Complex.exp (L t) = (puncturedLoopPath γ b hb t : ℂ)) ∧
      L 1 = L 0 + (loopWinding γ b hb : ℂ) * (2 * Real.pi * Complex.I) := by
  let c := puncturedLoopPath γ b hb
  let e : ℂ := Complex.log (c 0)
  have he : c 0 = (⟨Complex.exp e, Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) := by
    apply Subtype.ext
    exact (Complex.exp_log (c 0).property).symm
  let L := Complex.isCoveringMap_exp.liftPath c e he
  refine ⟨L, ?_, ?_⟩
  · intro t
    exact congrArg Subtype.val (congrFun
      (Complex.isCoveringMap_exp.liftPath_lifts c e he) t)
  · have hl := Complex.isCoveringMap_exp.liftPath_lifts c e he
    have hperiod : c 1 = c 0 := by
      apply Subtype.ext
      dsimp [c, puncturedLoopPath]
      congr 2
      apply Subtype.ext
      simp [Circle.coe_exp, Complex.exp_two_pi_mul_I]
    have hexp : Complex.exp (L 1) = Complex.exp (L 0) := by
      have h1 := congrArg Subtype.val (congrFun hl (1 : unitInterval))
      have h0 := congrArg Subtype.val (congrFun hl (0 : unitInterval))
      exact h1.trans ((congrArg Subtype.val hperiod).trans h0.symm)
    exact Classical.choose_spec (Complex.exp_eq_exp_iff_exists_int.mp hexp)


end
end HolomorphicAnosov
