import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingIncrement

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_eq_of_increment (γ : ComplexLoop) (b : ℂ)
    (hb : ∀ z, γ z ≠ b) (L : C(↑unitInterval, ℂ))
    (hL : ∀ t, Complex.exp (L t) = (puncturedLoopPath γ b hb t : ℂ)) (n : ℤ)
    (hn : L 1 - L 0 = (n : ℂ) * (2 * Real.pi * Complex.I)) :
    loopWinding γ b hb = n := by
  have hτ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have := (loopWinding_increment γ b hb L hL).symm.trans hn
  exact_mod_cast (mul_right_cancel₀ hτ this)


end
end HolomorphicAnosov
