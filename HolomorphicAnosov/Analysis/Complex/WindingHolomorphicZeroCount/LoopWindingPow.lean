import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingConstant
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingMul

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_pow (γ : ComplexLoop) (h : ∀ z, γ z ≠ 0) (n : ℕ) :
    loopWinding (γ ^ n) 0 (fun z ↦ pow_ne_zero n (h z)) =
      (n : ℤ) * loopWinding γ 0 h := by
  induction n with
  | zero =>
    have he : γ ^ 0 = constantLoop 1 := by ext; simp [constantLoop]
    simp only [he, Nat.cast_zero, zero_mul]
    exact loopWinding_constant 1 0 one_ne_zero
  | succ n ih =>
    have hm := loopWinding_mul (γ ^ n) γ (fun z ↦ pow_ne_zero n (h z)) h
    simpa only [← pow_succ, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hm


end
end HolomorphicAnosov
