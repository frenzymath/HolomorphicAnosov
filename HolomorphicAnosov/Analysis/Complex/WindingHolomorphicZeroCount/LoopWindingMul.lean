import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingLift
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_mul (γ₁ γ₂ : ComplexLoop)
    (h₁ : ∀ z, γ₁ z ≠ 0) (h₂ : ∀ z, γ₂ z ≠ 0) :
    loopWinding (γ₁ * γ₂) 0 (fun z ↦ mul_ne_zero (h₁ z) (h₂ z)) =
      loopWinding γ₁ 0 h₁ + loopWinding γ₂ 0 h₂ := by
  obtain ⟨L₁, hL₁, hi₁⟩ := loopWinding_lift γ₁ 0 h₁
  obtain ⟨L₂, hL₂, hi₂⟩ := loopWinding_lift γ₂ 0 h₂
  apply loopWinding_eq_of_increment _ _ _ (L₁ + L₂)
  · intro t
    simp only [ContinuousMap.add_apply, Complex.exp_add, hL₁, hL₂]
    simp [puncturedLoopPath]
  · push_cast
    change L₁ 1 + L₂ 1 - (L₁ 0 + L₂ 0) = _
    linear_combination hi₁ + hi₂


end
end HolomorphicAnosov
