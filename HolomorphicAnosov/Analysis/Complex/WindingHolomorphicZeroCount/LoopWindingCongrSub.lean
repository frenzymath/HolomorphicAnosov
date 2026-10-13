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


lemma loopWinding_congr_sub (γ γ' : ComplexLoop) (b b' : ℂ)
    (hb : ∀ z, γ z ≠ b) (hb' : ∀ z, γ' z ≠ b')
    (h : ∀ z, γ z - b = γ' z - b') : loopWinding γ b hb = loopWinding γ' b' hb' := by
  obtain ⟨L, hL, hi⟩ := loopWinding_lift γ' b' hb'
  apply loopWinding_eq_of_increment _ _ _ L (n := loopWinding γ' b' hb')
  · intro t
    rw [hL]
    exact (h _).symm
  · linear_combination hi


end
end HolomorphicAnosov
