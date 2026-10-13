import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingLift

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_increment (γ : ComplexLoop) (b : ℂ) (hb : ∀ z, γ z ≠ b)
    (L : C(↑unitInterval, ℂ))
    (hL : ∀ t, Complex.exp (L t) = (puncturedLoopPath γ b hb t : ℂ)) :
    L 1 - L 0 = (loopWinding γ b hb : ℂ) * (2 * Real.pi * Complex.I) := by
  obtain ⟨K, hK, hk⟩ := loopWinding_lift γ b hb
  have hc : Continuous (fun t ↦ L t - K t) := L.continuous.sub K.continuous
  have he : ∀ t t',
      (⟨Complex.exp (L t - K t), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) =
      ⟨Complex.exp (L t' - K t'), Complex.exp_ne_zero _⟩ := by
    intro t t'
    apply Subtype.ext
    simp only [Complex.exp_sub, hL, hK]
    simp only [div_self (puncturedLoopPath γ b hb _).property]
  have hd := Complex.isCoveringMap_exp.const_of_comp hc he
    (1 : unitInterval) (0 : unitInterval)
  linear_combination hd + hk


end
end HolomorphicAnosov
