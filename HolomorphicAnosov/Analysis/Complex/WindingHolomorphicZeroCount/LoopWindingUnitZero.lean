import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_unit_zero :
    loopWinding unitCircleLoop 0 (fun z ↦ by exact Circle.coe_ne_zero z) = 1 := by
  let L : C(↑unitInterval, ℂ) :=
    ⟨fun t ↦ (t : ℝ) * (2 * Real.pi * Complex.I), by fun_prop⟩
  apply loopWinding_eq_of_increment _ _ _ L
  · intro t
    dsimp [L, puncturedLoopPath, unitCircleLoop]
    simp only [sub_zero]
    change Complex.exp ((t : ℝ) * (2 * Real.pi * Complex.I)) =
      (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ)
    rw [Circle.coe_exp]
    congr 1
    push_cast
    ring_nf
  · dsimp [L]
    simp


end
end HolomorphicAnosov
