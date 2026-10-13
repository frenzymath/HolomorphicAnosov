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


lemma loopWinding_constant (c b : ℂ) (hb : c ≠ b) :
    loopWinding (constantLoop c) b (fun _ ↦ hb) = 0 := by
  apply loopWinding_eq_of_increment _ _ _ (.const _ (Complex.log (c - b)))
  · intro t
    exact Complex.exp_log (sub_ne_zero.mpr hb)
  · simp


end
end HolomorphicAnosov
