import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingOmittedPath
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingUnitZero

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_unit (b : ℂ) (hb : ∀ z, unitCircleLoop z ≠ b)
    (hbsmall : ‖b‖ < 1) : loopWinding unitCircleLoop b hb = 1 := by
  have h := loopWinding_omittedPath unitCircleLoop 0 b
    (fun z ↦ Circle.coe_ne_zero z) hb (by
      refine ⟨⟨⟨fun t ↦ (t : ℝ) • b, by fun_prop⟩, by simp, by simp⟩, ?_⟩
      intro t z hz
      have hn := congrArg norm hz
      have hsmall : ‖(t : ℝ) • b‖ < 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg b) t.property.2) hbsmall
      exact (ne_of_lt hsmall) (hn.trans (Circle.norm_coe z)))
  exact h.symm.trans loopWinding_unit_zero


end
end HolomorphicAnosov
