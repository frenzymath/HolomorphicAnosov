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


lemma loopWinding_prod {ι : Type*} (s : Finset ι) (γ : ι → ComplexLoop)
    (hne : ∀ i z, γ i z ≠ 0) :
    loopWinding (∏ i ∈ s, γ i) 0
      (fun z ↦ by simpa only [ContinuousMap.prod_apply] using
        Finset.prod_ne_zero_iff.mpr (fun i (_ : i ∈ s) ↦ hne i z)) =
      ∑ i ∈ s, loopWinding (γ i) 0 (hne i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    have he : (1 : ComplexLoop) = constantLoop 1 := by ext; rfl
    simpa only [Finset.prod_empty, Finset.sum_empty, he] using
      loopWinding_constant 1 0 one_ne_zero
  | cons i s hi ih =>
    have hw := loopWinding_mul (γ i) (∏ j ∈ s, γ j) (hne i)
      (fun z ↦ by simpa only [ContinuousMap.prod_apply] using
        Finset.prod_ne_zero_iff.mpr (fun j (_ : j ∈ s) ↦ hne j z))
    simpa only [Finset.prod_cons, Finset.sum_cons, ih] using hw


end
end HolomorphicAnosov
