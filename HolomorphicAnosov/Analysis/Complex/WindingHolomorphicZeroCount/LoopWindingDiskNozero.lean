import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingHomotopy
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingConstant

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_disk_nozero (a : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (hr : 0 < r) (hf : ContinuousOn f (Metric.closedBall a r))
    (hne : ∀ x ∈ Metric.closedBall a r, f x ≠ 0) :
    loopWinding (diskBoundaryLoop a r f hr hf) 0
      (fun z ↦ hne _ (by
        rw [Metric.mem_closedBall]
        simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr])) = 0 := by
  have ha : a ∈ Metric.closedBall a r := Metric.mem_closedBall_self hr.le
  apply (loopWinding_homotopy _ (constantLoop (f a)) 0 _ (fun _ ↦ hne a ha) ?_).trans
    (loopWinding_constant (f a) 0 (hne a ha))
  have hmem (t : unitInterval) (z : Circle) :
      a + ((1 - (t : ℝ)) * r : ℝ) * (z : ℂ) ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Circle.norm_coe, mul_one]
    rw [Real.norm_of_nonneg (sub_nonneg.mpr t.property.2), Real.norm_of_nonneg hr.le]
    nlinarith [t.property.1]
  refine ⟨⟨fun tz ↦ f (a + ((1 - (tz.1 : ℝ)) * r : ℝ) * (tz.2 : ℂ)),
    hf.comp_continuous (by fun_prop) (fun tz ↦ hmem tz.1 tz.2)⟩, ?_, ?_, ?_⟩
  · intro z
    simp only [ContinuousMap.coe_mk, Set.Icc.coe_zero, sub_zero, one_mul]
    rfl
  · intro z
    simp [constantLoop]
  · intro t z
    exact hne _ (hmem t z)


end
end HolomorphicAnosov
