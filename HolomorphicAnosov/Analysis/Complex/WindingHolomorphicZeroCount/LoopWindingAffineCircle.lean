import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingOmittedPath
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingCongrSub

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_affine_circle (a x : ℂ) (r : ℝ) (hr : 0 < r)
    (hx : x ∈ Metric.ball a r) :
    let γ : ComplexLoop := ⟨fun z ↦ a + r * (z : ℂ) - x, by fun_prop⟩
    ∀ hb : ∀ z, γ z ≠ 0, loopWinding γ 0 hb = 1 := by
  dsimp only
  let σ : ComplexLoop := ⟨fun z ↦ a + r * (z : ℂ), by fun_prop⟩
  have hs (z : Circle) : dist (σ z) a = r := by
    simp [σ, dist_eq_norm, Complex.norm_real, abs_of_pos hr]
  have havoid (y : ℂ) (hy : y ∈ Metric.ball a r) : ∀ z, σ z ≠ y := by
    intro z hz
    have hy' := Metric.mem_ball.mp hy
    rw [← hz, hs z] at hy'
    exact (lt_irrefl r) hy'
  have ha : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  have hcenter : loopWinding σ a (havoid a ha) = 1 := by
    let L : C(↑unitInterval, ℂ) :=
      ⟨fun t ↦ Complex.log (r : ℂ) + (t : ℝ) * (2 * Real.pi * Complex.I), by fun_prop⟩
    apply loopWinding_eq_of_increment _ _ _ L
    · intro t
      simp only [L, ContinuousMap.coe_mk, Complex.exp_add]
      rw [Complex.exp_log (by exact_mod_cast hr.ne')]
      change (r : ℂ) * Complex.exp ((t : ℝ) * (2 * Real.pi * Complex.I)) =
        a + r * (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) - a
      rw [Circle.coe_exp]
      push_cast
      ring_nf
    · dsimp [L]
      simp
  have hpath : OmittedValuePath σ a x := by
    refine ⟨Path.segment a x, ?_⟩
    intro t z
    have hm : Path.segment a x t ∈ Metric.ball a r :=
      (convex_ball a r).segment_subset ha hx (by
        rw [← Path.range_segment]
        exact Set.mem_range_self t)
    exact (havoid _ hm z).symm
  have hw := (loopWinding_omittedPath σ a x (havoid a ha) (havoid x hx) hpath).symm
  intro hb
  apply (loopWinding_congr_sub _ σ 0 x hb (havoid x hx) ?_).trans (hw.trans hcenter)
  intro z
  simp [σ]


end
end HolomorphicAnosov
