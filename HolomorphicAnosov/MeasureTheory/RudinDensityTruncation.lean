import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Function.AEMeasurableOrder
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

open MeasureTheory Set

namespace HolomorphicAnosov

/-- A measurable complex function with norm at most one almost everywhere has a measurable
representative with norm at most one everywhere, equal to it almost everywhere. -/
theorem measurable_complex_density_truncation
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (h : X → ℂ)
    (hh : Measurable h) (hae : ∀ᵐ x ∂μ, ‖h x‖ ≤ 1) :
    ∃ g : X → ℂ, Measurable g ∧ (∀ x, ‖g x‖ ≤ 1) ∧ g =ᵐ[μ] h := by
  classical
  let S : Set X := {x | ‖h x‖ ≤ 1}
  have hnorm : Measurable (fun x => ‖h x‖) := continuous_norm.measurable.comp hh
  have hS : MeasurableSet S := by
    exact measurableSet_le hnorm measurable_const
  let g : X → ℂ := S.indicator h
  refine ⟨g, hh.indicator hS, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ S
    · have hx' : ‖h x‖ ≤ 1 := by simpa [S] using hx
      simpa [g, Set.indicator_of_mem hx] using hx'
    · simp [g, hx]
  · filter_upwards [hae] with x hx
    by_cases hxs : x ∈ S
    · simp [g, Set.indicator_of_mem hxs]
    · exact (hxs (by simpa [S] using hx)).elim

end HolomorphicAnosov
