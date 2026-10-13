import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Topology.Compactness.Lindelof

/-!
The closed-set criterion for almost-everywhere membership from measurable-set averages on a finite
measure space. (Rudin, Thm 1.40, pp. 30–31)
-/

open MeasureTheory

namespace HolomorphicAnosov

/-- If every positive-mass measurable-set average of an integrable measurable complex function lies
in a closed set, then the function lies in that set almost everywhere. (Rudin, Thm 1.40, pp.
30–31) -/
theorem rudin_closed_set_average_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℂ) (hf_measurable : Measurable f) (hf_integrable : Integrable f μ)
    (S : Set ℂ) (hS : IsClosed S)
    (h_average : ∀ E : Set X, MeasurableSet E → 0 < μ E →
      ((μ E).toReal)⁻¹ • (∫ x in E, f x ∂μ) ∈ S) :
    ∀ᵐ x ∂μ, f x ∈ S := by
  classical
  have hnull (c : ℂ) (r : ℝ) (hdisc : Metric.closedBall c r ⊆ Sᶜ) :
      μ (f ⁻¹' Metric.closedBall c r) = 0 := by
    by_contra hpos
    have hE : MeasurableSet (f ⁻¹' Metric.closedBall c r) :=
      hf_measurable Metric.isClosed_closedBall.measurableSet
    have havg := (convex_closedBall c r).set_average_mem Metric.isClosed_closedBall hpos
      (measure_ne_top μ _) (ae_restrict_mem hE) hf_integrable.integrableOn
    rw [setAverage_eq, measureReal_def] at havg
    exact hdisc havg (h_average _ hE (bot_lt_iff_ne_bot.mpr hpos))
  have hrad : ∀ z : ↥(Sᶜ : Set ℂ), ∃ r : ℝ, 0 < r ∧ Metric.closedBall (z : ℂ) r ⊆ Sᶜ := by
    intro z
    exact Metric.nhds_basis_closedBall.mem_iff.mp (hS.isOpen_compl.mem_nhds z.property)
  choose r hr hsub using hrad
  obtain ⟨t, ht, hcover⟩ := (HereditarilyLindelofSpace.isLindelof Sᶜ).elim_nhds_subcover'
    (fun z hz => Metric.closedBall z (r ⟨z, hz⟩))
    (fun z hz => Metric.closedBall_mem_nhds _ (hr ⟨z, hz⟩))
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ z ∈ t, f ⁻¹' Metric.closedBall (z : ℂ) (r z))
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact Set.mem_iUnion₂.mpr ⟨z, hz, hxz⟩
  · exact (measure_biUnion_null_iff ht).mpr fun z _ => hnull z (r z) (hsub z)


end HolomorphicAnosov

