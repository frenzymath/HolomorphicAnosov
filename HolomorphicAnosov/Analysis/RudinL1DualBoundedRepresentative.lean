import HolomorphicAnosov.Analysis.RudinFiniteComplexL1Dual
import HolomorphicAnosov.MeasureTheory.RudinDensityTruncation

open MeasureTheory

namespace HolomorphicAnosov

/-- A contraction on complex L¹ over a finite measure has a measurable,
everywhere unit-bounded density, with genuine integrability of all pairings.

Source: Rudin, *Real and Complex Analysis*, third edition, Theorem 6.19,
printed p. 131, equation (6), applying Theorem 6.16 (pp. 127–128).
The local source is `literature/Rudin-Real-and-Complex-Analysis-3rd-1987.pdf`.

Proof: the finite-measure L¹ dual theorem supplies a measurable density h
bounded almost everywhere by the operator norm. The contraction hypothesis
makes this bound at most one. Replace h by zero outside its measurable
unit-bounded set using `measurable_complex_density_truncation`. Multiplication
of an integrable function by this bounded measurable representative is
integrable. Almost-everywhere equality of the densities preserves each
product integral, hence preserves the original L¹ dual representation.
The construction includes zero measures and empty measurable spaces. -/
theorem rudin_l1_dual_bounded_representative
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : Lp ℂ 1 μ →L[ℂ] ℂ) (hT : ‖T‖ ≤ 1) :
    ∃ g : X → ℂ, Measurable g ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      ∀ (f : X → ℂ) (hf : Integrable f μ),
        Integrable (fun x ↦ f x * g x) μ ∧
          T (hf.toL1 f) = ∫ x, f x * g x ∂μ := by
  obtain ⟨h, hm, hb, hrepr⟩ := rudin_finite_complex_l1_dual μ T
  obtain ⟨g, hg, hbound, hgh⟩ := measurable_complex_density_truncation μ h hm
    (hb.mono fun x hx ↦ hx.trans hT)
  refine ⟨g, hg, hbound, ?_⟩
  intro f hf
  refine ⟨hf.mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound), ?_⟩
  rw [(hrepr f hf).2]
  apply integral_congr_ae
  filter_upwards [hgh] with x hx
  rw [hx]

end HolomorphicAnosov

