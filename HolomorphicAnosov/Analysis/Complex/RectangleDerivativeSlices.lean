import HolomorphicAnosov.Analysis.Measure.LengthEnergyBound
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrable horizontal derivatives from finite rectangle energy

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed p.342, the finite-area Cauchy–Schwarz and Fubini
steps. Lehto–Virtanen (1973), I.Theorem 3.1, printed pp.18–19 and footnote 5,
uses Fubini to justify the horizontal integrals without boundary differentiability.
-/

open Set MeasureTheory
open scoped ENNReal

namespace HolomorphicAnosov.Analysis.Complex

/-- Finite quadratic energy of a holomorphic rectangle map gives integrability
of its complex derivative along almost every full horizontal interval.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, p.342 and
Lehto–Virtanen (1973), I.Theorem 3.1, pp.18–19, footnote 5.
Proof: The derivative of a holomorphic function is continuous in the open
rectangle. Its coordinate pullback is therefore measurable for the restricted
product measure. The finite-energy Cauchy–Schwarz estimate on the finite
rectangle makes its norm integrable. Norm integrability and measurability make
the complex derivative itself integrable. Fubini gives integrability of its
horizontal slices almost everywhere. Lebesgue-null endpoint singletons convert
the integrability on the open interval to interval integrability. No derivative
of a boundary extension is asserted.
-/
theorem ae_intervalIntegrable_rectangle_deriv
    {a b : ℝ} (ha : 0 ≤ a) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Complex.reProdIm (Ioo 0 a) (Ioo 0 b)))
    (henergy : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (‖deriv f (⟨p.1, p.2⟩ : ℂ)‖ ^ 2)
      ∂(volume.restrict (Ioo 0 a)).prod (volume.restrict (Ioo 0 b))) ≠ ⊤) :
    ∀ᵐ y : ℝ ∂volume.restrict (Ioo 0 b),
      IntervalIntegrable (fun x : ℝ ↦ deriv f (⟨x, y⟩ : ℂ)) volume 0 a := by
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦ deriv f (⟨p.1, p.2⟩ : ℂ))
      (Ioo 0 a ×ˢ Ioo 0 b) := by
    apply (hf.deriv (isOpen_Ioo.reProdIm isOpen_Ioo)).continuousOn.comp
      Complex.equivRealProdCLM.symm.continuous.continuousOn
    intro p hp
    exact hp
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ deriv f (⟨p.1, p.2⟩ : ℂ))
      ((volume.restrict (Ioo 0 a)).prod (volume.restrict (Ioo 0 b))) := by
    rw [Measure.prod_restrict]
    exact hc.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)
  have hnorm := (Analysis.Measure.integrable_and_integral_sq_le_mass_mul_energy
    hm.norm (ae_of_all _ (fun _ ↦ norm_nonneg _)) henergy).1
  have hi := hnorm.mono' hm (ae_of_all _ (fun _ ↦ le_rfl))
  filter_upwards [hi.prod_left_ae] with y hy
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ha).mpr hy

end HolomorphicAnosov.Analysis.Complex

