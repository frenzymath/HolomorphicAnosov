import HolomorphicAnosov.Analysis.InteriorVariationBound
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Complex.Basic

/-!
# Interval energy bound used in Rengel's inequality

Source: Lehto–Virtanen, Quasiconformal Mappings in the Plane, second edition (1973),
Chapter I §4.3, pp.22–23. The displayed inverse-canonical-map calculation applies
Schwarz's inequality to the integral of the derivative norm along a segment.
The endpoint passage below makes explicit the extension to continuous boundary values
without assuming endpoint derivatives or finite energy.
-/

open Set MeasureTheory
open scoped ENNReal

namespace HolomorphicAnosov

/-- The squared endpoint displacement is bounded by interval length times derivative energy.
Source: Lehto–Virtanen, Chapter I §4.3, pp.22–23, the Schwarz inequality step of
the inverse-canonical-map calculation for Rengel's inequality.

Proof: interior C¹ regularity bounds variation by the lower integral of derivative norm.
Each interior chord is bounded by this variation. Extend that inequality to each endpoint
by continuity on the closed interval and closedness of the order relation on extended
nonnegative reals. Apply Hölder with exponents two to the derivative norm and constant one,
then square. Extended nonnegative powers also handle infinite energy. The extension to
arbitrary continuous boundary values is the explicit agent-written justification of the
boundary step implicit in this source calculation; no endpoint differentiability is used. -/
theorem qc_rengel_interval_energy {a b : ℝ} {f : ℝ → ℂ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ContDiffOn ℝ 1 f (Ioo a b)) :
    edist (f a) (f b) ^ 2 ≤ ENNReal.ofReal (b - a) *
      ∫⁻ x in Ioo a b, ‖deriv f x‖ₑ ^ 2 := by
  have hc' : ContinuousOn f (closure (Ioo a b)) := by
    simpa only [closure_Ioo hab.ne] using hc
  have ha : a ∈ closure (Ioo a b) := by
    simp only [closure_Ioo hab.ne, mem_Icc, le_refl, hab.le, and_self]
  have hb : b ∈ closure (Ioo a b) := by
    simp only [closure_Ioo hab.ne, mem_Icc, le_refl, hab.le, and_self]
  have hi (x : ℝ) (hx : x ∈ Ioo a b) (y : ℝ) (hy : y ∈ Ioo a b) :
      edist (f x) (f y) ≤ ∫⁻ t in Ioo a b, ‖deriv f t‖ₑ :=
    (eVariationOn.edist_le f hx hy).trans
      (Analysis.eVariationOn_Ioo_le_lintegral_deriv_of_contDiffOn hd)
  have hleft (y : ℝ) (hy : y ∈ Ioo a b) :
      edist (f a) (f y) ≤ ∫⁻ t in Ioo a b, ‖deriv f t‖ₑ :=
    le_on_closure (fun x hx ↦ hi x hx y hy)
      (continuous_edist.comp_continuousOn (hc'.prodMk continuousOn_const))
      continuousOn_const ha
  have hend : edist (f a) (f b) ≤ ∫⁻ t in Ioo a b, ‖deriv f t‖ₑ :=
    le_on_closure hleft
      (continuous_edist.comp_continuousOn (continuousOn_const.prodMk hc'))
      continuousOn_const hb
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (Ioo a b)) (Real.holderConjugate_iff.mpr (by norm_num :
      (1 : ℝ) < 2 ∧ (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1))
    ((measurable_deriv f).enorm.aemeasurable :
      AEMeasurable (fun x ↦ ‖deriv f x‖ₑ) (volume.restrict (Ioo a b)))
    (aemeasurable_const : AEMeasurable (fun _ : ℝ ↦ (1 : ℝ≥0∞))
      (volume.restrict (Ioo a b)))
  simp only [Pi.mul_apply, mul_one, ENNReal.rpow_two, one_pow, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Ioo, one_mul] at hholder
  have hsquare := pow_le_pow_left' (hend.trans hholder) 2
  rw [mul_comm]
  simpa only [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    show (1 : ℝ) / 2 * 2 = 1 by norm_num, ENNReal.rpow_one] using hsquare


end HolomorphicAnosov
