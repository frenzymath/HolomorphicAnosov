import Mathlib.MeasureTheory.Function.L2Space

/-!
# The finite-area length–energy inequality

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed p.342, the Cauchy–Schwarz inequality in the
length–area chain. This version discharges the integrability prerequisite
from finite nonnegative quadratic energy and finite source measure.
-/

open MeasureTheory
open scoped ENNReal

namespace HolomorphicAnosov.Analysis.Measure

/-- A nonnegative measurable density with finite quadratic lower integral on a
finite measure space is integrable, and its squared integral is bounded by the
source mass times its quadratic energy.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, printed p.342.
For the rectangle application, the density is the complex derivative norm and
the measure is planar volume restricted to the source rectangle.

Proof: Nonnegativity of the square and finite quadratic lower integral imply
Bochner integrability of the square. Thus the density belongs to L². Since the
measure is finite, it belongs to L¹ as well. Apply Hölder with exponents two and
two to the density and the constant function one. This bounds the integral by
the product of the square roots of the quadratic integral and total mass.
Both sides are nonnegative, so square the inequality. The nonnegative Bochner
quadratic integral equals the real value of the given lower integral.
-/
theorem integrable_and_integral_sq_le_mass_mul_energy
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (hnonneg : 0 ≤ᵐ[μ] f)
    (henergy : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ≠ ⊤) :
    Integrable f μ ∧
      (∫ x, f x ∂μ) ^ 2 ≤ (μ Set.univ).toReal *
        (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ).toReal := by
  have hsqmeas : AEStronglyMeasurable (fun x ↦ f x ^ 2) μ := hf.pow 2
  have hsqnonneg : 0 ≤ᵐ[μ] fun x ↦ f x ^ 2 := Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  have hsqint : Integrable (fun x ↦ f x ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hsqmeas hsqnonneg).mp henergy
  have hL2 : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf).mpr hsqint
  refine ⟨hL2.integrable (by norm_num), ?_⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hnonneg (Filter.Eventually.of_forall fun _ ↦ (show (0 : ℝ) ≤ 1 by norm_num))
    (by simpa using hL2) (memLp_const (1 : ℝ) : MemLp (fun _ : α ↦ (1 : ℝ)) (ENNReal.ofReal 2) μ)
  have hb : (∫ x, f x ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (μ Set.univ).toReal := by
    simpa only [mul_one, Real.rpow_two, Real.one_rpow, integral_const, smul_eq_mul,
      mul_one, one_pow, MeasureTheory.measureReal_def, ← Real.sqrt_eq_rpow] using hh
  have hpos : 0 ≤ ∫ x, f x ∂μ := integral_nonneg_of_ae hnonneg
  have hsqpos : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg_of_ae hsqnonneg
  have hbound := mul_self_le_mul_self hpos hb
  rw [← pow_two, ← pow_two, mul_pow, Real.sq_sqrt hsqpos,
    Real.sq_sqrt ENNReal.toReal_nonneg] at hbound
  rw [integral_eq_lintegral_of_nonneg_ae hsqnonneg hsqmeas] at hbound
  simpa only [mul_comm] using hbound

end HolomorphicAnosov.Analysis.Measure

