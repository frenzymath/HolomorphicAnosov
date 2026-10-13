import HolomorphicAnosov.Analysis.Measure.LengthEnergyBound
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Forward and inverse length–area equality for unequal rectangle heights

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed pp.342–343. These are the conformal forward and
inverse length–area inequalities before normalizing either rectangle's height.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HolomorphicAnosov.Analysis.Measure

/-- Forward and inverse rectangle energy identities and slice lower bounds force
equal aspect ratios and almost-everywhere equality of both slice bounds.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, pp.342–343,
Cauchy–Schwarz, integrated horizontal length, and the K=1 equality argument.
This keeps the original side lengths instead of normalizing the heights.

Proof: Write S and R for the total integrals of f and g. Finite energy on finite
product measures makes both densities integrable. Cauchy–Schwarz gives
S²≤abAB and R²≤ABab. Fubini and the slice lower bounds give S≥Ab and R≥aB.
Squaring these nonnegative lower bounds and canceling the positive factors Ab
and aB gives Ab≤aB and aB≤Ab. Hence aB=Ab. The squared upper bounds now give
S=Ab and R=aB. Each integrable slice-length function dominates its constant
lower bound and has the same integral; equality in integral monotonicity makes
both slice bounds equalities almost everywhere.
-/
theorem aspect_eq_and_ae_slice_integral_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ κ : MeasureTheory.Measure α} {ν ρ : MeasureTheory.Measure β}
    [IsFiniteMeasure μ] [IsFiniteMeasure κ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (hμ : (μ univ).toReal = a) (hν : (ν univ).toReal = b)
    (hκ : (κ univ).toReal = A) (hρ : (ρ univ).toReal = B)
    {f g : α × β → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hg : AEStronglyMeasurable g (κ.prod ρ))
    (hfn : 0 ≤ᵐ[μ.prod ν] f) (hgn : 0 ≤ᵐ[κ.prod ρ] g)
    (hfe : (∫⁻ p, ENNReal.ofReal (f p ^ 2) ∂μ.prod ν) = ENNReal.ofReal (A * B))
    (hge : (∫⁻ p, ENNReal.ofReal (g p ^ 2) ∂κ.prod ρ) = ENNReal.ofReal (a * b))
    (hfl : ∀ᵐ y ∂ν, A ≤ ∫ x, f (x, y) ∂μ)
    (hgl : ∀ᵐ y ∂ρ, a ≤ ∫ x, g (x, y) ∂κ) :
    a * B = A * b ∧
      (∀ᵐ y ∂ν, (∫ x, f (x, y) ∂μ) = A) ∧
      (∀ᵐ y ∂ρ, (∫ x, g (x, y) ∂κ) = a) := by
  have hμprod : (μ.prod ν univ).toReal = a * b := by
    rw [← univ_prod_univ, MeasureTheory.Measure.prod_prod, ENNReal.toReal_mul, hμ, hν]
  have hκprod : (κ.prod ρ univ).toReal = A * B := by
    rw [← univ_prod_univ, MeasureTheory.Measure.prod_prod, ENNReal.toReal_mul, hκ, hρ]
  obtain ⟨hfi, hfb⟩ := integrable_and_integral_sq_le_mass_mul_energy hf hfn
    (by rw [hfe]; exact ENNReal.ofReal_ne_top)
  obtain ⟨hgi, hgb⟩ := integrable_and_integral_sq_le_mass_mul_energy hg hgn
    (by rw [hge]; exact ENNReal.ofReal_ne_top)
  rw [hμprod, hfe, ENNReal.toReal_ofReal (mul_pos hA hB).le] at hfb
  rw [hκprod, hge, ENNReal.toReal_ofReal (mul_pos ha hb).le] at hgb
  have hfmin : A * b ≤ ∫ p, f p ∂μ.prod ν := by
    rw [integral_prod_symm f hfi]
    simpa [integral_const, measureReal_def, hν, smul_eq_mul, mul_comm] using
      integral_mono_ae (integrable_const A) hfi.integral_prod_right hfl
  have hgmin : a * B ≤ ∫ p, g p ∂κ.prod ρ := by
    rw [integral_prod_symm g hgi]
    simpa [integral_const, measureReal_def, hρ, smul_eq_mul, mul_comm] using
      integral_mono_ae (integrable_const a) hgi.integral_prod_right hgl
  have hle : A * b ≤ a * B := by
    have hh := mul_self_le_mul_self (mul_pos hA hb).le hfmin
    apply (mul_le_mul_iff_right₀ (mul_pos hA hb)).mp
    nlinarith
  have hge' : a * B ≤ A * b := by
    have hh := mul_self_le_mul_self (mul_pos ha hB).le hgmin
    apply (mul_le_mul_iff_right₀ (mul_pos ha hB)).mp
    nlinarith
  have heq : a * B = A * b := le_antisymm hge' hle
  have hprod : a * b * (A * B) = (A * b) ^ 2 := by
    calc
      a * b * (A * B) = (a * B) * (A * b) := by ring
      _ = (A * b) ^ 2 := by rw [heq]; ring
  have hftotal : (∫ p, f p ∂μ.prod ν) = A * b := by
    rw [hprod] at hfb
    nlinarith [mul_pos hA hb]
  have hgtotal : (∫ p, g p ∂κ.prod ρ) = a * B := by
    rw [mul_comm (A * B) (a * b), hprod, ← heq] at hgb
    nlinarith [mul_pos ha hB]
  refine ⟨heq, ?_, ?_⟩
  · have hconst : (fun _ : β ↦ A) =ᵐ[ν] (fun y ↦ ∫ x, f (x, y) ∂μ) := by
      apply (integral_eq_iff_of_ae_le (integrable_const A) hfi.integral_prod_right hfl).mp
      rw [← integral_prod_symm f hfi, hftotal]
      simp [integral_const, measureReal_def, hν, smul_eq_mul, mul_comm]
    exact hconst.symm
  · have hconst : (fun _ : β ↦ a) =ᵐ[ρ] (fun y ↦ ∫ x, g (x, y) ∂κ) := by
      apply (integral_eq_iff_of_ae_le (integrable_const a) hgi.integral_prod_right hgl).mp
      rw [← integral_prod_symm g hgi, hgtotal]
      simp [integral_const, measureReal_def, hρ, smul_eq_mul, mul_comm]
    exact hconst.symm

end HolomorphicAnosov.Analysis.Measure

