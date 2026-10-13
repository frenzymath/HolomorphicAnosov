import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral

/-!
# Reflected mollifier change of variables

Source: Dyatlov, *Lecture notes for 18.155*, proof of Theorem 6.7,
printed p.73, the change of variables following equation (6.25).
-/

open MeasureTheory

namespace HolomorphicAnosov.Analysis.Distribution

/-- A positive dilation and translation turn a reflected Euclidean kernel
into its weighted average. No regularity, integrability or symmetry assumptions
are needed, using the Bochner integral's zero value for nonintegrable functions.

Source: Dyatlov, proof of Theorem 6.7, p.73, after equation (6.25).
Proof: substitute `p = y + ε • z` in the original integral. Translation
preserves volume and positive dilation scales volume by `ε ^ m`; this cancels
the kernel's factor `(ε⁻¹) ^ m`. -/
theorem reflected_mollifier_change_variables
    {m : ℕ} (ρ : EuclideanSpace ℝ (Fin m) → ℝ)
    (φ : EuclideanSpace ℝ (Fin m) → ℂ) {ε : ℝ} (hε : 0 < ε)
    (y : EuclideanSpace ℝ (Fin m)) :
    (∫ p, φ p * ((((ε⁻¹) ^ m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ))) =
      ∫ z, ρ z • φ (y + ε • z) := by
  let f : EuclideanSpace ℝ (Fin m) → ℂ := fun p =>
    φ p * ((((ε⁻¹) ^ m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ))
  have ht := integral_add_left_eq_self (μ := volume) f y
  have hs := Measure.integral_comp_smul_of_nonneg volume (fun x => f (y + x)) ε
    (hR := hε.le)
  have heq : (∫ z, f (y + ε • z)) =
      (ε⁻¹) ^ m • ∫ z, ρ z • φ (y + ε • z) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp [f, smul_smul, hε.ne', Complex.real_smul, mul_comm, mul_left_comm]
  rw [heq, ht] at hs
  have hs' : (ε⁻¹) ^ m • (∫ z, ρ z • φ (y + ε • z)) =
      (ε⁻¹) ^ m • (∫ p, f p) := by
    simpa [inv_pow] using hs
  have hc := congrArg (fun w : ℂ => ε ^ m • w) hs'
  simpa [smul_smul, ← mul_pow, hε.ne', f] using hc.symm

end HolomorphicAnosov.Analysis.Distribution

