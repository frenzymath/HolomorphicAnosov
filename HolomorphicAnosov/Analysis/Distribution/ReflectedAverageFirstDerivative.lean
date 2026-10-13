import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology
namespace HolomorphicAnosov.Analysis.Distribution

/-- Differentiating a compactly weighted translated average differentiates its second factor.

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), proof of Theorem 6.7,
p.73, translated-average formula following (6.25). This is its first derivative step,
with a real Banach target. The statement includes every real scale, including zero.

Proof: continuity and compact support of the kernel make the integrands integrable.
The continuous derivative of the compactly supported function is bounded globally
by a constant C. Thus the derivative integrand is dominated by ‖ρ(z)‖ C, an integrable
function. The chain rule for translation and dominated differentiation give the result. -/
theorem hasFDerivAt_reflected_average
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (ε : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (fun y ↦ ∫ z, ρ z • f (y + ε • z))
      (∫ z, ρ z • fderiv ℝ f (y + ε • z)) y := by
  have hdf := hf.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hdf.bounded_above_of_compact_support (hc.fderiv ℝ)
  have hint (y) : Integrable (fun z ↦ ρ z • f (y + ε • z)) volume :=
    (ρ.continuous.smul (hf.continuous.comp
      (continuous_const.add (continuous_id.const_smul ε)))).integrable_of_hasCompactSupport
      (ρ.hasCompactSupport.smul_right (f' := fun z ↦ f (y + ε • z)))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y z ↦ ρ z • f (y + ε • z))
    (F' := fun y z ↦ ρ z • fderiv ℝ f (y + ε • z))
    (s := univ) (bound := fun z ↦ ‖ρ z‖ * C) Filter.univ_mem
  · exact Filter.Eventually.of_forall (fun y ↦ (hint y).aestronglyMeasurable)
  · exact hint y
  · exact (ρ.continuous.smul (hdf.comp
      (continuous_const.add (continuous_id.const_smul ε)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z y _ ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  · exact (ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport).norm.mul_const C
  · exact Filter.Eventually.of_forall (fun z y _ ↦ by
      simpa [Function.comp_def, Pi.smul_apply] using! (((hf.differentiable (by simp) (y + ε • z)).hasFDerivAt).comp y
        ((hasFDerivAt_id y).add_const (ε • z))).const_smul (ρ z))
end HolomorphicAnosov.Analysis.Distribution
