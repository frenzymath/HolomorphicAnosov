import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ScaledKernelFDerivNeg
import Mathlib.Analysis.Distribution.TestFunction

/-!
# scaled_kernel_neg_test_derivative

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, Theorem6.4, p.69,
derivative sign for a translated convolution kernel; Proposition6.3, pp.68–69, differentiation of
a fixed-support family.
DAG node: `analysis.dbar_helper_scaled_kernel_neg_test_derivative_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
A scaled translated mollifier represented as a native test has parameter derivative equal to minus
the spatial directional derivative of that test.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, Theorem6.4, p.69,
derivative sign for a translated convolution kernel; Proposition6.3, pp.68–69, differentiation of
a fixed-support family.

Proof/construction: Use the proved scaled-kernel affine sign identity. Replace the explicit
spatial kernel by the underlying test function using its pointwise equality. Rewrite the native
test directional derivative as the Frechet derivative of its smooth underlying function.
-/
theorem scaled_kernel_neg_test_derivative {m : ℕ}
    (U : Opens (EuclideanSpace ℝ (Fin m)))
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin m))
    (κ : TestFunction U ℂ ⊤)
    (hκ : ∀ y, κ y = (((ε⁻¹)^m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (x-y)) : ℝ) : ℂ)) (y v : EuclideanSpace ℝ (Fin m)) :
    (fderiv ℝ (fun p ↦ (((ε⁻¹)^m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (p-y)) : ℝ) : ℂ)) x) v =
      -(TestFunction.lineDerivCLM ℂ v κ : TestFunction U ℂ ⊤) y := by
  rw [scaled_kernel_fderiv_neg]
  have heq : (κ : EuclideanSpace ℝ (Fin m) → ℂ) =
      (fun q ↦ (((ε⁻¹)^m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (x-q)) : ℝ) : ℂ)) := funext hκ
  rw [← heq]
  simp only [TestFunction.lineDerivCLM_apply, le_top, ↓reduceIte]
  rw [(κ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv]


end HolomorphicAnosov.Analysis.Distribution
