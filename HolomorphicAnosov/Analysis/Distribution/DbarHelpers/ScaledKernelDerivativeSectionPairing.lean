import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ScaledKernelNegTestDerivative
import Mathlib.Analysis.Distribution.TestFunction

/-!
# scaled_kernel_derivative_section_pairing

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, Theorem6.4, p.69,
derivative sign for a translated convolution kernel; Proposition6.3, pp.68–69, differentiation of
a fixed-support family.
DAG node: `analysis.dbar_helper_scaled_kernel_derivative_section_pairing_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
A test representing the parameter derivative section of a scaled translated kernel equals minus
the spatial derivative test, and its current pairing has the corresponding negative sign.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, Theorem6.4, p.69,
derivative sign for a translated convolution kernel; Proposition6.3, pp.68–69, differentiation of
a fixed-support family.

Proof/construction: Use test-function extensionality and the preceding pointwise derivative
identity to identify the two bundled tests. A complex-linear current maps their negative to the
negative pairing.
-/
theorem scaled_kernel_derivative_section_pairing {m : ℕ}
    (U : Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (ε : ℝ) (x v : EuclideanSpace ℝ (Fin m))
    (κ θ : TestFunction U ℂ ⊤)
    (hκ : ∀ y, κ y = (((ε⁻¹)^m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (x-y)) : ℝ) : ℂ))
    (hθ : ∀ y, θ y = (fderiv ℝ (fun p ↦ (((ε⁻¹)^m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (p-y)) : ℝ) : ℂ)) x) v) :
    θ = -(TestFunction.lineDerivCLM ℂ v κ : TestFunction U ℂ ⊤) ∧
      T θ = -T (TestFunction.lineDerivCLM ℂ v κ) := by
  have heq : θ = -(TestFunction.lineDerivCLM ℂ v κ : TestFunction U ℂ ⊤) := by
    ext y
    rw [hθ y, scaled_kernel_neg_test_derivative U ρ ε x κ hκ y v]
    rfl
  exact ⟨heq, by rw [heq, map_neg]⟩


end HolomorphicAnosov.Analysis.Distribution
