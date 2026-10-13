import Mathlib.Analysis.Distribution.TestFunction

/-!
# monoTest_lineDeriv

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_mono_test_line_deriv_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Inclusion of a compactly supported smooth test from an open subset into a larger open set commutes
with directional differentiation.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: The native inclusion of test spaces has the same underlying global smooth
function when the opens are nested. Evaluate the two bundled derivatives pointwise, expand the
native directional-derivative definition, and use that function equality.
-/
theorem monoTest_lineDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U V : Opens E) (hUV : U ≤ V) (v : E) (φ : TestFunction U ℂ ⊤) :
    (TestFunction.monoCLM ℂ (TestFunction.lineDerivCLM ℂ v φ : TestFunction U ℂ ⊤) : TestFunction V ℂ ⊤) =
      TestFunction.lineDerivCLM ℂ v (TestFunction.monoCLM ℂ φ : TestFunction V ℂ ⊤) := by
  ext x
  simp only [TestFunction.lineDerivCLM_apply, le_top, ↓reduceIte]
  have hφ : ((TestFunction.monoCLM ℂ φ : TestFunction V ℂ ⊤) : E → ℂ) = φ := by
    simp [TestFunction.monoCLM_apply, hUV]
  rw [hφ]
  simp [TestFunction.monoCLM_apply, hUV, TestFunction.lineDerivCLM_apply]


end HolomorphicAnosov.Analysis.Distribution
