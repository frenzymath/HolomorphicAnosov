import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLM
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLMApply
import Mathlib.Analysis.Distribution.TestFunction

/-!
# coordPullbackCLM_lineDeriv

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_coord_pullback_c_l_m_line_deriv_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
For a real linear coordinate equivalence between Banach spaces, directional differentiation of a
pulled-back test in direction v equals pullback of its derivative in direction e(v).

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Use test-function extensionality. Rewrite the directional derivatives as
Frechet derivatives of smooth tests. The native linear chain rule comp_right_fderiv inserts e into
the derivative, giving the stated coordinate direction.
-/
theorem coordPullbackCLM_lineDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (e : E ≃L[ℝ] F) (U : Opens F) (v : E) (φ : TestFunction U ℂ ⊤) :
    (TestFunction.lineDerivCLM ℂ v (coordPullbackCLM e U φ) :
      TestFunction (coordDomain e U) ℂ ⊤) =
    coordPullbackCLM e U (TestFunction.lineDerivCLM ℂ (e v) φ) := by
  ext x
  simp only [TestFunction.lineDerivCLM_apply, le_top, ↓reduceIte,
    coordPullbackCLM_apply]
  rw [((coordPullbackCLM e U φ).contDiff.differentiable
    (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  change (fderiv ℝ ((φ : F → ℂ) ∘ e) x) v = _
  rw [e.comp_right_fderiv]
  rfl


end HolomorphicAnosov.Analysis.Distribution
