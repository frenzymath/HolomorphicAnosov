import Mathlib.Analysis.Complex.RealDeriv

/-!
# Horizontal-line preservation forces real complex derivatives

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5, Theorem 11.10, printed p. 343, the K = 1 line-preservation conclusion.
The derivative argument below is an agent-written justification of its omitted
Cauchy–Riemann step, using Mathlib's real restriction and derivative chain rules.
-/

open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Complex

/-- A holomorphic function preserving horizontal lines has real derivative.
This is the Cauchy–Riemann consequence of horizontal line preservation in the K = 1
case of Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0, §11.5, p.343.
Restrict the function to the horizontal line through the point. Its imaginary part
is locally constant, so its real derivative, the imaginary part of the complex
derivative, is zero. -/
theorem deriv_im_eq_zero_of_horizontal_preservation {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hline : ∀ z ∈ U, ∀ w ∈ U, z.im = w.im → (f z).im = (f w).im) :
    ∀ z ∈ U, (deriv f z).im = 0 := by
  intro z hz
  have hd : HasDerivAt (fun w : ℂ ↦ f (w + z)) (deriv f z) 0 := by
    have hdz : HasDerivAt f (deriv f z) (0 + z) := by
      simpa using ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    simpa only [Function.comp_def, id_eq, mul_one] using
      hdz.comp 0 ((hasDerivAt_id (0 : ℂ)).add_const z)
  have hdr : HasDerivAt (fun t : ℝ ↦ (f ((t : ℂ) + z)).im) (deriv f z).im 0 := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd.comp_ofReal
  have heq : (fun t : ℝ ↦ (f ((t : ℂ) + z)).im) =ᶠ[𝓝 0] fun _ ↦ (f z).im := by
    have hm : ∀ᶠ t : ℝ in 𝓝 0, (t : ℂ) + z ∈ U :=
      ((Complex.continuous_ofReal.add continuous_const).continuousAt.tendsto
        (by simpa using hU.mem_nhds hz))
    filter_upwards [hm] with t ht
    exact hline _ ht z hz (by simp)
  exact hdr.unique ((hasDerivAt_const (0 : ℝ) (f z).im).congr_of_eventuallyEq heq)

end HolomorphicAnosov.Analysis.Complex

