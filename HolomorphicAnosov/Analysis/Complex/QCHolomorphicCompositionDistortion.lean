import HolomorphicAnosov.Analysis.Complex.QCSimilarityDistortion
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Directional distortion under holomorphic coordinate changes

Source: Ghys, *Holomorphic Anosov systems* (1995), Proposition 2.2, p. 590,
the conformality of the leafwise iterates in `hₖ = φ⁻ᵏ πₖ φᵏ`; Lehto–Virtanen,
*Quasiconformal Mappings in the Plane* (1973), I §3.3, p. 17.
-/

namespace HolomorphicAnosov

/-- Holomorphic precomposition and postcomposition preserve a real derivative's directional
distortion bound at the corresponding point.

Source: Ghys Proposition 2.2, p. 590, and Lehto–Virtanen I §3.3, p. 17. Restrict the
complex derivatives of the outer and inner maps to real scalars. The real chain rule gives
the derivative `v ↦ a * A (b * v)`. The similarity distortion theorem applies to this
expression: normalize the input similarity by its positive norm, apply the unit-vector
bound for `A`, and multiply both sides by the output similarity's norm. If either
similarity is zero the derivative vanishes, so the same inequality holds.
-/
theorem qc_holomorphic_composition_distortion
    {pre f post : ℂ → ℂ} {z a b : ℂ} {A : ℂ →L[ℝ] ℂ} {K : ℝ}
    (hpre : HasDerivAt pre b z) (hf : HasFDerivAt f A (pre z))
    (hpost : HasDerivAt post a (f (pre z)))
    (hK : ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 → ‖A v‖ ≤ K * ‖A w‖) :
    ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (post ∘ f ∘ pre) z v‖ ≤
        K * ‖fderiv ℝ (post ∘ f ∘ pre) z w‖ := by
  have hcomp := (hpost.hasFDerivAt.restrictScalars ℝ).comp z
    (hf.comp z (hpre.hasFDerivAt.restrictScalars ℝ))
  intro v w hv hw
  rw [hcomp.fderiv]
  simpa [ContinuousLinearMap.comp_apply, mul_comm] using
    qc_similarity_distortion A hK a b hv hw

end HolomorphicAnosov

