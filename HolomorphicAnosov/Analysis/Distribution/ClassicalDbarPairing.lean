import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import HolomorphicAnosov.Analysis.Distribution.LocalDirectionalIntegrationByParts
import HolomorphicAnosov.Analysis.Distribution.LocalAntiholomorphicIntegrationByParts

/-!
# Agreement of classical and distributional antiholomorphic derivatives

Source: Demailly, Complex Analytic and Differential Geometry, Chapter I §2.B.1,
equation (2.6) and the following Stokes argument, printed p.15; Zhang,
Codimension-one holomorphic Anosov diffeomorphisms, Lemma 4.1, printed pp.13–14.
-/

open MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.DistributionalSection

/-- For a real-smooth coefficient on an open complex coordinate domain, the
unconjugated distributional ∂̄ pairing equals the classical derivative pairing.
Source: Demailly I §2.B.1, (2.6) and the identity dT_f = T_df immediately below,
p.15; Zhang Lemma 4.1, pp.13–14.

Proof: Apply the local directional integration-by-parts identity separately in
the real direction `Pi.single j 1` and the imaginary direction
`Pi.single j Complex.I`. Smoothness gives continuity and local integrability of
the coefficient and its directional derivatives on Ω. Each test and its derivative
has compact support inside Ω, so the products are integrable and their integrals
over Ω equal the ambient integrals. Expand the definition of `dbarPairing` and the
test directional derivatives. Integral linearity combines the two integration-by-parts
identities, cancels the leading minus signs, and factors out `(2 : ℂ)⁻¹` to obtain
the displayed `regularPairing`. Values outside Ω have no effect. If Ω is empty the
tests vanish; if d = 0 there is no coordinate direction j. -/
theorem classical_dbar_pairing {d : ℕ}
    (Ω : Opens (Fin d → ℂ)) (a : (Fin d → ℂ) → ℂ)
    (ha : ContDiffOn ℝ ∞ a Ω) (j : Fin d) (φ : TestFunction Ω ℂ ⊤) :
    dbarPairing Ω a j φ = regularPairing Ω
      (fun z ↦ (2 : ℂ)⁻¹ * (fderiv ℝ a z (Pi.single j 1) +
        Complex.I * fderiv ℝ a z (Pi.single j Complex.I))) φ := by
  let ψ : TestFunction Ω ℂ ⊤ := (2 : ℂ)⁻¹ •
    ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ : TestFunction Ω ℂ ⊤) +
      Complex.I • (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ :
        TestFunction Ω ℂ ⊤))
  have hsupport : (∫ z in (Ω : Set (Fin d → ℂ)), a z * ψ z) =
      ∫ z, a z * ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzψ : ψ z = 0 := ψ.zero_on_compl hz
    simp only [hzψ, mul_zero]
  have hanti := local_antiholomorphic_integration_by_parts Ω a ha j φ
  have hanti' : (∫ z, Analysis.antiholomorphicPartial a j z * φ z) =
      -(∫ z, a z * ψ z) := by
    simpa only [ψ, scalarDbarTest] using hanti
  unfold dbarPairing regularPairing
  change -(∫ z in (Ω : Set (Fin d → ℂ)), a z * ψ z) = _
  rw [hsupport, ← hanti']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z ↦ by
      dsimp [Analysis.antiholomorphicPartial]
      ring)
  · intro z hz
    have hzφ : φ z = 0 := φ.zero_on_compl hz
    simp only [hzφ, mul_zero]


end HolomorphicAnosov.DistributionalSection
