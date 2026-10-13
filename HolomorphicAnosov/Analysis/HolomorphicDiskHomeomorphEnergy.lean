import HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCrosscuts
import HolomorphicAnosov.Analysis.BoundedHolomorphicImageFiniteEnergy

open Set MeasureTheory Metric
open scoped ENNReal
open HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCrosscuts

namespace HolomorphicAnosov.Analysis

/-- A disk homeomorphism agreeing inside with a holomorphic map has a holomorphic total
representative and finite Dirichlet energy when its target is bounded. This is the finite-area
step in Tao, 246C Notes 2 (2018), Theorem 20 proof,
`literature/Tao-246C-Notes2-2018.txt:253–255`. The representative equals the given function on
the open disk, so differentiability transfers by equality there. Injectivity and surjectivity
are those of the homeomorphism, including their ambient subtype-value identities. Apply the
published injective-holomorphic bounded-image area bound to this representative. No boundary
regularity or assumption on the values of the holomorphic function outside the disk is used. -/
theorem diskExtension_eq_holomorphic_finite_energy
    {Q : Set ℂ} (hQbounded : Bornology.IsBounded Q)
    (e : (Metric.ball (0 : ℂ) 1) ≃ₜ Q) (φ : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1))
    (he : ∀ z : Metric.ball (0 : ℂ) 1, (e z : ℂ) = φ z) :
    EqOn (diskExtension e) φ (Metric.ball (0 : ℂ) 1) ∧
      DifferentiableOn ℂ (diskExtension e) (Metric.ball (0 : ℂ) 1) ∧
      (∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖deriv (diskExtension e) z‖ ^ 2) ∂volume) < ⊤ := by
  classical
  have heq : EqOn (diskExtension e) φ (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    simpa [diskExtension, hz] using he ⟨z, hz⟩
  have hde := hhol.congr (fun z hz ↦ heq hz)
  refine ⟨heq, hde, ?_⟩
  have hb : BijOn (diskExtension e) (Metric.ball (0 : ℂ) 1) Q := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      simp [diskExtension, hz]
    · intro a ha b hb heab
      have he' : e ⟨a, ha⟩ = e ⟨b, hb⟩ := by
        apply Subtype.ext
        simpa only [diskExtension, dite_eq_left ha, dite_eq_left hb] using heab
      exact congrArg Subtype.val (e.injective he')
    · intro q hq
      refine ⟨(e.symm ⟨q, hq⟩ : ℂ), (e.symm ⟨q, hq⟩).property, ?_⟩
      simp [diskExtension, (e.symm ⟨q, hq⟩).property]
  exact finite_energy_of_bijOn_bounded isOpen_ball hde hb hQbounded


end HolomorphicAnosov.Analysis
