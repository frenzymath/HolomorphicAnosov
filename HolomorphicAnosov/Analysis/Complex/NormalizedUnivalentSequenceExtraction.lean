import HolomorphicAnosov.Analysis.Complex.NormalizedUnivalentSequenceCore
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence

namespace HolomorphicAnosov

/-- Public wrapper for Lyubich's normalized-univalent normal-family interface. -/
theorem normalized_univalent_sequence_extraction
    (ext : C(Complex.UnitDisc, ℂ) → ℂ → ℂ)
    (hext : ∀ f (z : Complex.UnitDisc), ext f z = f z)
    (u : ℕ → C(Complex.UnitDisc, ℂ))
    (hu : ∀ n,
      DifferentiableOn ℂ (ext (u n)) (Metric.ball (0 : ℂ) 1) ∧
      Function.Injective (u n) ∧ (u n) 0 = 0 ∧
      ‖deriv (ext (u n)) 0‖ = 1) :
    ∃ v : C(Complex.UnitDisc, ℂ),
      DifferentiableOn ℂ (ext v) (Metric.ball (0 : ℂ) 1) ∧
      Function.Injective v ∧ v 0 = 0 ∧ ‖deriv (ext v) 0‖ = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ K : Set Complex.UnitDisc, IsCompact K →
          TendstoUniformlyOn (fun n z ↦ u (φ n) z) v Filter.atTop K := by
  exact normalized_univalent_sequence_extraction_core ext hext u
    (fun n ↦ (hu n).1)
    (fun n ↦ (hu n).2.1)
    (fun n ↦ (hu n).2.2.1)
    (fun n ↦ (hu n).2.2.2)

end HolomorphicAnosov

