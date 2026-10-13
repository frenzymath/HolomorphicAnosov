import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTest
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTestApply

/-!
# Every antiholomorphic partial derivative of a smooth compactly supported test cutoff is smooth, and its closed support is contained in the closed support of the cutoff.

Source: Demailly, Complex Analytic and Differential Geometry (2012), I §3.E (3.29), p.28: the
smooth compactly supported coefficient dbar psi in the cutoff kernel; I §3.A (3.1), p.20.
DAG node: `analysis.dbar_helper_cutoff_dbar_smooth_support_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology BigOperators

namespace HolomorphicAnosov.Analysis

/--
Every antiholomorphic partial derivative of a smooth compactly supported test cutoff is smooth,
and its closed support is contained in the closed support of the cutoff.

Source: Demailly (2012), I §3.E (3.29), p.28: the smooth compactly supported coefficient dbar psi
in the cutoff kernel; I §3.A (3.1), p.20.

Proof: The published scalar test-derivative identity identifies the coefficient with a bundled
smooth test, giving its smoothness. Outside the cutoff support, the cutoff vanishes on a
neighborhood, so its derivative is zero. Thus the nonzero set of the derivative lies in the closed
cutoff support, and taking the closure proves the support inclusion.
-/
theorem cutoff_dbar_smooth_support {n : ℕ} (U : Opens (Fin n → ℂ))
    (ψ : TestFunction U ℂ ⊤) (j : Fin n) :
    ContDiff ℝ ∞ (antiholomorphicPartial ψ j) ∧
      tsupport (antiholomorphicPartial ψ j) ⊆ tsupport (ψ : (Fin n → ℂ) → ℂ) := by
  constructor
  · have heq : antiholomorphicPartial ψ j =
        (HolomorphicAnosov.scalarDbarTest U j ψ : (Fin n → ℂ) → ℂ) := by
      funext x
      exact (HolomorphicAnosov.scalarDbarTest_apply U j ψ x).symm
    rw [heq]
    exact (HolomorphicAnosov.scalarDbarTest U j ψ).contDiff
  · apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hnot
    have hz := fderiv_of_notMem_tsupport ℝ hnot
    exact hx (by simp [antiholomorphicPartial, hz])


end HolomorphicAnosov.Analysis
