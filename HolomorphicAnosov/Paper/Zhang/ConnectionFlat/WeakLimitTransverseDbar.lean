import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ClosedTransverseDbar
import HolomorphicAnosov.Paper.Zhang.ComplexManifold

open scoped Manifold ContDiff Topology _root_.Topology
open Filter MeasureTheory TopologicalSpace Set
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates
open scoped BigOperators

/-- A weak limit of transverse currents whose exterior derivative pairings tend to zero has
vanishing antiholomorphic derivatives in every direction. (Zhang, p. 7) -/
theorem weak_limit_transverse_current_dbar_zero {n : ℕ}
    (Ω : TopologicalSpace.Opens (Fin n → ℂ)) (j₀ : Fin n)
    (Tseq : ℕ → TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hweak : ∀ φ : TestFunction Ω ℂ ⊤,
      Filter.Tendsto (fun m ↦ Tseq m φ) Filter.atTop (nhds (T φ)))
    (hcurvature : ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤),
      Filter.Tendsto (fun m ↦
        -Tseq m (TestFunction.lineDerivCLM ℂ v φ) * w j₀ +
          Tseq m (TestFunction.lineDerivCLM ℂ w φ) * v j₀)
        Filter.atTop (nhds 0)) :
    ∀ (j : Fin n) (φ : TestFunction Ω ℂ ⊤),
      -T ((2 : ℂ)⁻¹ •
        ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ : TestFunction Ω ℂ ⊤) +
          Complex.I • (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ :
            TestFunction Ω ℂ ⊤))) = 0 := by
  apply closed_transverse_current_dbar_zero Ω j₀ T
  intro v w φ
  exact tendsto_nhds_unique
    (((hweak (TestFunction.lineDerivCLM ℂ v φ)).neg.mul_const (w j₀)).add
      ((hweak (TestFunction.lineDerivCLM ℂ w φ)).mul_const (v j₀)))
    (hcurvature v w φ)

end ConnectionFlatEstimates
end HolomorphicAnosov
