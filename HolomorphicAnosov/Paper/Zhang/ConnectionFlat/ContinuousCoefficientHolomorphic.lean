import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ContinuousCoefficientsEqOn

open scoped Topology _root_.Topology
open Filter MeasureTheory TopologicalSpace Set
noncomputable section
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates

/-- A continuous coefficient representing a current with vanishing antiholomorphic derivatives is
holomorphic. -/
theorem continuous_coefficient_holomorphic_of_current {n : ℕ}
    (Ω : Opens (Fin n → ℂ)) (a : (Fin n → ℂ) → ℂ) (ha : ContinuousOn a Ω)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hregular : ∀ φ : TestFunction Ω ℂ ⊤,
      T φ = ∫ z in (Ω : Set (Fin n → ℂ)), a z * φ z ∂volume)
    (hclosed : ∀ (j : Fin n) (φ : TestFunction Ω ℂ ⊤),
      -T ((2 : ℂ)⁻¹ •
        ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ : TestFunction Ω ℂ ⊤) +
          Complex.I • (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ :
            TestFunction Ω ℂ ⊤))) = 0) :
    DifferentiableOn ℂ a (Ω : Set (Fin n → ℂ)) := by
  intro z hz
  by_cases hn : n = 0
  · subst n
    have heq : a = fun _ ↦ a z := funext fun y ↦ congrArg a (Subsingleton.elim y z)
    rw [heq]
    exact differentiableWithinAt_const _
  obtain ⟨V, hzV, hVΩ, h, hhol, hrep⟩ :=
    dbar_closed_scalar_current_holomorphic (Nat.one_le_iff_ne_zero.mpr hn) Ω T hclosed z hz
  have heq := continuous_coefficients_eqOn_of_current Ω V hVΩ a h
    (ha.mono hVΩ) hhol.continuousOn T hregular hrep
  have hevent : a =ᶠ[𝓝 z] h :=
    Filter.eventually_of_mem (V.isOpen.mem_nhds hzV) (fun y hy ↦ heq hy)
  exact ((hhol.differentiableAt (V.isOpen.mem_nhds hzV)).congr_of_eventuallyEq
    hevent).differentiableWithinAt

end ConnectionFlatEstimates
end HolomorphicAnosov
