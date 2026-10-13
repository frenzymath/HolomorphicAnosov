import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ContinuousCoefficientHolomorphic

open scoped Topology _root_.Topology
open Filter MeasureTheory TopologicalSpace Set
noncomputable section
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates

/-- A continuous coefficient whose distributional `dbarPairing` vanishes in every coordinate
direction is holomorphic. -/
theorem continuous_coefficient_holomorphic_of_dbarPairing {n : ℕ}
    (Ω : Opens (Fin n → ℂ)) (a : (Fin n → ℂ) → ℂ) (ha : ContinuousOn a Ω)
    (hclosed : ∀ (j : Fin n) (φ : TestFunction Ω ℂ ⊤),
      DistributionalSection.dbarPairing Ω a j φ = 0) :
    DifferentiableOn ℂ a (Ω : Set (Fin n → ℂ)) := by
  have hali := ha.locallyIntegrableOn Ω.isOpen.measurableSet (μ := volume)
  let T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ :=
    TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) volume a
  have hT (φ : TestFunction Ω ℂ ⊤) :
      T φ = ∫ z in (Ω : Set (Fin n → ℂ)), a z * φ z ∂volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz ↦ by simp [φ.zero_on_compl hz])]
    rw [show (fun z ↦ a z * φ z) = (fun z ↦ φ z * a z) by
      funext z; exact mul_comm _ _]
    exact TestFunction.integralAgainstBilinCLM_eq_integral hali
  exact continuous_coefficient_holomorphic_of_current Ω a ha T hT
    (fun j φ ↦ by simpa only [hT, DistributionalSection.dbarPairing,
      DistributionalSection.regularPairing] using hclosed j φ)

end ConnectionFlatEstimates
end HolomorphicAnosov
