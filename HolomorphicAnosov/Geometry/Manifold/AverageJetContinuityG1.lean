import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Continuity of spatial jets obtained by parameter integration. (Bochner–Montgomery, equation (13).) -/

open scoped Interval Topology _root_.Topology
open MeasureTheory Set Filter

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [TopologicalSpace E] [FirstCountableTopology E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

/-- Dominated continuity of an interval integral in its spatial parameter. -/
theorem average_jet_continuous_g1
    (G : E → ℝ → F) (a b : ℝ)
    (hmeas : ∀ x, AEStronglyMeasurable (G x) <| μ.restrict <| Ι a b)
    (hbound : ∀ x, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖G x t‖ ≤ (1 : ℝ))
    (hcont : ∀ᵐ t ∂μ, t ∈ Ι a b → Continuous (fun x ↦ G x t)) :
    Continuous (fun x ↦ ∫ t in a..b, G x t ∂μ) := by
  apply intervalIntegral.continuous_of_dominated_interval hmeas hbound
  · exact intervalIntegrable_const
  · exact hcont

end HolomorphicAnosov

