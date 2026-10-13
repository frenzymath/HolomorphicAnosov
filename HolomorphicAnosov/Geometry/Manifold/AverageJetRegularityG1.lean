import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Smoothness from continuity and differentiability of the averaged spatial-jet ladder. (Bochner–Montgomery, equation (13).) -/

open scoped ContDiff
open Set

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuous/differentiable iterated-jet ladder implies smoothness on a uniquely differentiable chart set. -/
theorem average_jet_regular_contDiffOn_g1
    (S : Set E) (f : E → F) (hS : UniqueDiffOn ℝ S)
    (hcont : ∀ m : ℕ, ContinuousOn (iteratedFDerivWithin ℝ m f S) S)
    (hdiff : ∀ m : ℕ, DifferentiableOn ℝ (iteratedFDerivWithin ℝ m f S) S) :
    ContDiffOn ℝ ∞ f S := by
  exact (contDiffOn_iff_continuousOn_differentiableOn hS).2
    ⟨fun m _ ↦ hcont m, fun m _ ↦ hdiff m⟩

end HolomorphicAnosov

