import HolomorphicAnosov.Geometry.Manifold.AverageJetRegularityG1

/-! Differentiability supplied by the averaged spatial-jet identities. (Bochner–Montgomery, equation (13).) -/

open scoped ContDiff
open Set

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A derivative certificate for each iterated spatial jet supplies the `DifferentiableOn` half of the infinite-order `ContDiffOn` criterion. -/
theorem average_jet_differentiableOn_g1
    (S : Set E) (f : E → F)
    (haverage : ∀ m : ℕ, ∀ y ∈ S,
      ∃ D : E →L[ℝ] (E [×m]→L[ℝ] F), HasFDerivAt (iteratedFDerivWithin ℝ m f S) D y) :
    ∀ m : ℕ, DifferentiableOn ℝ (iteratedFDerivWithin ℝ m f S) S := by
  intro m y hy
  rcases haverage m y hy with ⟨D, hD⟩
  exact hD.differentiableAt.differentiableWithinAt

/-- Combining continuity of all averaged jets with their `HasFDerivAt` certificates gives smoothness on a uniquely differentiable chart set. -/
theorem average_jet_smooth_of_derivatives_g1
    (S : Set E) (f : E → F) (hS : UniqueDiffOn ℝ S)
    (hcont : ∀ m : ℕ, ContinuousOn (iteratedFDerivWithin ℝ m f S) S)
    (haverage : ∀ m : ℕ, ∀ y ∈ S,
      ∃ D : E →L[ℝ] (E [×m]→L[ℝ] F), HasFDerivAt (iteratedFDerivWithin ℝ m f S) D y) :
    ContDiffOn ℝ ∞ f S := by
  apply average_jet_regular_contDiffOn_g1 S f hS hcont
  exact average_jet_differentiableOn_g1 S f haverage

end HolomorphicAnosov

