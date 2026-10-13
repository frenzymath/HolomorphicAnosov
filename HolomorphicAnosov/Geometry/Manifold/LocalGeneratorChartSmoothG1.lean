import HolomorphicAnosov.Geometry.Manifold.LocalSmoothGeneratorFromAverageG1
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
The inverse-Jacobian expression for a local generator is smooth when the Jacobian and
displacement are smooth. (Bochner–Montgomery, Lemma 5)
-/

open scoped ContDiff
open Set

noncomputable section

namespace HolomorphicAnosov

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- If `B` is a smooth family of continuous linear equivalences and `u` is smooth on `S`, then `y ↦
(B y).symm (u y)` is smooth on `S`. -/
theorem local_generator_chart_smooth_g1
    (S : Set E) (B : E → E ≃L[ℝ] E) (u : E → E)
    (hB : ContDiffOn ℝ ∞ (fun y ↦ (B y).toContinuousLinearMap) S) (hu : ContDiffOn ℝ ∞ u S) :
    ContDiffOn ℝ ∞ (fun y ↦ (B y).symm (u y)) S := by
  have hinv : ContDiffOn ℝ ∞ (fun y ↦ (B y).symm.toContinuousLinearMap) S := by
    intro y hy
    have hi := (contDiffAt_map_inverse (n := ∞) (B y)).comp_contDiffWithinAt y (hB y hy)
    simpa only [Function.comp_def, ContinuousLinearMap.inverse_equiv] using hi
  exact hinv.clm_apply hu

end HolomorphicAnosov

