import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform parameter Taylor remainder on compact fixed-support cores

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Proposition 6.3,
pp. 68–69, equation (6.8), together with the compact-uniform continuity and
convex segment estimates in Mathlib.  This is the finite-dimensional modulus
step used before applying a fixed-support distribution's finite-order bound.
-/

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology _root_.Topology
namespace HolomorphicAnosov.Analysis

/-- A jointly continuous parameter derivative gives a uniform first-order Taylor
remainder on a compact convex parameter core, uniformly over a compact spatial
core.  The conclusion is stated with the actual parameter derivative, so it can
be fed directly to a norm remainder criterion for a distribution pairing. -/
theorem uniform_parameter_taylor_remainder
    {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → X → F) (Q : Set E) (K : Set X)
    (hQ : IsCompact Q) (hK : IsCompact K) (hconv : Convex ℝ Q)
    (hdiff : ∀ q ∈ Q, ∀ y ∈ K, DifferentiableAt ℝ (fun r ↦ f r y) q)
    (hA : ContinuousOn
      (fun z : E × X ↦ fderiv ℝ (fun r ↦ f r z.2) z.1) (Q ×ˢ K)) :
    ∀ ε > 0, ∃ δ > 0, ∀ q ∈ Q, ∀ r ∈ Q, ∀ y ∈ K, dist r q < δ →
      ‖f r y - f q y - fderiv ℝ (fun t ↦ f t y) q (r - q)‖ ≤ ε * ‖r - q‖ := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((hQ.prod hK).uniformContinuousOn_of_continuous hA) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro q hq r hr y hy hdist
  have hseg : segment ℝ q r ⊆ Q := hconv.segment_subset hq hr
  have hball : segment ℝ q r ⊆ Metric.ball q δ :=
    (convex_ball q δ).segment_subset (by simpa using hδ) hdist
  apply (convex_segment q r).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz ↦ hdiff z (hseg hz) y hy) _
    (left_mem_segment ℝ q r) (right_mem_segment ℝ q r)
  intro z hz
  exact le_of_lt (by simpa only [dist_eq_norm] using
    (hclose (z, y) ⟨hseg hz, hy⟩ (q, y) ⟨hq, hy⟩
      (by simpa [Prod.dist_eq] using hball hz)))

end HolomorphicAnosov.Analysis

