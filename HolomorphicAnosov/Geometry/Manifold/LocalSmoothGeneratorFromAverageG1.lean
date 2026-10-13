import HolomorphicAnosov.Geometry.Manifold.LocalActionGeneratorFromAverage
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
A smooth family of invertible averaged derivatives yields a smooth coordinate generator for a
local action. (Bochner–Montgomery, Lemmas 2 and 5, pp. 688–689, 691)
-/

open scoped Topology _root_.Topology ContDiff
open MeasureTheory Filter

namespace HolomorphicAnosov

/-- A smooth family of invertible averaged derivatives on `S` gives a smooth coordinate generator
and the orbit derivative at zero for each point of `S`. (Bochner–Montgomery, Lemmas 2 and 5, pp.
688–689, 691) -/
theorem local_smooth_generator_from_average_g1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a : ℝ → E → E) (S : Set E) (h : ℝ) (B : E → E ≃L[ℝ] E)
    (hzero : ∀ y ∈ S, a 0 y = y)
    (hB : ContDiffOn ℝ ∞ (fun y ↦ (B y).toContinuousLinearMap) S)
    (hslice : ContDiffOn ℝ ∞ (a h) S)
    (hint : ∀ y ∈ S, IntervalIntegrable (fun t ↦ a t y) volume 0 h)
    (hmeas₀ : ∀ y ∈ S, StronglyMeasurableAtFilter (fun t ↦ a t y) (𝓝 0))
    (hmeasₕ : ∀ y ∈ S, StronglyMeasurableAtFilter (fun t ↦ a t y) (𝓝 h))
    (hcont₀ : ∀ y ∈ S, ContinuousAt (fun t ↦ a t y) 0)
    (hcontₕ : ∀ y ∈ S, ContinuousAt (fun t ↦ a t y) h)
    (haverage : ∀ y ∈ S, HasFDerivAt (fun z ↦ ∫ t in 0..h, a t z)
      (B y).toContinuousLinearMap y)
    (hcomp : ∀ y ∈ S, ∀ᶠ p in 𝓝 (0 : ℝ), ∀ t ∈ Set.uIcc 0 h,
      a t (a p y) = a (t + p) y) :
    ContDiffOn ℝ ∞ (fun y ↦ (B y).symm (a h y - y)) S ∧
      ∀ y ∈ S, HasDerivAt (fun p ↦ a p y) ((B y).symm (a h y - y)) 0 := by
  have hinv : ContDiffOn ℝ ∞ (fun y ↦ (B y).symm.toContinuousLinearMap) S := by
    intro y hy
    have hi := (contDiffAt_map_inverse (n := ∞) (B y)).comp_contDiffWithinAt y (hB y hy)
    simpa only [Function.comp_def, ContinuousLinearMap.inverse_equiv] using hi
  refine ⟨hinv.clm_apply (hslice.sub contDiffOn_id), ?_⟩
  intro y hy
  have havg : HasFDerivAt (fun z ↦ ∫ t in 0..h, a t z)
      (B y).toContinuousLinearMap (a 0 y) := by
    simpa only [hzero y hy] using haverage y hy
  simpa only [hzero y hy] using local_action_generator_from_average a y h
    (hint y hy) (hmeas₀ y hy) (hmeasₕ y hy) (hcont₀ y hy) (hcontₕ y hy)
    (B y) havg (hcomp y hy)

end HolomorphicAnosov

