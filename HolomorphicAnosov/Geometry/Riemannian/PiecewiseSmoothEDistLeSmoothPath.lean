import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothEDistLeSegmentBounds
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The piecewise-smooth Riemannian extended distance between the endpoints of a smooth path is at
most its Riemannian extended length. (Lee, pp.275, 277) -/
theorem piecewiseSmoothRiemannianEDist_le_smooth_path
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {c : ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ) I ∞ c (Icc 0 1)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    piecewiseSmoothRiemannianEDist g (c 0) (c 1) ≤
      Manifold.pathELength I c 0 1 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let t : Fin 2 → ℝ := fun i ↦ (i : ℝ)
  have ht : StrictMono t := by
    intro i j hij
    simpa [t] using (show (i : ℝ) < (j : ℝ) by exact_mod_cast hij)
  have ht0 : t 0 = 0 := by simp [t]
  have ht1 : t (Fin.last 1) = 1 := by simp [t]
  let γ : Fin 1 → ℝ → M := fun _ ↦ c
  have hγ : ∀ i, ContMDiffOn 𝓘(ℝ) I ∞ (γ i) (Icc 0 1) := by
    intro i
    simpa [γ] using hc
  have hstart : ∀ i, γ i 0 = c (t i.castSucc) := by
    intro i
    simp [γ, t]
  have hend : ∀ i, γ i 1 = c (t i.succ) := by
    intro i
    simp [γ, t]
  have hseg : ∀ i, Manifold.pathELength I (γ i) 0 1 ≤
      (1 : ℝ≥0∞) * Manifold.pathELength I c (t i.castSucc) (t i.succ) := by
    intro i
    simp [γ, t]
  have h := piecewiseSmoothRiemannianEDist_le_segment_bounds g c 0 t ht ht0 ht1
    γ hγ hstart hend 1 hseg
  simpa [t] using h

end HolomorphicAnosov

