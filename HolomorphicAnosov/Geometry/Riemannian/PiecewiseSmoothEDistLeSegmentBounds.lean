import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothRiemannianEDist
import HolomorphicAnosov.Geometry.Riemannian.AssembleSmoothPathSegments
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothRiemannianEDistLePath
import HolomorphicAnosov.Geometry.Riemannian.SumPathELengthPartition

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

/-- If smooth replacements on a strict partition have lengths bounded by a common factor times the
original segment lengths, the piecewise-smooth distance is bounded by that factor times the original
curve length. (Lee, pp.275, 277) -/
theorem piecewiseSmoothRiemannianEDist_le_segment_bounds
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ → M) (n : ℕ) (t : Fin (n + 2) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last (n + 1)) = 1)
    (γ : Fin (n + 1) → ℝ → M)
    (hγ : ∀ i, ContMDiffOn 𝓘(ℝ) I ∞ (γ i) (Icc 0 1))
    (hstart : ∀ i, γ i 0 = c (t i.castSucc))
    (hend : ∀ i, γ i 1 = c (t i.succ)) (C : ℝ≥0∞) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    (∀ i, Manifold.pathELength I (γ i) 0 1 ≤
      C * Manifold.pathELength I c (t i.castSucc) (t i.succ)) →
    piecewiseSmoothRiemannianEDist g (c 0) (c 1) ≤
      C * Manifold.pathELength I c 0 1 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro hbound
  obtain ⟨p, hp⟩ := assemble_smooth_path_segments g n t ht ht0 ht1
    (fun i ↦ c (t i)) γ hγ hstart hend
  have hdistance := (piecewiseSmoothRiemannianEDist_le_path g p).trans_eq hp
  simp only [ht0, ht1] at hdistance
  let d : ℕ → ℝ := fun k ↦ t ⟨min k (n + 1), by omega⟩
  have hd : Monotone d := by
    intro j k hjk
    exact ht.monotone (min_le_min_right (n + 1) hjk)
  have hsum := sum_pathELength_partition (I := I) (γ := c) d hd (n + 1)
  have heq : (∑ i : Fin (n + 1), Manifold.pathELength I c (t i.castSucc) (t i.succ)) =
      Manifold.pathELength I c 0 1 := by
    convert hsum using 1
    · apply Finset.sum_congr rfl
      intro i hi
      dsimp only [d]
      congr 2 <;> apply Fin.ext <;> simp ; omega
    · have hd0 : d 0 = 0 := by simpa [d] using ht0
      have hd1 : d (n + 1) = 1 := by
        change t ⟨min (n + 1) (n + 1), _⟩ = 1
        convert ht1 using 1
        congr 1 ; apply Fin.ext ; simp
      rw [hd0, hd1]
  calc
    _ ≤ ∑ i, Manifold.pathELength I (γ i) 0 1 := hdistance
    _ ≤ ∑ i, C * Manifold.pathELength I c (t i.castSucc) (t i.succ) :=
      Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = C * Manifold.pathELength I c 0 1 := by rw [← Finset.mul_sum, heq]

end HolomorphicAnosov

