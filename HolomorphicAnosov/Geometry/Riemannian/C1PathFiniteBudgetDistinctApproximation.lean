import HolomorphicAnosov.Geometry.Riemannian.C1PathSmoothReplacementMul
import HolomorphicAnosov.Geometry.Riemannian.C1PathFiniteLength

/-! Nonsmooth C¹ paths with distinct endpoints admit smooth replacements within any finite positive
length budget. -/

open Set MeasureTheory Bundle Filter Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology _root_.Topology

namespace HolomorphicAnosov
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A nonsmooth C¹ path with distinct endpoints admits a smooth path with the same endpoints and
length less than its length plus any finite positive budget. (Petersen, Cor. 5.3.10, p.150) -/
theorem exists_smooth_path_length_lt_add_of_not_smooth_finite_budget_distinct
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    {c : ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ) I 1 c (Icc 0 1))
    (_hsmooth : ¬ ContMDiffOn 𝓘(ℝ) I ∞ c (Icc 0 1))
    {ε : ℝ≥0∞} (hε : 0 < ε) (_hεfinite : ε ≠ (∞ : ℝ≥0∞))
    (_hclosed : c 0 ≠ c 1) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ σ : ℝ → M,
      ContMDiffOn 𝓘(ℝ) I ∞ σ (Icc 0 1) ∧
      σ 0 = c 0 ∧ σ 1 = c 1 ∧
      Manifold.pathELength I σ 0 1 <
        Manifold.pathELength I c 0 1 + ε := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hL := c1_path_elength_ne_top g zero_le_one hc
  have hlt : pathELength I c 0 1 < pathELength I c 0 1 + ε :=
    ENNReal.lt_add_right hL hε.ne'
  have hcont : Continuous (fun r : ℝ≥0 ↦ (r : ℝ≥0∞) * r * pathELength I c 0 1) := by
    apply (ENNReal.continuous_mul_const hL).comp
    exact ENNReal.continuous_coe.comp (continuous_id.mul continuous_id)
  have hev : ∀ᶠ r : ℝ≥0 in 𝓝 1,
      (r : ℝ≥0∞) * r * pathELength I c 0 1 < pathELength I c 0 1 + ε :=
    (hcont.tendsto 1).eventually (gt_mem_nhds (by simpa using hlt))
  obtain ⟨r, hr, hrlen⟩ := (nhdsGT_basis 1).mem_iff.mp (nhdsWithin_le_nhds hev)
  obtain ⟨q, hq1, hqr⟩ := exists_between hr
  have hq := hrlen ⟨hq1, hqr⟩
  obtain ⟨σ, hσ, hσ0, hσ1, hσlen⟩ := c1_path_smooth_replacement_mul g hc q hq1
  exact ⟨σ, hσ, hσ0, hσ1, hσlen.trans_lt hq⟩

end HolomorphicAnosov

