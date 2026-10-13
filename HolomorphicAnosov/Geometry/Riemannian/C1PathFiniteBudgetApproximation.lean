import HolomorphicAnosov.Geometry.Riemannian.C1PathFiniteBudgetC1Approximation
import HolomorphicAnosov.Geometry.Riemannian.C1PathFiniteBudgetDistinctApproximation
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A nonsmooth C¹ path admits a smooth path with the same endpoints and length less than its length
plus any finite positive budget. (Petersen, §5.3, p.150) -/
theorem exists_smooth_path_length_lt_add_of_not_smooth_finite_budget
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    {c : ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ) I 1 c (Icc 0 1))
    (hsmooth : ¬ ContMDiffOn 𝓘(ℝ) I ∞ c (Icc 0 1))
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεfinite : ε ≠ (∞ : ℝ≥0∞)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ σ : ℝ → M,
      ContMDiffOn 𝓘(ℝ) I ∞ σ (Icc 0 1) ∧
      σ 0 = c 0 ∧ σ 1 = c 1 ∧
      Manifold.pathELength I σ 0 1 <
        Manifold.pathELength I c 0 1 + ε := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_cases hclosed : c 0 = c 1
  · refine ⟨fun _ ↦ c 0, contMDiffOn_const, rfl, hclosed, ?_⟩
    have hzero : Manifold.pathELength I (fun _ : ℝ ↦ c 0) 0 1 = 0 := by
      simp [Manifold.pathELength_eq_lintegral_mfderiv_Icc, mfderiv_const]
    rw [hzero]
    exact hε.trans_le (le_add_left le_rfl)
  · exact exists_smooth_path_length_lt_add_of_not_smooth_finite_budget_distinct
      g hc hsmooth hε hεfinite hclosed

end HolomorphicAnosov
