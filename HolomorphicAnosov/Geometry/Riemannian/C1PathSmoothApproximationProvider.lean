import HolomorphicAnosov.Geometry.Riemannian.C1PathFiniteBudgetApproximation
import HolomorphicAnosov.Geometry.Riemannian.C1PathFiniteLength
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A nonsmooth C¹ path admits a smooth path with the same endpoints and length less than its length
plus any positive budget. (Petersen, §5.3, p.150) -/
theorem exists_smooth_path_length_lt_add_of_not_smooth
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    {c : ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ) I 1 c (Icc 0 1))
    (hsmooth : ¬ ContMDiffOn 𝓘(ℝ) I ∞ c (Icc 0 1))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ σ : ℝ → M,
      ContMDiffOn 𝓘(ℝ) I ∞ σ (Icc 0 1) ∧
      σ 0 = c 0 ∧ σ 1 = c 1 ∧
      Manifold.pathELength I σ 0 1 <
        Manifold.pathELength I c 0 1 + ε := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_cases hεfinite : ε ≠ (∞ : ℝ≥0∞)
  · have hcore := exists_smooth_path_length_lt_add_of_not_smooth_finite_budget
      g hc hsmooth hε hεfinite
    exact hcore
  · have htop : ε = (∞ : ℝ≥0∞) := by simpa using hεfinite
    subst ε
    have hcore := exists_smooth_path_length_lt_add_of_not_smooth_finite_budget
      (ε := (1 : ℝ≥0∞)) g hc hsmooth (by norm_num) (by norm_num)
    rcases hcore with ⟨σ, hσ, hσ0, hσ1, hlen⟩
    refine ⟨σ, hσ, hσ0, hσ1, ?_⟩
    have hcfinite : Manifold.pathELength I c 0 1 ≠ (∞ : ℝ≥0∞) :=
      c1_path_elength_ne_top g zero_le_one hc
    have hsumfinite : Manifold.pathELength I c 0 1 + (1 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := by
      exact ENNReal.add_ne_top.mpr ⟨hcfinite, by simp⟩
    have hsigfinite : Manifold.pathELength I σ 0 1 ≠ (∞ : ℝ≥0∞) :=
      ne_of_lt (lt_trans hlen (lt_top_iff_ne_top.mpr hsumfinite))
    simpa using (lt_top_iff_ne_top.mpr hsigfinite)

end HolomorphicAnosov

