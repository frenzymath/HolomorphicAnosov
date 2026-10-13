import HolomorphicAnosov.Geometry.Riemannian.C1PathFiniteLength
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A C¹ path admits a C¹ path with the same endpoints and length less than its length plus any
finite positive budget. (Petersen, §5.3, pp.146–150; Lee, p.275) -/
theorem exists_c1_path_length_lt_add_finite_budget
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    {c : ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ) I 1 c (Icc 0 1))
    {ε : ℝ≥0∞} (hε : 0 < ε) (_hεfinite : ε ≠ (∞ : ℝ≥0∞)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ σ : ℝ → M,
      ContMDiffOn 𝓘(ℝ) I 1 σ (Icc 0 1) ∧
      σ 0 = c 0 ∧ σ 1 = c 1 ∧
      Manifold.pathELength I σ 0 1 <
        Manifold.pathELength I c 0 1 + ε := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcfinite : Manifold.pathELength I c 0 1 ≠ (∞ : ℝ≥0∞) :=
    c1_path_elength_ne_top g zero_le_one hc
  have hdist : Manifold.riemannianEDist I (c 0) (c 1) ≤
      Manifold.pathELength I c 0 1 :=
    Manifold.riemannianEDist_le_pathELength hc rfl rfl zero_le_one
  have hlt : Manifold.riemannianEDist I (c 0) (c 1) <
      Manifold.pathELength I c 0 1 + ε :=
    hdist.trans_lt (ENNReal.lt_add_right hcfinite hε.ne')
  obtain ⟨σ, hσ0, hσ1, hσ, hlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hlt
  exact ⟨σ, hσ, hσ0, hσ1, hlen⟩

end HolomorphicAnosov

