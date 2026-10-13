import HolomorphicAnosov.Geometry.Riemannian.C1PathSmoothApproximation
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothEDistLeSmoothPath
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The piecewise-smooth Riemannian extended distance is bounded above by the C¹ Riemannian extended
distance for the same smooth metric. -/
theorem piecewiseSmoothRiemannianEDist_le_riemannianEDist
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    piecewiseSmoothRiemannianEDist g x y ≤ Manifold.riemannianEDist I x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  by_cases htop : Manifold.riemannianEDist I x y = ⊤
  · simp [htop]
  · have hlt : Manifold.riemannianEDist I x y <
        Manifold.riemannianEDist I x y + ε := by
      have := ENNReal.add_lt_add_left htop hε
      simpa using this
    obtain ⟨γ, hγ0, hγ1, hγ, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt
        (I := I) (x := x) (y := y)
        (r := Manifold.riemannianEDist I x y + ε) hlt
    have hcustom : piecewiseSmoothRiemannianEDist g x y ≤
        Manifold.pathELength I γ 0 1 := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      obtain ⟨σ, hσ, hσ0, hσ1, hσlen⟩ :=
        exists_smooth_path_length_lt_add g hγ hδ
      have hpath := piecewiseSmoothRiemannianEDist_le_smooth_path g hσ
      rw [hσ0, hσ1, hγ0, hγ1] at hpath
      exact hpath.trans hσlen.le
    exact hcustom.trans hγlen.le

end HolomorphicAnosov

