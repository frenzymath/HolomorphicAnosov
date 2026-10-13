import HolomorphicAnosov.Geometry.Riemannian.Gauss.SmoothMetricPullbackEntry
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

open Set Bundle
open scoped Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The Riemannian tensor in an ambient chart, pulled back by the inverse-chart differential. -/
def originalMetricChartTensor_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ,E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact (g.inner ((extChartAt 𝓘(ℝ,E) p).symm z)).bilinearComp
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm z)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm z)

/-- The chart expression of the smooth Riemannian tensor is smooth as an operator-valued bilinear
form. -/
theorem originalMetricChartTensor_contDiffOn_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p : M) :
    ContDiffOn ℝ ∞ (originalMetricChartTensor_g18 g p) (extChartAt 𝓘(ℝ,E) p).target := by
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ,E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  exact gauss_smooth_metric_pullback_entry g (isOpen_extChartAt_target p)
    (extChartAt 𝓘(ℝ,E) p).symm (contMDiffOn_extChartAt_symm p) v w

omit [FiniteDimensional ℝ E] in
/-- The chart expression of the Riemannian tensor is strictly positive on every nonzero model vector
at points in the chart target. -/
theorem originalMetricChartTensor_pos_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p : M) (z : E) (hz : z ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (v : E) (hv : v ≠ 0) : 0 < originalMetricChartTensor_g18 g p z v v := by
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ,E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,E)) hz
  simp only [ModelWithCorners.Boundaryless.range_eq_univ,mfderivWithin_univ] at hinv
  obtain ⟨A,hA⟩ := hinv
  apply g.pos
  intro hzero
  apply hv
  rw [← hA] at hzero
  exact A.injective (hzero.trans A.map_zero.symm)

end HolomorphicAnosov
