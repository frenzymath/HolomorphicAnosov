import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothEDistLeRiemannianEDist
import HolomorphicAnosov.Geometry.Riemannian.RiemannianEDistLePiecewiseSmooth

open Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The C¹ and piecewise-smooth Riemannian extended distances coincide for the same smooth metric.
-/
theorem riemannianEDist_eq_piecewiseSmoothRiemannianEDist
    (h : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x y : M) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨h.toRiemannianMetric⟩
    Manifold.riemannianEDist I x y = piecewiseSmoothRiemannianEDist h x y := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  exact le_antisymm
    (riemannianEDist_le_piecewiseSmoothRiemannianEDist h x y)
    (piecewiseSmoothRiemannianEDist_le_riemannianEDist h x y)

end HolomorphicAnosov

