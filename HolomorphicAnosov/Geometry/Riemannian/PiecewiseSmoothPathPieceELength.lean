import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathSpeedIntegrable
import Mathlib.Geometry.Manifold.Riemannian.PathELength

namespace HolomorphicAnosov

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Riemannian extended length of a smooth piece equals `ENNReal.ofReal` of its speed integral
for the supplied metric. (Lee, p.275) -/
theorem RiemannianPiecewiseSmoothPath.pathELength_piece
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E
      (fun x : M ↦ TangentSpace I x)) {x y : M}
    (p : RiemannianPiecewiseSmoothPath I x y) (i : Fin (p.n + 1)) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨h.toRiemannianMetric⟩
    Manifold.pathELength I (p.piece i) (p.time i.castSucc) (p.time i.succ) =
      ENNReal.ofReal (∫ t in p.time i.castSucc..p.time i.succ, p.speed h i t) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  have hint := p.speed_integrableOn h i
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc,
    intervalIntegral.integral_of_le (p.time_strictMono.monotone (Fin.castSucc_le_succ i)),
    ← integral_Icc_eq_integral_Ioc]
  change IntegrableOn (p.speed h i) (Icc (p.time i.castSucc) (p.time i.succ)) at hint
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun t ↦ Real.sqrt_nonneg _))]
  apply lintegral_congr
  intro t
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl
end HolomorphicAnosov
