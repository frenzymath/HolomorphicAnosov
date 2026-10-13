import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathSpeed
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace HolomorphicAnosov

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The speed of each smooth piece is integrable on its closed parameter interval. (Lee, p.275) -/
theorem RiemannianPiecewiseSmoothPath.speed_integrableOn
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E
      (fun x : M ↦ TangentSpace I x)) {x y : M}
    (p : RiemannianPiecewiseSmoothPath I x y) (i : Fin (p.n + 1)) :
    IntegrableOn (p.speed h i) (p.pieceInterval i) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  have ht := (p.piece_smooth i).continuousOn_tangentMapWithin (by simp)
    ((uniqueDiffOn_Icc (p.time_strictMono Fin.castSucc_lt_succ)).uniqueMDiffOn)
  have hc : Continuous (fun t : ℝ ↦
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ) ℝ)) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hv : ContinuousOn (fun t ↦
      (⟨p.piece i t, p.velocity i t⟩ : TangentBundle I M)) (p.pieceInterval i) :=
    ht.comp hc.continuousOn (fun t ht ↦ ht)
  have hs : ContinuousOn (p.speed h i) (p.pieceInterval i) := by
    exact (hv.inner_bundle hv).sqrt
  exact hs.integrableOn_Icc

end HolomorphicAnosov
