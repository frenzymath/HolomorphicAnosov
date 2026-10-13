import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathPieceELength
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothRiemannianEDist
import HolomorphicAnosov.Geometry.Riemannian.FiniteRiemannianChain
import Mathlib.Basic.ENNReal.BigOperators

namespace HolomorphicAnosov

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The C¹ Riemannian extended distance is at most the piecewise-smooth Riemannian extended distance
for the same metric. (Lee, pp.275–279) -/
theorem riemannianEDist_le_piecewiseSmoothRiemannianEDist
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E
      (fun x : M ↦ TangentSpace I x)) (x y : M) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨h.toRiemannianMetric⟩
    Manifold.riemannianEDist I x y ≤ piecewiseSmoothRiemannianEDist h x y := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  apply le_iInf
  intro p
  have hchain : Manifold.riemannianEDist I x y ≤
      ∑ i : Fin (p.n + 1), Manifold.pathELength I (p.piece i)
        (p.time i.castSucc) (p.time i.succ) := by
    have hj (i : Fin p.n) :
        p.piece i.castSucc (p.time i.castSucc.succ) =
          p.piece i.succ (p.time i.succ.castSucc) := by
      simpa only [Fin.castSucc_succ] using p.junction i
    have hc := riemannianEDist_le_fin_chain (I := I) p.n
      (fun i ↦ p.piece i (p.time i.castSucc))
      (fun i ↦ p.piece i (p.time i.succ)) hj
    simp only [Fin.castSucc_zero, p.time_zero, p.source,
      Fin.succ_last, p.time_one, p.target] at hc
    apply hc.trans
    apply Finset.sum_le_sum
    intro i hi
    exact Manifold.riemannianEDist_le_pathELength
      ((p.piece_smooth i).of_le (by simp)) rfl rfl
      (p.time_strictMono.monotone (Fin.castSucc_le_succ i))
  apply hchain.trans_eq
  simp_rw [p.pathELength_piece h]
  unfold RiemannianPiecewiseSmoothPath.length
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro i hi
  exact intervalIntegral.integral_nonneg_of_forall
    (p.time_strictMono.monotone (Fin.castSucc_le_succ i)) (fun t ↦ Real.sqrt_nonneg _)
end HolomorphicAnosov
