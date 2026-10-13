import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathLength
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathPieceELength
import HolomorphicAnosov.Geometry.Riemannian.SmoothPathAffineRescale
import Mathlib.Basic.ENNReal.BigOperators

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

/-- A finite chain of smooth unit-interval segments determines a piecewise-smooth path on any strict
partition, with the same endpoints and length equal to the sum of the segment lengths. (Lee,
p.275) -/
theorem assemble_smooth_path_segments
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (n : ℕ) (t : Fin (n + 2) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last (n + 1)) = 1)
    (x : Fin (n + 2) → M) (γ : Fin (n + 1) → ℝ → M)
    (hγ : ∀ i, ContMDiffOn 𝓘(ℝ) I ∞ (γ i) (Icc 0 1))
    (hstart : ∀ i, γ i 0 = x i.castSucc)
    (hend : ∀ i, γ i 1 = x i.succ) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ p : RiemannianPiecewiseSmoothPath I (x 0) (x (Fin.last (n + 1))),
      ENNReal.ofReal (p.length g) = ∑ i, Manifold.pathELength I (γ i) 0 1 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let η : Fin (n + 1) → ℝ → M :=
    fun i s ↦ γ i ((s - t i.castSucc) / (t i.succ - t i.castSucc))
  have hr i := smooth_path_affine_rescale (I := I) (hγ i) (ht (Fin.castSucc_lt_succ (i := i)))
  let p : RiemannianPiecewiseSmoothPath I (x 0) (x (Fin.last (n + 1))) := {
    n := n
    time := t
    time_strictMono := ht
    time_zero := ht0
    time_one := ht1
    piece := η
    piece_smooth := fun i ↦ (hr i).1
    source := by
      have h := (hr 0).2.1.trans (hstart 0)
      simpa only [η, Fin.castSucc_zero, ht0] using h
    target := by
      have h := (hr (Fin.last n)).2.2.1.trans (hend (Fin.last n))
      simpa only [η, Fin.succ_last, ht1] using h
    junction := by
      intro i
      have hleft := (hr i.castSucc).2.2.1.trans (hend i.castSucc)
      have hright := (hr i.succ).2.1.trans (hstart i.succ)
      simpa only [η, Fin.castSucc_succ] using hleft.trans hright.symm }
  refine ⟨p, ?_⟩
  calc
    ENNReal.ofReal (p.length g) = ∑ i, Manifold.pathELength I (p.piece i)
        (p.time i.castSucc) (p.time i.succ) := by
      simp_rw [p.pathELength_piece g]
      exact ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
        intervalIntegral.integral_nonneg_of_forall
          (ht.monotone (Fin.castSucc_le_succ i)) (fun _ ↦ Real.sqrt_nonneg _))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hr i).2.2.2

end HolomorphicAnosov

