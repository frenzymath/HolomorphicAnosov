import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Every scalar coefficient of the Bochner–Martinelli kernel is jointly infinitely real differentiable at a pair of distinct complex points.

Source: Demailly, Complex Analytic and Differential Geometry (2012), I §3.D (3.23), p.26, and
proof of (3.26), p.27: kernel has no singularities away from the diagonal.
DAG node: `analysis.dbar_helper_bm_kernel_smooth_off_diagonal_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology BigOperators

namespace HolomorphicAnosov.Analysis

/--
Every scalar coefficient of the Bochner–Martinelli kernel is jointly infinitely real
differentiable at a pair of distinct complex points.

Source: Demailly (2012), I §3.D (3.23), p.26, and proof of (3.26), p.27: kernel has no
singularities away from the diagonal.

Proof: Use the displayed rational kernel formula. Expand the squared Euclidean radius as the
finite sum of squared coordinate norms. Distinct points have one nonzero coordinate difference, so
this sum is positive. Each coordinate difference and its conjugate are smooth, and each squared
norm is smooth. The finite sum and its nth power are smooth; its value is nonzero. Native
smoothness of inversion and multiplication gives smoothness of the rational coefficient.
-/
theorem bm_kernel_smooth_off_diagonal {n : ℕ} (j : Fin n)
    (z w : Fin n → ℂ) (h : w ≠ z) :
    ContDiffAt ℝ ∞ (fun p : (Fin n → ℂ) × (Fin n → ℂ) ↦
      scalarBochnerMartinelliKernel j p.1 p.2) (z,w) := by
  have hformula : (fun p : (Fin n → ℂ) × (Fin n → ℂ) ↦
      scalarBochnerMartinelliKernel j p.1 p.2) =
      (fun p ↦ star (p.2 j - p.1 j) /
        ((∑ i, ‖p.2 i - p.1 i‖ ^ 2 : ℝ) : ℂ) ^ n) := by
    funext p
    unfold scalarBochnerMartinelliKernel bochnerMartinelliEuclideanNorm
    rw [pow_mul, ← Complex.ofReal_pow,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    rfl
  rw [hformula]
  have he (i : Fin n) : ContDiff ℝ ∞
      (fun p : (Fin n → ℂ) × (Fin n → ℂ) ↦ p.2 i - p.1 i) :=
    (contDiff_apply ℝ _ i |>.comp contDiff_snd).sub (contDiff_apply ℝ _ i |>.comp contDiff_fst)
  have hd : ContDiff ℝ ∞
      (fun p : (Fin n → ℂ) × (Fin n → ℂ) ↦ (∑ i, ‖p.2 i - p.1 i‖ ^ 2 : ℝ)) :=
    ContDiff.sum fun i _ ↦ (he i).norm_sq ℂ
  have hdist : 0 < ∑ i, ‖w i - z i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
      ⟨i, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hi))⟩
  simpa only [div_eq_mul_inv, Function.comp_def, Complex.conjCLE_apply, Complex.ofRealCLM_apply] using!
    (Complex.conjCLE.contDiff.comp (he j)).contDiffAt.mul
      (((Complex.ofRealCLM.contDiff.comp hd).pow n).contDiffAt.inv
        (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hdist))))


end HolomorphicAnosov.Analysis
