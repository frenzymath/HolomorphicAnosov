import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Euclidean-radius bound for a scalar Bochner–Martinelli coefficient

Source: Demailly (2012), I §3.D, pp.25–26. This is the agent-written elementary
coordinate norm estimate specified by `analysis.scalar_bm_kernel_norm_bound_g1`.
-/

noncomputable section
open scoped BigOperators

namespace HolomorphicAnosov.Analysis

/-- The pointwise singularity bound for one scalar Bochner–Martinelli coefficient.

Source: Demailly, *Complex Analytic and Differential Geometry* (2012), I §3.D,
pp.25–26, the Euclidean radial kernel. This elementary coordinate estimate is
an agent-written expansion of the singularity estimate in the compact-support
scalar formula, DAG parent `analysis.scalar_bochnermartinelli_compact_support_g2`.

Proof. Put r=sqrt(sum_j |w_j|²). Each summand is nonnegative, so |w_j|²≤r²
and consequently |w_j|≤r. A nonzero coordinate of w makes the sum strictly
positive, hence r>0. Complex conjugation preserves norm, and the denominator
has norm r^(2n). Divide the coordinate bound by this positive power and cancel
one r, using 2n=(2n−1)+1. This argument includes n=1 and requires no comparison
of the product maximum norm with the Euclidean radius. -/
theorem scalar_bochnerMartinelli_kernel_norm_bound
    {n : ℕ} (hn : 1 ≤ n) (w : Fin n → ℂ) (hw : w ≠ 0) (j : Fin n) :
    ‖star (w j) / (Real.sqrt (∑ k, ‖w k‖ ^ 2) : ℂ) ^ (2 * n)‖ ≤
      1 / Real.sqrt (∑ k, ‖w k‖ ^ 2) ^ (2 * n - 1) := by
  let r := Real.sqrt (∑ k, ‖w k‖ ^ 2)
  have hsum : 0 ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hcoord : ∀ k, ‖w k‖ ^ 2 ≤ ∑ l, ‖w l‖ ^ 2 := fun k ↦
    Finset.single_le_sum (fun l _ ↦ sq_nonneg ‖w l‖) (Finset.mem_univ k)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = ∑ k, ‖w k‖ ^ 2 := Real.sq_sqrt hsum
  have hr : 0 < r := by
    by_contra h
    have hz : r = 0 := le_antisymm (le_of_not_gt h) hr0
    apply hw
    funext k
    have hk := hcoord k
    have : ‖w k‖ = 0 := by nlinarith [sq_nonneg ‖w k‖]
    exact norm_eq_zero.mp this
  have hj : ‖w j‖ ≤ r := by nlinarith [hcoord j, norm_nonneg (w j)]
  change ‖star (w j) / (r : ℂ) ^ (2*n)‖ ≤ 1 / r ^ (2*n-1)
  rw [norm_div, norm_star, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
  calc
    _ ≤ r / r ^ (2*n) := div_le_div_of_nonneg_right hj (pow_nonneg hr0 _)
    _ = 1 / r ^ (2*n-1) := by
      have he : 2*n = (2*n-1)+1 := by omega
      conv_lhs => rw [he, pow_succ]
      field_simp

end HolomorphicAnosov.Analysis
