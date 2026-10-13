import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace HolomorphicAnosov

open Set Topology _root_.Topology Metric Bornology

/-- The normalized barycentric coordinate body is closed, convex, and bounded
in the native finite-product maximum norm.

Source: Hatcher, *Algebraic Topology*, §2.1 pp.103–104, where normalized
nonnegative barycentric coefficients form the closed simplex.  The finite-sum
continuity, order-closedness, convex interpolation, and finite-Pi norm bounds
are checked with pinned Mathlib v4.35.0-rc1 APIs.  No nonempty-complex or
nontrivial-vector-space assumption is present; d=0 is included.

Natural-language proof: for V = Fin d → Real, write
Delta = {u | (∀ i, 0 ≤ u i) ∧ Σ i, u i ≤ 1}. Each coordinate evaluation is
continuous, and the finite sum is continuous, so every defining weak inequality
is closed; their intersection is closed. Coordinatewise affine interpolation
preserves nonnegativity, and linearity of the finite sum preserves the sum bound,
so Delta is convex. For u∈Delta, each coordinate lies in [0,1], hence the
native maximum norm is at most one; this gives metric boundedness. -/
theorem standard_coordinate_simplex_closed_convex_bounded (d : ℕ) :
    let V := Fin d → ℝ
    let Delta : Set V := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}
    Convex ℝ Delta ∧ IsClosed Delta ∧ IsBounded Delta := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    constructor
    · intro i
      exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      calc
        a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
            (mul_le_mul_of_nonneg_left hy.2 hb)
        _ = 1 := by simpa using hab
  · convert
      (isClosed_iInter fun i : Fin d ↦
        isClosed_le (continuous_const : Continuous (fun _ : Fin d → ℝ => (0 : ℝ)))
          (continuous_apply i)).inter
        (isClosed_le (continuous_finsetSum (Finset.univ : Finset (Fin d))
          (fun i _ ↦ continuous_apply i))
          (continuous_const : Continuous (fun _ : Fin d → ℝ => (1 : ℝ)))) using 1
    ext u
    simp
  · apply (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := 1)).subset
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    exact (Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i)).trans hu.2


end HolomorphicAnosov
