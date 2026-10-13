import HolomorphicAnosov.Dynamics.CutoffProductDerivativeBound

/-!
# A quantitative cutoff product estimate

Source: Merry, *Sixty Lectures on Dynamical Systems*, Lecture 32, Theorem 32.2,
equations (32.6)–(32.7). This is the product-rule and radius-cancellation step
used in the proof of the HPS Theorem 5.5 exponential cutoff extension.
-/

namespace HolomorphicAnosov.ExponentialCutoff

open Set Metric
open scoped Topology _root_.Topology

/-- Multiplying a remainder vanishing at zero by a cutoff of radius `δ`
has Lipschitz constant `(1 + K) * η` when the remainder derivative is bounded
by `η` on the closed cutoff ball and the cutoff derivative by `K / δ`.

Proof: the convex-ball mean value theorem gives `‖q x‖ ≤ η * ‖x‖` on the
closed ball. The product rule then bounds the two derivative terms by `η`
and `(K / δ) * (η * δ) = K * η`. Outside the ball the product is locally
zero. The mean value theorem on the whole vector space finishes.
Source: Merry, Lecture 32, equations (32.6)–(32.7), with the finite cutoff
bound retained explicitly instead of prescribing a numerical constant. -/
theorem cutoff_product_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : E → ℝ) (q : E → F) {δ K η : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hχ : Differentiable ℝ χ)
    (hχbound : ∀ x, ‖χ x‖ ≤ 1)
    (hχderiv : ∀ x, ‖x‖ ≤ δ → ‖fderiv ℝ χ x‖ ≤ K / δ)
    (hχzero : ∀ x, δ < ‖x‖ → χ x = 0)
    (hqzero : q 0 = 0)
    (hq : ∀ x, ‖x‖ ≤ δ → DifferentiableAt ℝ q x)
    (hqderiv : ∀ x, ‖x‖ ≤ δ → ‖fderiv ℝ q x‖ ≤ η)
    (v w : E) :
    ‖χ v • q v - χ w • q w‖ ≤ (1 + K) * η * ‖v - w‖ := by
  have hb := cutoff_product_derivative_bound χ q hδ hK hη hχ hχbound hχderiv
    hχzero hqzero hq hqderiv
  exact (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ ↦ (hb x).1) (fun x _ ↦ (hb x).2) (mem_univ w) (mem_univ v)


end HolomorphicAnosov.ExponentialCutoff
