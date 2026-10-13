import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hölder bounds for lower derivative fields

Source: de la Llave–Obaya, *Regularity of the composition operator in spaces of
Hölder functions*, Proposition 3.6, pp. 165–166, specialized to convex domains.
-/

namespace HolomorphicAnosov

/-- Bounded derivatives through order `n` give a uniform Hölder bound for every lower jet.

Proof: the derivative of the order-`j` field has norm equal to the order-`j+1` jet.
The convex mean-value inequality therefore bounds its difference by `A * ‖x-y‖`.
When the distance is at most one, this is at most `A * ‖x-y‖^α`. For larger distance,
the two value bounds give `2*A`, which is at most `2*A * ‖x-y‖^α`.
No Hölder premise on the order-`n` field is needed. -/
theorem lower_jet_holder_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set E) (hS : IsOpen S) (hSconv : Convex ℝ S)
    (n : ℕ) (α A : ℝ) (hαpos : 0 < α) (hαle : α ≤ 1) (hA : 0 ≤ A)
    (f : E → F) (hf : ContDiffOn ℝ n f S)
    (hfnorm : ∀ i : ℕ, i ≤ n → ∀ z ∈ S, ‖iteratedFDerivWithin ℝ i f S z‖ ≤ A)
    (j : ℕ) (hj : j < n) (x : E) (hx : x ∈ S) (y : E) (hy : y ∈ S) :
    ‖iteratedFDerivWithin ℝ j f S x - iteratedFDerivWithin ℝ j f S y‖ ≤
      (2 * A) * ‖x - y‖ ^ α := by
  have hnorm (i : ℕ) (hi : i ≤ n) (z : E) (hz : z ∈ S) :
      ‖iteratedFDeriv ℝ i f z‖ ≤ A := by
    simpa only [iteratedFDerivWithin_of_isOpen _ hS hz] using hfnorm i hi z hz
  rw [iteratedFDerivWithin_of_isOpen _ hS hx, iteratedFDerivWithin_of_isOpen _ hS hy]
  have hd : ∀ z ∈ S, DifferentiableAt ℝ (iteratedFDeriv ℝ j f) z :=
    fun z hz ↦ (hf.contDiffAt (hS.mem_nhds hz)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast hj)
  have hb : ∀ z ∈ S, ‖fderiv ℝ (iteratedFDeriv ℝ j f) z‖ ≤ A := by
    intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hnorm (j + 1) hj z hz
  have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hdist : ‖x - y‖ ≤ 1
  · have hp : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
      convert Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hdist hαpos.le hαle using 1
      simp only [Real.rpow_one]
    exact (hSconv.norm_image_sub_le_of_norm_fderiv_le hd hb hy hx).trans (by nlinarith)
  · have hp := Real.one_le_rpow (le_of_not_ge hdist) hαpos.le
    apply (norm_sub_le _ _).trans
    have hfx := hnorm j hj.le x hx
    have hfy := hnorm j hj.le y hy
    have hp' : 2 * A ≤ (2 * A) * ‖x - y‖ ^ α := by
      calc
        2 * A = (2 * A) * 1 := by ring
        _ ≤ (2 * A) * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hp (by positivity)
    nlinarith


end HolomorphicAnosov
