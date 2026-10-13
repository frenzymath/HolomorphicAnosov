import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace HolomorphicAnosov

/-- First derivative Hölder estimate in the base case of de la Llave–Obaya,
Theorem 4.3(ii.3), printed pp.169–170.

The chain rule writes the derivative as the product of the two derivative fields.
Subtract the products at x and y and insert the mixed product. The first difference
is bounded using the Hölder estimate for Dg and the Af-Lipschitz estimate for f
on the convex domain; the second uses the Hölder estimate for Df. Operator
composition has norm at most the product of norms. The two resulting terms are
Ag Af^(1+α) and Ag Af, times the α power of the distance. -/
theorem composition_fderiv_holder_bound
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : Set E) (B : Set F) (hA : IsOpen A) (hcA : Convex ℝ A) (hB : IsOpen B)
    (f : E → F) (g : F → G) (hf : ContDiffOn ℝ 1 f A) (hg : ContDiffOn ℝ 1 g B)
    (hmap : Set.MapsTo f A B) (Af Ag α : ℝ) (hAf : 0 ≤ Af) (hAg : 0 ≤ Ag)
    (hα : 0 < α)
    (hfnorm : ∀ x ∈ A, ‖fderiv ℝ f x‖ ≤ Af)
    (hgnorm : ∀ y ∈ B, ‖fderiv ℝ g y‖ ≤ Ag)
    (hfhold : ∀ x ∈ A, ∀ y ∈ A,
      ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ Af * ‖x - y‖ ^ α)
    (hghold : ∀ x ∈ B, ∀ y ∈ B,
      ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ Ag * ‖x - y‖ ^ α)
    (x : E) (hx : x ∈ A) (y : E) (hy : y ∈ A) :
    ‖fderiv ℝ (g ∘ f) x - fderiv ℝ (g ∘ f) y‖ ≤
      Ag * Af * (1 + Af ^ α) * ‖x - y‖ ^ α := by
  have hfd (z : E) (hz : z ∈ A) : DifferentiableAt ℝ f z :=
    (hf.contDiffAt (hA.mem_nhds hz)).differentiableAt (by norm_num)
  have hgd (z : F) (hz : z ∈ B) : DifferentiableAt ℝ g z :=
    (hg.contDiffAt (hB.mem_nhds hz)).differentiableAt (by norm_num)
  have hLip : ‖f x - f y‖ ≤ Af * ‖x - y‖ :=
    hcA.norm_image_sub_le_of_norm_fderiv_le hfd hfnorm hy hx
  have hpow : ‖f x - f y‖ ^ α ≤ Af ^ α * ‖x - y‖ ^ α := by
    calc
      _ ≤ (Af * ‖x - y‖) ^ α := Real.rpow_le_rpow (norm_nonneg _) hLip hα.le
      _ = _ := Real.mul_rpow hAf (norm_nonneg _)
  rw [fderiv_comp x (hgd (f x) (hmap hx)) (hfd x hx),
    fderiv_comp y (hgd (f y) (hmap hy)) (hfd y hy)]
  have hid : (fderiv ℝ g (f x)).comp (fderiv ℝ f x) -
      (fderiv ℝ g (f y)).comp (fderiv ℝ f y) =
      (fderiv ℝ g (f x) - fderiv ℝ g (f y)).comp (fderiv ℝ f x) +
        (fderiv ℝ g (f y)).comp (fderiv ℝ f x - fderiv ℝ f y) := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖(fderiv ℝ g (f x) - fderiv ℝ g (f y)).comp (fderiv ℝ f x)‖ +
        ‖(fderiv ℝ g (f y)).comp (fderiv ℝ f x - fderiv ℝ f y)‖ := norm_add_le _ _
    _ ≤ (Ag * (Af ^ α * ‖x - y‖ ^ α)) * Af +
        Ag * (Af * ‖x - y‖ ^ α) := by
      apply add_le_add
      · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
        exact mul_le_mul ((hghold (f x) (hmap hx) (f y) (hmap hy)).trans
          (mul_le_mul_of_nonneg_left hpow hAg)) (hfnorm x hx) (norm_nonneg _) (by positivity)
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hgnorm (f y) (hmap hy)) (hfhold x hx y hy)
            (norm_nonneg _) hAg)
    _ = _ := by ring


end HolomorphicAnosov
