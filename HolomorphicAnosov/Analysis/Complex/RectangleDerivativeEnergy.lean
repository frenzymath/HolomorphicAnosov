import HolomorphicAnosov.Analysis.Complex.HolomorphicImageArea
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Exact derivative energy in rectangle coordinates

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed p.342: the integral of the Jacobian is the
area of the target rectangle. This gives the coordinate product-measure form
needed by the horizontal-slice length–area argument.
-/

open Set MeasureTheory
open scoped ENNReal

namespace HolomorphicAnosov.Analysis.Complex

/-- The squared complex derivative of a holomorphic rectangle bijection has
coordinate energy equal to the target area.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, printed p.342.
Proof: The complex-to-real-product coordinate equivalence preserves Lebesgue
volume. Its inverse pulls the complex source rectangle back to the product of
the two open coordinate intervals. Transport the nonnegative derivative-energy
integral through this measurable equivalence. The holomorphic image-area theorem
equals that integral to the measure of the target rectangle. Transport the target
rectangle measure to the real product and multiply the two interval lengths.
All endpoint parameters are allowed: a nonpositive target side has zero measure,
and the product of the positive parts records that degenerate case exactly.
-/
theorem rectangle_derivative_energy
    {a b A B : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Complex.reProdIm (Ioo 0 a) (Ioo 0 b)))
    (hbij : BijOn f (Complex.reProdIm (Ioo 0 a) (Ioo 0 b))
      (Complex.reProdIm (Ioo 0 A) (Ioo 0 B))) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (‖deriv f (⟨p.1, p.2⟩ : ℂ)‖ ^ 2)
      ∂(volume.restrict (Ioo 0 a)).prod (volume.restrict (Ioo 0 b))) =
      ENNReal.ofReal A * ENNReal.ofReal B := by
  have hcoord := Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd
  have htransport := hcoord.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun z ↦ ENNReal.ofReal (‖deriv f z‖ ^ 2))
    (Complex.reProdIm (Ioo 0 a) (Ioo 0 b))
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹'
      Complex.reProdIm (Ioo 0 a) (Ioo 0 b) = Ioo 0 a ×ˢ Ioo 0 b := by
    ext p
    rfl
  rw [hpre] at htransport
  simp only [Complex.measurableEquivRealProd_symm_apply] at htransport
  rw [Measure.prod_restrict]
  change (∫⁻ p : ℝ × ℝ in Ioo 0 a ×ˢ Ioo 0 b,
    ENNReal.ofReal (‖deriv f (⟨p.1, p.2⟩ : ℂ)‖ ^ 2)) = _
  rw [htransport, lintegral_norm_deriv_sq_eq_volume_image
    (isOpen_Ioo.reProdIm isOpen_Ioo) hf hbij.injOn, hbij.image_eq]
  have htarget := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
    (Ioo 0 A ×ˢ Ioo 0 B)
  change volume (Complex.reProdIm (Ioo 0 A) (Ioo 0 B)) = _ at htarget
  rw [htarget]
  change volume.prod volume (Ioo 0 A ×ˢ Ioo 0 B) = _
  rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo, sub_zero, sub_zero]

end HolomorphicAnosov.Analysis.Complex

