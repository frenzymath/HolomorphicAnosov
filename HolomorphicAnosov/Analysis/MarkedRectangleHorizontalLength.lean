import HolomorphicAnosov.Analysis.MarkedRectangleHorizontalCurves
import HolomorphicAnosov.Analysis.Complex.RectangleDerivativeEnergy
import HolomorphicAnosov.Analysis.Complex.ClosedEmbeddingHolomorphicInverse
import HolomorphicAnosov.Analysis.Measure.RectangleLengthAreaEquality

/-!
# Almost-everywhere equality in marked rectangle horizontal lengths

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed pp.342–343, forward/inverse conformal
length–area bounds and equality in the horizontal length inequality.
-/

namespace HolomorphicAnosov.Analysis

open Set MeasureTheory

/-- The derivative speed integral along almost every horizontal segment equals
the target rectangle width.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, pp.342–343.
Proof: The closed extension's inverse has a holomorphic ambient representative
on the target interior, and it is bijective back to the source. The inverse
homeomorphism has the inverse corner marks. Apply the proved AE closed-curve
length lower bound to both directions. Their derivative norm densities are
measurable on the coordinate rectangles by holomorphic derivative continuity.
The exact coordinate area identities give energies AB and ab. Apply the
original-dimension forward/inverse scalar length–area theorem with horizontal
measure masses a,A and vertical masses b,B. It proves aB=Ab and equality of
both slice lower bounds almost everywhere. Null endpoint singletons identify
the real restricted-open-interval integrals with the displayed interval integral.
No height normalization, boundary derivative, or reflection is used.
-/
theorem ae_horizontal_length_eq_width
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (T : ℂ → ℂ)
    (h_holomorphic : DifferentiableOn ℂ T ((Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b))))
    (h_bijective : Set.BijOn T ((Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b))) ((Complex.reProdIm (Set.Ioo 0 A) (Set.Ioo 0 B))))
    (e : (Complex.reProdIm (Set.Icc 0 a) (Set.Icc 0 b)) ≃ₜ (Complex.reProdIm (Set.Icc 0 A) (Set.Icc 0 B)))
    (h_extension : ∀ z : (Complex.reProdIm (Set.Icc 0 a) (Set.Icc 0 b)),
      (z : ℂ) ∈ (Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b)) → (e z : ℂ) = T z)
    (h_zero : (e ⟨0, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = 0)
    (h_right : (e ⟨(a : ℂ), by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ))
    (h_top_right : (e ⟨(a : ℂ) + (b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) =
      (A : ℂ) + (B : ℂ) * Complex.I)
    (h_top_left : (e ⟨(b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) =
      (B : ℂ) * Complex.I) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 b),
      (∫ x in (0 : ℝ)..a, ‖deriv T ((x : ℂ) + (t : ℂ) * Complex.I)‖) = A := by
  have hU : IsOpen (Complex.reProdIm (Ioo 0 a) (Ioo 0 b)) :=
    isOpen_Ioo.reProdIm isOpen_Ioo
  have hV : IsOpen (Complex.reProdIm (Ioo 0 A) (Ioo 0 B)) :=
    isOpen_Ioo.reProdIm isOpen_Ioo
  obtain ⟨S, hS, hSbij, hSext⟩ := Complex.exists_holomorphic_inverse_extension
    (K := Complex.reProdIm (Icc 0 a) (Icc 0 b))
    (L := Complex.reProdIm (Icc 0 A) (Icc 0 B)) hU hV
    (fun z hz ↦ ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩)
    (fun z hz ↦ ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩)
    h_holomorphic h_bijective e h_extension
  have hmark (z : Complex.reProdIm (Icc 0 a) (Icc 0 b))
      (w : Complex.reProdIm (Icc 0 A) (Icc 0 B))
      (h : (e z : ℂ) = (w : ℂ)) : (e.symm w : ℂ) = (z : ℂ) := by
    have heq : e z = w := Subtype.ext h
    rw [← heq, e.symm_apply_apply]
  have hforward := ae_closed_horizontal_curves ha hb hA hB T h_holomorphic h_bijective e
    h_extension h_zero h_right h_top_right h_top_left
  have hreverse := ae_closed_horizontal_curves hA hB ha hb S hS hSbij e.symm
    (fun w _ ↦ (hSext w).symm)
    (hmark ⟨0, by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩
      ⟨0, by simp [Complex.mem_reProdIm, hA.le, hB.le]⟩ h_zero)
    (hmark ⟨(a : ℂ), by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩
      ⟨(A : ℂ), by simp [Complex.mem_reProdIm, hA.le, hB.le]⟩ h_right)
    (hmark ⟨(a : ℂ) + (b : ℂ) * Complex.I, by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩
      ⟨(A : ℂ) + (B : ℂ) * Complex.I, by simp [Complex.mem_reProdIm, hA.le, hB.le]⟩ h_top_right)
    (hmark ⟨(b : ℂ) * Complex.I, by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩
      ⟨(B : ℂ) * Complex.I, by simp [Complex.mem_reProdIm, hA.le, hB.le]⟩ h_top_left)
  have hfm : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ‖deriv T ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖)
      ((volume.restrict (Ioo 0 a)).prod (volume.restrict (Ioo 0 b))) := by
    rw [Measure.prod_restrict]
    apply ContinuousOn.aestronglyMeasurable _ (measurableSet_Ioo.prod measurableSet_Ioo)
    apply ((h_holomorphic.deriv hU).continuousOn.comp (by fun_prop) ?_).norm
    intro p hp
    simpa [Complex.mem_reProdIm] using hp
  have hgm : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ‖deriv S ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖)
      ((volume.restrict (Ioo 0 A)).prod (volume.restrict (Ioo 0 B))) := by
    rw [Measure.prod_restrict]
    apply ContinuousOn.aestronglyMeasurable _ (measurableSet_Ioo.prod measurableSet_Ioo)
    apply ((hS.deriv hV).continuousOn.comp (by fun_prop) ?_).norm
    intro p hp
    simpa [Complex.mem_reProdIm] using hp
  have hcoord (p : ℝ × ℝ) : (⟨p.1, p.2⟩ : ℂ) =
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    apply _root_.Complex.ext <;> simp
  have hfe := Complex.rectangle_derivative_energy h_holomorphic h_bijective
  have hge := Complex.rectangle_derivative_energy hS hSbij
  simp only [hcoord, ← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_mul ha.le] at hfe hge
  have hfl : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 b),
      A ≤ ∫ x : ℝ in Ioo 0 a, ‖deriv T ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
    filter_upwards [hforward] with t ht
    obtain ⟨g, _, _, _, _, _, hlen⟩ := ht
    simpa only [intervalIntegral.integral_of_le ha.le, integral_Ioc_eq_integral_Ioo] using hlen
  have hgl : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 B),
      a ≤ ∫ x : ℝ in Ioo 0 A, ‖deriv S ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
    filter_upwards [hreverse] with t ht
    obtain ⟨g, _, _, _, _, _, hlen⟩ := ht
    simpa only [intervalIntegral.integral_of_le hA.le, integral_Ioc_eq_integral_Ioo] using hlen
  have hmass (c : ℝ) (hc : 0 ≤ c) :
      ((volume.restrict (Ioo 0 c)) univ).toReal = c := by
    simp [Real.volume_Ioo, ENNReal.toReal_ofReal hc]
  have hresult := Measure.aspect_eq_and_ae_slice_integral_eq ha hb hA hB
    (hmass a ha.le) (hmass b hb.le) (hmass A hA.le) (hmass B hB.le)
    hfm hgm (ae_of_all _ (fun _ ↦ norm_nonneg _)) (ae_of_all _ (fun _ ↦ norm_nonneg _))
    hfe hge hfl hgl
  simpa only [intervalIntegral.integral_of_le ha.le, integral_Ioc_eq_integral_Ioo] using hresult.2.1

end HolomorphicAnosov.Analysis

