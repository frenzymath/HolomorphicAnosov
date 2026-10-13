import HolomorphicAnosov.Analysis.Complex.ClosedRectangleHorizontalCurve
import HolomorphicAnosov.Analysis.Complex.RectangleDerivativeEnergy
import HolomorphicAnosov.Analysis.Complex.RectangleDerivativeSlices
import HolomorphicAnosov.Analysis.Complex.QCIntervalEndpointBound
import HolomorphicAnosov.Analysis.MarkedRectangleVerticalSides

/-!
# Almost-everywhere horizontal curves and their length lower bound

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed pp.341–342, horizontal length estimate (11.3).
-/

namespace HolomorphicAnosov.Analysis

open Set MeasureTheory

/-- Almost every horizontal slice of a marked holomorphic rectangle bijection
has a continuous closed curve, integrable actual velocity, and real endpoint
displacement equal to the target width. Its length is at least that width.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, printed pp.341–342,
(11.3), with the endpoint-continuity Fubini justification of Lehto–Virtanen
(1973), I.Theorem 3.1, pp.18–19, footnote 5.
Proof: The exact holomorphic image-area formula in coordinate product measure
makes the squared derivative energy finite. Fubini and the finite-energy
Cauchy–Schwarz theorem make the derivative interval integrable on almost every
horizontal slice. At each such interior height construct the globally continuous
clamped curve from the given closed extension; its interior velocity is exactly
the complex derivative of T. The marked-corner side-correspondence theorem sends
the two endpoints to the target left and right sides, giving real displacement A.
The fundamental theorem for the endpoint-continuous curve bounds its endpoint
distance by the integral of its speed. Real displacement is at most distance,
so A is at most that length. No boundary derivative or reflection is required.
-/
theorem ae_closed_horizontal_curves
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
      ∃ g : ℝ → ℂ,
        (∀ x ∈ Ioo 0 a, g x = T ((x : ℂ) + (t : ℂ) * Complex.I)) ∧
        ContinuousOn g (Icc 0 a) ∧
        (∀ x ∈ Ioo 0 a,
          HasDerivAt g (deriv T ((x : ℂ) + (t : ℂ) * Complex.I)) x) ∧
        IntervalIntegrable (fun x : ℝ ↦ deriv T ((x : ℂ) + (t : ℂ) * Complex.I))
          volume 0 a ∧
        (g a).re - (g 0).re = A ∧
        A ≤ ∫ x in (0 : ℝ)..a, ‖deriv T ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have henergy := Complex.rectangle_derivative_energy h_holomorphic h_bijective
  have hfinite : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (‖deriv T (⟨p.1, p.2⟩ : ℂ)‖ ^ 2)
      ∂(volume.restrict (Ioo 0 a)).prod (volume.restrict (Ioo 0 b))) ≠ ⊤ := by
    rw [henergy]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hslices := Complex.ae_intervalIntegrable_rectangle_deriv ha.le h_holomorphic hfinite
  have hside := marked_rectangle_open_vertical_side ha hb hA hB T h_bijective e
    h_extension h_zero h_right h_top_right h_top_left
  filter_upwards [hslices, ae_restrict_mem measurableSet_Ioo] with t hint ht
  obtain ⟨g, hgc, hgmatch, hgd⟩ := Complex.exists_closed_rectangle_horizontal_curve ha.le ht
    h_holomorphic (fun z ↦ (e z : ℂ)) (continuous_subtype_val.comp e.continuous) h_extension
  have hcoord (x : ℝ) : (⟨x, t⟩ : ℂ) = (x : ℂ) + (t : ℂ) * Complex.I := by
    apply _root_.Complex.ext <;> simp
  simp only [hcoord] at hint
  have hleft : (g 0).re = 0 := by
    rw [hgmatch 0 ⟨le_rfl, ha.le⟩]
    exact (hside 0 0 (Or.inl ⟨rfl, rfl⟩) _ (by simp) (by simpa using ht)).1
  have hright : (g a).re = A := by
    rw [hgmatch a ⟨ha.le, le_rfl⟩]
    exact (hside a A (Or.inr ⟨rfl, rfl⟩) _ (by simp) (by simpa using ht)).1
  have hdispl : (g a).re - (g 0).re = A := by rw [hleft, hright, sub_zero]
  refine ⟨g, ?_, hgc.continuousOn, hgd, hint, hdispl, ?_⟩
  · intro x hx
    rw [hgmatch x ⟨hx.1.le, hx.2.le⟩]
    apply h_extension
    simpa [Complex.mem_reProdIm] using And.intro hx ht
  · have hbound := HolomorphicAnosov.qc_slice_endpoint_bound ha.le hgc.continuousOn hgd hint
    have hre := Complex.re_le_norm (g a - g 0)
    simpa only [Complex.sub_re, hdispl] using hre.trans hbound

end HolomorphicAnosov.Analysis

