import HolomorphicAnosov.Analysis.MarkedRectangleHorizontalCurves
import HolomorphicAnosov.Analysis.MarkedRectangleHorizontalLength
import HolomorphicAnosov.Analysis.Complex.InteriorHorizontalLengthEquality
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Homeomorph.Defs

/-!
# Horizontal preservation for marked holomorphic rectangle bijections

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed pp.341–343, conformal K=1 length–area argument.
The endpoint-continuity version of the slice bound follows Lehto–Virtanen (1973),
I.Theorem 3.1, pp.18–19; no boundary derivative is required.
-/

namespace HolomorphicAnosov.Analysis.MarkedRectangleHorizontalPreservation

open Set MeasureTheory

/-- A corner-marked holomorphic rectangle bijection preserves horizontal lines.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, printed pp.341–343.
Complete natural-language proof:

1. Apply analysis.marked_rectangle_horizontal_curves_g20 to construct the
actual closed horizontal curves at almost every interior height. This theorem
uses the closed extension and four marks to prove side correspondence, exact
endpoint displacement A, the derivative formula, its interval integrability,
and the horizontal length lower bound.

2. Apply analysis.marked_rectangle_horizontal_length_g20 to prove that the
horizontal speed integral equals A almost everywhere. Its source argument
constructs the literal holomorphic inverse agreeing with e.symm, applies the
same length lower bound to both directions, and uses the exact derivative areas
AB and ab. The original-dimension scalar length–area theorem gives aB=Ab and
both AE equalities, without normalizing heights. The two AE events together give
continuous closed curves whose length equals their real endpoint displacement.

3. Apply analysis.interior_horizontal_length_equality_g20 to each such curve.
Its subinterval fundamental-theorem argument forces zero imaginary displacement
between any two points of the horizontal curve. Fix two interior real coordinates.
Their image imaginary coordinates are continuous functions of height, since T
is holomorphic on the open rectangle. They agree almost everywhere by the curve
result; Measure.eqOn_open_of_ae_eq makes them agree at every interior height.
Identifying the complex points by their real and imaginary coordinates proves
the stated horizontal preservation.

This uses only the conformal K=1 forward/inverse inequalities and the source's
first equality argument. No boundary differentiability or local reflection is
required. The target statement is unchanged.
-/
theorem horizontal_preservation
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
    ∀ z ∈ (Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b)),
      ∀ w ∈ (Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b)),
        z.im = w.im → (T z).im = (T w).im := by
  suffices hcurves : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 b),
      ∃ g g' : ℝ → ℂ,
        (∀ x ∈ Ioo 0 a, g x = T ((x : ℂ) + (t : ℂ) * Complex.I)) ∧
        ContinuousOn g (Icc 0 a) ∧
        (∀ x ∈ Ioo 0 a, HasDerivAt g (g' x) x) ∧
        IntervalIntegrable g' volume 0 a ∧
        (∫ x in (0 : ℝ)..a, ‖g' x‖) = (g a).re - (g 0).re by
    intro z hz w hw hi
    have hc (x : ℝ) (hx : x ∈ Ioo 0 a) :
        ContinuousOn (fun t : ℝ ↦ (T ((x : ℂ) + (t : ℂ) * Complex.I)).im)
          (Ioo 0 b) := by
      apply Complex.continuous_im.comp_continuousOn
      apply h_holomorphic.continuousOn.comp (by fun_prop)
      intro t ht
      simpa [Complex.mem_reProdIm] using And.intro hx ht
    have heq : (fun t : ℝ ↦ (T ((z.re : ℂ) + (t : ℂ) * Complex.I)).im) =ᵐ[
        volume.restrict (Ioo 0 b)]
        (fun t : ℝ ↦ (T ((w.re : ℂ) + (t : ℂ) * Complex.I)).im) := by
      filter_upwards [hcurves] with t ht
      obtain ⟨g, g', hmatch, hgc, hd, hint, hlen⟩ := ht
      have he := Analysis.Complex.im_eq_of_interior_length_eq_re_sub hgc hd hint hlen
        z.re ⟨hz.1.1.le, hz.1.2.le⟩ w.re ⟨hw.1.1.le, hw.1.2.le⟩
      simpa only [hmatch z.re hz.1, hmatch w.re hw.1] using he
    have hp := Measure.eqOn_open_of_ae_eq heq isOpen_Ioo (hc z.re hz.1) (hc w.re hw.1)
    have hzrep : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
    have hwrep : (w.re : ℂ) + (z.im : ℂ) * Complex.I = w := by
      rw [hi]
      exact Complex.re_add_im w
    simpa only [hzrep, hwrep] using hp hz.2
  have hdata := Analysis.ae_closed_horizontal_curves ha hb hA hB T h_holomorphic
    h_bijective e h_extension h_zero h_right h_top_right h_top_left
  suffices hlen : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 b),
      (∫ x in (0 : ℝ)..a, ‖deriv T ((x : ℂ) + (t : ℂ) * Complex.I)‖) = A by
    filter_upwards [hdata, hlen] with t ht hlength
    obtain ⟨g, hmatch, hgc, hd, hint, hdispl, _⟩ := ht
    exact ⟨g, (fun x ↦ deriv T ((x : ℂ) + (t : ℂ) * Complex.I)),
      hmatch, hgc, hd, hint, hlength.trans hdispl.symm⟩
  exact Analysis.ae_horizontal_length_eq_width ha hb hA hB T h_holomorphic
    h_bijective e h_extension h_zero h_right h_top_right h_top_left

end HolomorphicAnosov.Analysis.MarkedRectangleHorizontalPreservation

