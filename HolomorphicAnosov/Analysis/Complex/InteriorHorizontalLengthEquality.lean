import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Horizontal length equality with derivatives only in the open interval

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed p.343, equality in the horizontal length bound.
The endpoint regularity is the one used in Lehto–Virtanen (1973), I.Theorem 3.1,
pp.18–19: continuity at endpoints and an integrable interior derivative suffice.
-/

namespace HolomorphicAnosov.Analysis.Complex

open Set MeasureTheory

/-- A continuous complex curve with integrable interior derivative has constant
imaginary part if its length equals its real endpoint displacement.

Source: the single-curve detail in Farb–Margalit Version 5.0, §11.5 Theorem 11.10,
printed p.343. The following proof expands the omitted equality argument.

Proof: Split the interval at any x. The fundamental theorem and the norm bound
for integrals bound each subcurve's endpoint distance by its integral of speed.
Each real endpoint displacement is at most the corresponding distance. The sum
of the two integrals of speed is the whole length, and the two real displacements
sum to the whole real displacement. The assumed equality forces equality in
each subcurve's distance bound. In particular the distance from g(a) to g(x)
equals its real displacement. The complex norm-square identity makes its
imaginary displacement zero. Every g(x) therefore has imaginary part Im g(a).
This proof requires no derivative or derivative limit at either endpoint.
-/
theorem im_eq_of_interior_length_eq_re_sub {a b : ℝ}
    {g g' : ℝ → ℂ}
    (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hint : IntervalIntegrable g' volume a b)
    (hlen : (∫ x in a..b, ‖g' x‖) = (g b).re - (g a).re) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (g x).im = (g y).im := by
  have hbase (x : ℝ) (hx : x ∈ Icc a b) : (g x).im = (g a).im := by
    have hlint := hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx))
    have hrint := hint.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hx) right_mem_uIcc)
    have hl := intervalIntegral.norm_integral_le_integral_norm (f := g') (μ := volume) hx.1
    have hr := intervalIntegral.norm_integral_le_integral_norm (f := g') (μ := volume) hx.2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (hcont.mono (Icc_subset_Icc le_rfl hx.2))
      (fun t ht ↦ hderiv t ⟨ht.1, ht.2.trans_le hx.2⟩) hlint] at hl
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.2
      (hcont.mono (Icc_subset_Icc hx.1 le_rfl))
      (fun t ht ↦ hderiv t ⟨hx.1.trans_lt ht.1, ht.2⟩) hrint] at hr
    have hadd := intervalIntegral.integral_add_adjacent_intervals hlint.norm hrint.norm
    rw [hlen] at hadd
    have hleftre := Complex.re_le_norm (g x - g a)
    have hrightre := Complex.re_le_norm (g b - g x)
    simp only [Complex.sub_re] at hleftre hrightre
    have hnorm : (g x - g a).re = ‖g x - g a‖ := by
      simp only [Complex.sub_re]
      linarith
    have hsq := Complex.sq_norm_sub_sq_re (g x - g a)
    rw [← hnorm, sub_self] at hsq
    have him : (g x - g a).im = 0 := by nlinarith [sq_nonneg (g x - g a).im]
    simpa only [Complex.sub_im, sub_eq_zero] using him
  intro x hx y hy
  exact (hbase x hx).trans (hbase y hy).symm

end HolomorphicAnosov.Analysis.Complex

