import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Divided-difference integral on a rectangle

Source: Ahlfors, Complex Analysis, third edition, IV §1.4, Theorem 3,
pp.111–112; Conway VIII Proposition 1.1, pp.195–196.
DAG node: `analysis.rectangle_divided_difference_integral_g19`.
The agent-written proof uses Mathlib removable singularities in place of the
published shrinking-square argument, preserving the literal boundary quotient.
-/

namespace HolomorphicAnosov.Analysis.Complex

open Set
open scoped Interval Topology _root_.Topology
open Filter

/-- The four-side divided-difference integral vanishes when the evaluation point is
strictly inside the rectangle.

Source: Ahlfors IV §1.4, Theorem 3, pp.111–112; Conway VIII Proposition 1.1,
pp.195–196. Agent-written implementation of the exceptional-point step:
fill the divided difference at z by f′(z). Mathlib makes this function
holomorphic on U, so rectangle Cauchy applies after restriction. The imaginary
coordinates on horizontal sides and real coordinates on vertical sides differ
strictly from those of z. Hence the filled function equals the original
quotient everywhere on each side. Substitute these identities, with tangent
factor i on vertical sides, into the zero boundary integral. -/
theorem rectangle_divided_difference_integral_eq_zero
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (a b z : ℂ)
    (hR : ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) ⊆ U)
    (har : a.re < z.re) (hrb : z.re < b.re)
    (hai : a.im < z.im) (hib : z.im < b.im) :
    (∫ x : ℝ in a.re..b.re, (f (x + a.im * Complex.I) - f z) /
      (x + a.im * Complex.I - z)) -
    (∫ x : ℝ in a.re..b.re, (f (x + b.im * Complex.I) - f z) /
      (x + b.im * Complex.I - z)) +
    Complex.I * (∫ y : ℝ in a.im..b.im, (f (b.re + y * Complex.I) - f z) /
      (b.re + y * Complex.I - z)) -
    Complex.I * (∫ y : ℝ in a.im..b.im, (f (a.re + y * Complex.I) - f z) /
      (a.re + y * Complex.I - z)) = 0 := by
  have hzR : z ∈ ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
    simp only [Complex.mem_reProdIm, mem_uIcc]
    exact ⟨Or.inl ⟨le_of_lt har, le_of_lt hrb⟩, Or.inl ⟨le_of_lt hai, le_of_lt hib⟩⟩
  have hzn : U ∈ 𝓝 z := hU.mem_nhds (hR hzR)
  have hdsU : DifferentiableOn ℂ (dslope f z) U :=
    (Complex.differentiableOn_dslope hzn).mpr hf
  have hds : DifferentiableOn ℂ (dslope f z)
      ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := hdsU.mono hR
  have hdscont : ContinuousOn (dslope f z)
      ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := hds.continuousOn
  have hopen : DifferentiableOn ℂ (dslope f z)
      (Ioo (min a.re b.re) (max a.re b.re) ×ℂ
        Ioo (min a.im b.im) (max a.im b.im)) := by
    exact hds.mono (by
      intro w hw
      simp only [Complex.mem_reProdIm, mem_Ioo] at hw ⊢
      exact ⟨⟨le_of_lt hw.1.1, le_of_lt hw.1.2⟩,
        ⟨le_of_lt hw.2.1, le_of_lt hw.2.2⟩⟩)
  have hzero := _root_.Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (dslope f z) a b hdscont hopen
  have hbottom : ∀ x : ℝ, x + a.im * Complex.I ≠ z := by
    intro x heq
    have him := congrArg Complex.im heq
    norm_num at him
    linarith [hai]
  have htop : ∀ x : ℝ, x + b.im * Complex.I ≠ z := by
    intro x heq
    have him := congrArg Complex.im heq
    norm_num at him
    linarith [hib]
  have hright : ∀ y : ℝ, b.re + y * Complex.I ≠ z := by
    intro y heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith [hrb]
  have hleft : ∀ y : ℝ, a.re + y * Complex.I ≠ z := by
    intro y heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith [har]
  simp only [dslope_of_ne _ (hbottom _), dslope_of_ne _ (htop _),
    dslope_of_ne _ (hright _), dslope_of_ne _ (hleft _)] at hzero
  simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using hzero


end HolomorphicAnosov.Analysis.Complex
