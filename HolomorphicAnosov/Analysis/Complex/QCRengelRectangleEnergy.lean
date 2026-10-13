import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import HolomorphicAnosov.Analysis.QCSignedDistortionModulusRectangleConformalModel
import HolomorphicAnosov.Analysis.Complex.QCRengelIntervalEnergy
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Rengel's rectangle energy estimate

Source: Lehto–Virtanen, *Quasiconformal mappings in the plane* (1973), Chapter I,
§4.3, pp. 22–23.  For each vertical segment of a rectangle, the endpoint
separation is bounded by the integral of the derivative along that segment;
Cauchy–Schwarz gives the square-energy lower bound.  Integrating those bounds
over the horizontal coordinate and applying Tonelli yields the displayed
rectangle estimate.  The proof uses the interval provider
`analysis.qc_rengel_interval_energy_g11`, Mathlib Tonelli, and its
volume-preserving complex-coordinate equivalence.

The displayed source calculation uses the inverse canonical map and a rectangle
of height one. This theorem isolates its energy estimate for arbitrary positive
height and uses endpoint separation as the lower bound for each vertical image
arc. The same proof needs only continuity on the closed rectangle and
holomorphicity on its interior. Injectivity is needed later to identify energy
with image area, and is not needed in this energy estimate. No boundary
differentiability or finite-energy assumption is introduced.
-/

open Set MeasureTheory
open scoped ENNReal
open HolomorphicAnosov.Analysis.MarkedRectangle

namespace HolomorphicAnosov

/-- Lehto–Virtanen I §4.3, pp. 22–23, Rengel rectangle energy estimate.

Fix `x ∈ (0,w)` and put `g(y) = f(x + iy)`. The vertical affine map sends
`[0,h]` into the closed rectangle, so `g` is continuous there. Holomorphicity
makes `f` smooth on the open rectangle. Restriction of scalars to the reals
and composition with the affine map give real `C¹` regularity of `g` on `(0,h)`.
At every interior point the scalar chain rule gives
`deriv g y = deriv f (x + iy) * I`, whose norm equals `‖deriv f (x + iy)‖`.
Apply `qc_rengel_interval_energy` to `g`. The endpoint assumption and `s ≥ 0`
bound `ofReal(s²)` by its squared endpoint edistance, hence by `ofReal(h)`
times the vertical derivative energy. The total derivative is measurable, so
its squared extended norm is measurable. Integrate the slice inequality in `x`,
pull out the finite factor `ofReal(h)`, and evaluate the integral of the constant
as `ofReal(w * s²)`. Tonelli identifies the iterated integral with the product
integral. The inverse volume-preserving complex-coordinate equivalence transports
this to the complex rectangle: `⟨x,y⟩` equals `x + iy`, and `OpenRectangle` is the
complex product of the two open intervals. This gives precisely the stated inequality. The interval
provider uses continuity for the endpoints, so no endpoint derivative is needed;
all integrals are lower integrals, permitting infinite energy.
-/
theorem qc_rengel_rectangle_energy {w h s : ℝ} {f : ℂ → ℂ}
    (_hw : 0 < w) (hh : 0 < h) (hs : 0 ≤ s)
    (hc : ContinuousOn f (ClosedRectangle w h))
    (hf : DifferentiableOn ℂ f (OpenRectangle w h))
    (hsep : ∀ x ∈ Ioo 0 w, s ≤ dist (f (x : ℂ)) (f ((x : ℂ) + h * Complex.I))) :
    ENNReal.ofReal (w * s ^ 2) ≤ ENNReal.ofReal h *
      ∫⁻ z in OpenRectangle w h, ‖deriv f z‖ₑ ^ 2 := by
  have hslice (x : ℝ) (hx : x ∈ Ioo 0 w) : ENNReal.ofReal (s ^ 2) ≤
      ENNReal.ofReal h * ∫⁻ y in Ioo 0 h, ‖deriv f (⟨x,y⟩ : ℂ)‖ₑ ^ 2 := by
    let g : ℝ → ℂ := fun y ↦ f ((x : ℂ) + y * Complex.I)
    have hmap : MapsTo (fun y : ℝ ↦ (x : ℂ) + y * Complex.I) (Ioo 0 h)
        (Complex.reProdIm (Ioo 0 w) (Ioo 0 h)) := by
      intro y hy
      simpa [Complex.reProdIm] using And.intro hx hy
    have hmapc : MapsTo (fun y : ℝ ↦ (x : ℂ) + y * Complex.I) (Icc 0 h)
        (Complex.reProdIm (Icc 0 w) (Icc 0 h)) := by
      intro y hy
      simpa [Complex.reProdIm] using And.intro (And.intro hx.1.le hx.2.le) hy
    have hgc : ContinuousOn g (Icc 0 h) := hc.comp
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn) hmapc
    have hgd : ContDiffOn ℝ 1 g (Ioo 0 h) :=
      ((hf.contDiffOn (isOpen_Ioo.reProdIm isOpen_Ioo)).restrict_scalars ℝ).comp
        ((contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).contDiffOn) hmap
    have hd (y : ℝ) (hy : y ∈ Ioo 0 h) :
        deriv g y = deriv f ((x : ℂ) + y * Complex.I) * Complex.I := by
      have hfd := (hf.differentiableAt
        ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds (hmap hy))).hasDerivAt
      have ha : HasDerivAt (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add (x : ℂ)
      simpa only [g, Function.comp_def, smul_eq_mul, mul_comm] using (hfd.scomp y ha).deriv
    have he := HolomorphicAnosov.qc_rengel_interval_energy hh hgc hgd
    have hdist : ENNReal.ofReal (s ^ 2) ≤ edist (g 0) (g h) ^ 2 := by
      rw [edist_dist, ENNReal.ofReal_pow hs]
      apply pow_le_pow_left'
      exact ENNReal.ofReal_le_ofReal (by simpa [g] using hsep x hx)
    have hint : (∫⁻ y in Ioo 0 h, ‖deriv g y‖ₑ ^ 2) =
        ∫⁻ y in Ioo 0 h, ‖deriv f (⟨x,y⟩ : ℂ)‖ₑ ^ 2 := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro y hy
      dsimp only
      rw [hd y hy]
      simp [enorm_eq_nnnorm, ← Complex.re_add_im (⟨x,y⟩ : ℂ)]
    simpa only [sub_zero, hint] using hdist.trans he
  let ρ : ℂ → ℝ≥0∞ := fun z ↦ ‖deriv f z‖ₑ ^ 2
  have hρ : Measurable ρ := (measurable_deriv f).enorm.pow_const 2
  have hcoord := Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd
  have htransport := hcoord.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding ρ
    (Complex.reProdIm (Ioo 0 w) (Ioo 0 h))
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹'
      Complex.reProdIm (Ioo 0 w) (Ioo 0 h) = Ioo 0 w ×ˢ Ioo 0 h := by
    ext p
    rfl
  rw [hpre] at htransport
  simp only [Complex.measurableEquivRealProd_symm_apply] at htransport
  have hm : Measurable (fun p : ℝ × ℝ ↦ ρ (⟨p.1,p.2⟩ : ℂ)) :=
    hρ.comp Complex.measurableEquivRealProd.symm.measurable
  have ht := setLIntegral_prod (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (s := Ioo 0 w) (t := Ioo 0 h)
    (fun p : ℝ × ℝ ↦ ρ (⟨p.1,p.2⟩ : ℂ)) hm.aemeasurable
  have hle := setLIntegral_mono' (μ := (volume : Measure ℝ)) measurableSet_Ioo hslice
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hle
  change ENNReal.ofReal (s ^ 2) * ENNReal.ofReal w ≤
    ENNReal.ofReal h * ∫⁻ x in Ioo 0 w, ∫⁻ y in Ioo 0 h, ρ (⟨x,y⟩ : ℂ) at hle
  rw [← ht] at hle
  change ENNReal.ofReal (s ^ 2) * ENNReal.ofReal w ≤
    ENNReal.ofReal h * ∫⁻ z in Ioo 0 w ×ˢ Ioo 0 h,
      ρ (⟨z.1,z.2⟩ : ℂ) ∂(volume : Measure (ℝ × ℝ)) at hle
  rw [htransport] at hle
  simpa only [OpenRectangle, ρ, ENNReal.ofReal_mul' (sq_nonneg s), mul_comm] using hle

end HolomorphicAnosov

