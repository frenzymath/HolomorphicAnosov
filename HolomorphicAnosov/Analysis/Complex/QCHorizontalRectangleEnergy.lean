import HolomorphicAnosov.Analysis.Complex.QCRengelIntervalEnergy
import HolomorphicAnosov.Analysis.QCSignedDistortionModulusRectangleConformalModel
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Horizontal energy of a regular rectangle map

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973), I.Theorem 3.1,
pp.18–19, the Schwarz and horizontal-length estimates following equation (3.4).
DAG node: `analysis.qc_horizontal_rectangle_energy_g18`.
-/

open Set MeasureTheory
open scoped ENNReal
open HolomorphicAnosov.Analysis.MarkedRectangle

namespace HolomorphicAnosov

/-- For a real C¹ rectangle map with continuous boundary values, horizontal endpoint
separation bounds its horizontal derivative energy from below.

Source: Lehto–Virtanen I.Theorem 3.1, pp.18–19. At each interior height, restrict to
the horizontal segment, whose derivative is `fderiv ℝ f z 1`. The interval energy
inequality bounds squared endpoint displacement by width times slice energy. Integrate
over the height, use Tonelli, and transport Lebesgue measure through complex coordinates.
No holomorphicity, injectivity, endpoint derivatives, or finite-energy hypothesis is used.
-/
theorem qc_horizontal_rectangle_energy {w h s : ℝ} {f : ℂ → ℂ}
    (hw : 0 < w) (hs : 0 ≤ s)
    (hc : ContinuousOn f (ClosedRectangle w h))
    (hf : ContDiffOn ℝ 1 f (OpenRectangle w h))
    (hsep : ∀ y ∈ Ioo 0 h,
      s ≤ dist (f (y * Complex.I)) (f ((w : ℂ) + y * Complex.I))) :
    ENNReal.ofReal (h * s ^ 2) ≤ ENNReal.ofReal w *
      ∫⁻ z in OpenRectangle w h, ‖fderiv ℝ f z 1‖ₑ ^ 2 := by
  have hslice (y : ℝ) (hy : y ∈ Ioo 0 h) : ENNReal.ofReal (s ^ 2) ≤
      ENNReal.ofReal w * ∫⁻ x in Ioo 0 w, ‖fderiv ℝ f (⟨x,y⟩ : ℂ) 1‖ₑ ^ 2 := by
    let g : ℝ → ℂ := fun x ↦ f ((x : ℂ) + y * Complex.I)
    have hmap : MapsTo (fun x : ℝ ↦ (x : ℂ) + y * Complex.I) (Ioo 0 w)
        (OpenRectangle w h) := by
      intro x hx
      simpa [OpenRectangle, Complex.reProdIm] using And.intro hx hy
    have hmapc : MapsTo (fun x : ℝ ↦ (x : ℂ) + y * Complex.I) (Icc 0 w)
        (ClosedRectangle w h) := by
      intro x hx
      simpa [ClosedRectangle, Complex.reProdIm] using And.intro hx ⟨hy.1.le, hy.2.le⟩
    have hgc : ContinuousOn g (Icc 0 w) :=
      hc.comp ((Complex.continuous_ofReal.add continuous_const).continuousOn) hmapc
    have hgd : ContDiffOn ℝ 1 g (Ioo 0 w) :=
      hf.comp ((Complex.ofRealCLM.contDiff.add contDiff_const).contDiffOn) hmap
    have hd (x : ℝ) (hx : x ∈ Ioo 0 w) :
        deriv g x = fderiv ℝ f ((x : ℂ) + y * Complex.I) 1 := by
      have hfd := (hf.differentiableOn (by norm_num)).differentiableAt
        ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds (hmap hx))
      simpa [g, Function.comp_def] using
        (hfd.hasFDerivAt.comp_hasDerivAt x
          (Complex.ofRealCLM.hasDerivAt.add_const (y * Complex.I))).deriv
    have he := qc_rengel_interval_energy hw hgc hgd
    have hdist : ENNReal.ofReal (s ^ 2) ≤ edist (g 0) (g w) ^ 2 := by
      rw [edist_dist, ENNReal.ofReal_pow hs]
      apply pow_le_pow_left'
      exact ENNReal.ofReal_le_ofReal (by simpa [g] using hsep y hy)
    have hint : (∫⁻ x in Ioo 0 w, ‖deriv g x‖ₑ ^ 2) =
        ∫⁻ x in Ioo 0 w, ‖fderiv ℝ f (⟨x,y⟩ : ℂ) 1‖ₑ ^ 2 := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [hd x hx]
      simp [← Complex.re_add_im (⟨x,y⟩ : ℂ)]
    simpa only [sub_zero, hint] using hdist.trans he
  let ρ : ℂ → ℝ≥0∞ := fun z ↦ ‖fderiv ℝ f z 1‖ₑ ^ 2
  have hρ : Measurable ρ := (measurable_fderiv_apply_const ℝ f 1).enorm.pow_const 2
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
  have ht := setLIntegral_prod_symm (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (s := Ioo 0 w) (t := Ioo 0 h)
    (fun p : ℝ × ℝ ↦ ρ (⟨p.1,p.2⟩ : ℂ)) hm.aemeasurable
  have hle := setLIntegral_mono' (μ := (volume : Measure ℝ)) measurableSet_Ioo hslice
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hle
  change ENNReal.ofReal (s ^ 2) * ENNReal.ofReal h ≤
    ENNReal.ofReal w * ∫⁻ y in Ioo 0 h, ∫⁻ x in Ioo 0 w, ρ (⟨x,y⟩ : ℂ) at hle
  rw [← ht] at hle
  change ENNReal.ofReal (s ^ 2) * ENNReal.ofReal h ≤
    ENNReal.ofReal w * ∫⁻ z in Ioo 0 w ×ˢ Ioo 0 h,
      ρ (⟨z.1,z.2⟩ : ℂ) ∂(volume : Measure (ℝ × ℝ)) at hle
  rw [htransport] at hle
  simpa only [OpenRectangle, ρ, ENNReal.ofReal_mul' (sq_nonneg s), mul_comm] using hle

end HolomorphicAnosov
