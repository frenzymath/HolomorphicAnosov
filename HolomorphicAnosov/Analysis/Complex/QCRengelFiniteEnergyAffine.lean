import HolomorphicAnosov.Analysis.Complex.QCRengelEnergyEqualityAffine
import HolomorphicAnosov.Analysis.Complex.QCRengelRectangleEnergy
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Set MeasureTheory
open scoped ENNReal
open HolomorphicAnosov.Analysis.MarkedRectangle
namespace HolomorphicAnosov

set_option maxHeartbeats 400000 in
/-- Lehto–Virtanen I.§4.3 p.23, equality in Rengel's inequality.
The finite total lower integral gives integrable squared speeds by Tonelli.
The continuous endpoint values bound the integral of speed on each good slice.
Fubini identifies the real total energy, and the existing equality theorem
makes the map affine. No derivative on the boundary is required. -/
theorem qc_rengel_finite_energy_affine {w : ℝ} {f : ℂ → ℂ}
    (hw : 0 < w) (hc : ContinuousOn f (ClosedRectangle w 1))
    (hf : DifferentiableOn ℂ f (OpenRectangle w 1))
    (hsep : ∀ x ∈ Ioo 0 w, 1 ≤ dist (f (x : ℂ)) (f ((x : ℂ) + Complex.I)))
    (he : (∫⁻ z in OpenRectangle w 1, ‖deriv f z‖ₑ ^ 2) = ENNReal.ofReal w) :
    ∃ c d : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ OpenRectangle w 1, f z = c * z + d := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 w)
  let ν : Measure ℝ := volume.restrict (Ioo 0 1)
  let e : ℝ × ℝ → ℝ := fun p ↦ ‖deriv f (⟨p.1,p.2⟩ : ℂ)‖ ^ 2
  have hem : Measurable e := ((measurable_deriv f).comp
    Complex.measurableEquivRealProd.symm.measurable).norm.pow_const 2
  have hcoord := Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd
  have ht := hcoord.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun z ↦ ‖deriv f z‖ₑ ^ 2) (OpenRectangle w 1)
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' OpenRectangle w 1 =
      Ioo 0 w ×ˢ Ioo 0 1 := by ext p; rfl
  rw [hpre] at ht
  have he' : (∫⁻ p, ENNReal.ofReal (e p) ∂μ.prod ν) = ENNReal.ofReal w := by
    rw [show μ.prod ν = (volume : Measure (ℝ × ℝ)).restrict (Ioo 0 w ×ˢ Ioo 0 1) by
      exact Measure.prod_restrict _ _]
    simpa only [e, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      Complex.measurableEquivRealProd_symm_apply] using ht.trans he
  have hei : Integrable e (μ.prod ν) := by
    refine ⟨hem.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hnon : ∀ p, 0 ≤ e p := fun p ↦ sq_nonneg _
    simpa only [Real.enorm_eq_ofReal (hnon _), he'] using ENNReal.ofReal_lt_top
  have hLp : ∀ᵐ x ∂μ,
      MemLp (fun y : ℝ ↦ ‖deriv f (⟨x,y⟩ : ℂ)‖) 2 ν := by
    filter_upwards [hei.prod_right_ae] with x hx
    apply (memLp_two_iff_integrable_sq
      (((measurable_deriv f).comp (Complex.measurableEquivRealProd.symm.measurable.comp
        (measurable_const.prodMk measurable_id))).norm.aestronglyMeasurable)).mpr
    exact hx
  have hLength : ∀ᵐ x ∂μ, 1 ≤ ∫ y, ‖deriv f (⟨x,y⟩ : ℂ)‖ ∂ν := by
    filter_upwards [hLp, ae_restrict_mem measurableSet_Ioo] with x hx hxw
    let g : ℝ → ℂ := fun y ↦ f ((x : ℂ) + y * Complex.I)
    have hmap : MapsTo (fun y : ℝ ↦ (x : ℂ) + y * Complex.I) (Ioo 0 1)
        (OpenRectangle w 1) := by
      intro y hy; simpa [OpenRectangle, Complex.reProdIm] using And.intro hxw hy
    have hmapc : MapsTo (fun y : ℝ ↦ (x : ℂ) + y * Complex.I) (Icc 0 1)
        (ClosedRectangle w 1) := by
      intro y hy
      simpa [ClosedRectangle, Complex.reProdIm] using And.intro
        (And.intro hxw.1.le hxw.2.le) hy
    have hgc : ContinuousOn g (Icc 0 1) := hc.comp
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn) hmapc
    have hgd : ContDiffOn ℝ 1 g (Ioo 0 1) :=
      ((hf.contDiffOn (isOpen_Ioo.reProdIm isOpen_Ioo)).restrict_scalars ℝ).comp
        ((contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).contDiffOn) hmap
    have hd (y : ℝ) (hy : y ∈ Ioo 0 1) :
        deriv g y = deriv f ((x : ℂ) + y * Complex.I) * Complex.I := by
      have hfd := (hf.differentiableAt
        ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds (hmap hy))).hasDerivAt
      have ha : HasDerivAt (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add (x : ℂ)
      simpa only [g, Function.comp_def, smul_eq_mul, mul_comm] using (hfd.scomp y ha).deriv
    have hc' : ContinuousOn g (closure (Ioo (0 : ℝ) 1)) := by
      simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hgc
    have hi (a : ℝ) (ha : a ∈ Ioo 0 1) (b : ℝ) (hb : b ∈ Ioo 0 1) :
        edist (g a) (g b) ≤ ∫⁻ t in Ioo 0 1, ‖deriv g t‖ₑ :=
      (eVariationOn.edist_le g ha hb).trans
        (Analysis.eVariationOn_Ioo_le_lintegral_deriv_of_contDiffOn hgd)
    have hleft (b : ℝ) (hb : b ∈ Ioo 0 1) :
        edist (g 0) (g b) ≤ ∫⁻ t in Ioo 0 1, ‖deriv g t‖ₑ :=
      le_on_closure (fun a ha ↦ hi a ha b hb)
        (continuous_edist.comp_continuousOn (hc'.prodMk continuousOn_const))
        continuousOn_const (by simp)
    have hend : edist (g 0) (g 1) ≤ ∫⁻ t in Ioo 0 1, ‖deriv g t‖ₑ :=
      le_on_closure hleft
        (continuous_edist.comp_continuousOn (continuousOn_const.prodMk hc'))
        continuousOn_const (by simp)
    have hn : (∫⁻ t in Ioo 0 1, ‖deriv g t‖ₑ) =
        ∫⁻ t, ENNReal.ofReal ‖deriv f (⟨x,t⟩ : ℂ)‖ ∂ν := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht; dsimp only; rw [hd t ht]
      simp [enorm_eq_nnnorm, ← Complex.re_add_im (⟨x,t⟩ : ℂ)]
    rw [hn, ← ofReal_integral_eq_lintegral_ofReal (hx.integrable (by norm_num))
      (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))] at hend
    have hsep' : ENNReal.ofReal 1 ≤ edist (g 0) (g 1) := by
      simpa [g, edist_dist] using ENNReal.ofReal_le_ofReal (hsep x hxw)
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ ↦ norm_nonneg _))).mp
      (hsep'.trans hend)
  apply qc_rengel_energy_equality_affine hw (by norm_num) hf hLp hLength
    hei.integral_prod_left
  rw [← integral_prod e hei]
  have hreal : (∫ p, e p ∂μ.prod ν) =
      (∫⁻ p, ENNReal.ofReal (e p) ∂μ.prod ν).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun p ↦ sq_nonneg (‖deriv f (⟨p.1,p.2⟩ : ℂ)‖)))
      hem.aestronglyMeasurable
  rw [hreal, he']
  simp [hw.le]


end HolomorphicAnosov
