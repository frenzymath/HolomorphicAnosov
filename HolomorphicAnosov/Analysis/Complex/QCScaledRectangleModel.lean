import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulus
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

namespace HolomorphicAnosov
open Set Filter _root_.Topology Analysis.MarkedRectangle

/-- Centered strict scaling of a conformal rectangle gives an inner marked
quadrilateral with the same modulus and its literal closed parametrization.
Source: Lehto--Virtanen (1973), I.Lemma 4.4 p.27, inner approximation, using
rectangles in place of concentric disks. The affine map `S` maps the whole
closed rectangle into the open rectangle. Its composition with `F` is
injective and holomorphic, with inverse obtained by applying `Fi` and `S⁻¹`.
The compact closed image is the closure of the open image by continuity and
density. This gives its closure homeomorphism, and evaluating at the four
corners gives the marks. The parameter rectangle keeps side ratio `a/b`. -/
theorem qc_scaled_rectangle_model {Q : Set ℂ} {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hr1 : r < 1)
    (F Fi : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (OpenRectangle a b))
    (hFi : DifferentiableOn ℂ Fi Q)
    (hbij : BijOn F (OpenRectangle a b) Q)
    (hFiF : ∀ z ∈ OpenRectangle a b, Fi (F z) = z) :
    let S : ℂ → ℂ := fun z ↦ (r : ℂ) * z + (1 - r : ℝ) *
      ((a : ℂ) + b * Complex.I) / 2
    let P := (F ∘ S) '' OpenRectangle a b
    IsCompact (closure P) ∧ closure P ⊆ Q ∧
      HasMarkedConformalModulus P (fun i ↦ F (S (RectangleCorner a b i))) (a / b) ∧
      ∃ e : ClosedRectangle a b ≃ₜ closure P,
        ∀ z : ClosedRectangle a b, (e z : ℂ) = F (S z) := by
  dsimp only
  let S : ℂ → ℂ := fun z ↦ (r : ℂ) * z + (1 - r : ℝ) *
    ((a : ℂ) + b * Complex.I) / 2
  let Si : ℂ → ℂ := fun z ↦ (z - (1 - r : ℝ) *
    ((a : ℂ) + b * Complex.I) / 2) / r
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hSiS (z : ℂ) : Si (S z) = z := by
    dsimp [Si, S]
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hrC]
  have hSclosed : MapsTo S (ClosedRectangle a b) (OpenRectangle a b) := by
    intro z hz
    rcases hz with ⟨hx, hy⟩
    change (0 < (S z).re ∧ (S z).re < a) ∧ (0 < (S z).im ∧ (S z).im < b)
    simp only [S, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_re, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.mul_im, Complex.div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one]
    constructor <;> constructor <;> nlinarith [mul_nonneg hr.le hx.1,
      mul_nonneg hr.le hy.1, mul_le_mul_of_nonneg_left hx.2 hr.le,
      mul_le_mul_of_nonneg_left hy.2 hr.le]
  have hRsub : OpenRectangle a b ⊆ ClosedRectangle a b := by
    rw [← RectangleModelPreparation.closure_openRectangle ha hb]
    exact subset_closure
  have hSopen := hSclosed.mono_left hRsub
  have hS : Differentiable ℂ S := by
    exact ((differentiable_const _).mul differentiable_id).add_const _
  have hSi : Differentiable ℂ Si :=
    (differentiable_id.sub_const _).div_const _
  let P := (F ∘ S) '' OpenRectangle a b
  have hPsub : P ⊆ Q := by
    rintro w ⟨z, hz, rfl⟩
    exact hbij.mapsTo (hSopen hz)
  have hc : ContinuousOn (F ∘ S) (ClosedRectangle a b) :=
    hF.continuousOn.comp hS.continuous.continuousOn hSclosed
  have hcompactR : IsCompact (ClosedRectangle a b) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcompact := hcompactR.image_of_continuousOn hc
  have heq : closure P = (F ∘ S) '' ClosedRectangle a b := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono hRsub) hcompact.isClosed
    · have hc' : ContinuousOn (F ∘ S) (closure (OpenRectangle a b)) := by
        rwa [RectangleModelPreparation.closure_openRectangle ha hb]
      simpa only [RectangleModelPreparation.closure_openRectangle ha hb] using hc'.image_closure
  have hcompactP : IsCompact (closure P) := heq.symm ▸ hcompact
  have hclsub : closure P ⊆ Q := by
    rw [heq]
    rintro w ⟨z, hz, rfl⟩
    exact hbij.mapsTo (hSclosed hz)
  have : CompactSpace (ClosedRectangle a b) := isCompact_iff_compactSpace.mp hcompactR
  let G : ClosedRectangle a b → ℂ := fun z ↦ F (S z)
  have hGc : Continuous G := hc.domRestrict
  have hGinj : Function.Injective G := by
    intro z w hzw
    apply Subtype.ext
    have he := hbij.injOn (hSclosed z.property) (hSclosed w.property) hzw
    exact (hSiS z).symm.trans ((congrArg Si he).trans (hSiS w))
  have hrange : range G = closure P := by
    rw [heq]
    ext w
    simp only [mem_range, mem_image, G, Function.comp_apply]
    exact ⟨fun ⟨z, hz⟩ ↦ ⟨z, z.property, hz⟩, fun ⟨z, hz, he⟩ ↦ ⟨⟨z, hz⟩, he⟩⟩
  let e := (hGc.isClosedEmbedding hGinj).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)
  have he (z : ClosedRectangle a b) : (e z : ℂ) = F (S z) := rfl
  have hF' : DifferentiableOn ℂ (F ∘ S) (OpenRectangle a b) :=
    hF.comp hS.differentiableOn hSopen
  have hFi' : DifferentiableOn ℂ (Si ∘ Fi) P :=
    hSi.differentiableOn.comp (hFi.mono hPsub) (mapsTo_univ _ _)
  have hFiF' (z : ℂ) (hz : z ∈ OpenRectangle a b) : Si (Fi (F (S z))) = z := by
    rw [hFiF _ (hSopen hz), hSiS]
  have hbij' : BijOn (F ∘ S) (OpenRectangle a b) P := by
    refine ⟨mapsTo_image _ _, ?_, surjOn_image _ _⟩
    intro z hz w hw he
    exact (hFiF' z hz).symm.trans ((congrArg (Si ∘ Fi) he).trans (hFiF' w hw))
  refine ⟨hcompactP, hclsub, ?_, e, he⟩
  refine ⟨a, b, ha, hb, rfl, F ∘ S, Si ∘ Fi, hF', hFi', hbij', ?_, ?_, ?_,
    e, fun z _ ↦ he z, ?_⟩
  · rintro w ⟨z, hz, rfl⟩
    change Si (Fi (F (S z))) ∈ OpenRectangle a b
    rw [hFiF' z hz]
    exact hz
  · exact hFiF'
  · rintro w ⟨z, hz, rfl⟩
    change F (S (Si (Fi (F (S z))))) = F (S z)
    rw [hFiF' z hz]
  · intro i z hz
    rw [he, hz]


/-- Uniform continuity of a continuous closed rectangle map along centered
scalings whose ratios tend to one. This is the compact continuous-family
criterion for uniform convergence. -/
lemma qc_rectangle_center_scaling_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℂ → ℂ) (hf : ContinuousOn f (ClosedRectangle a b))
    (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto r atTop (𝓝 1)) :
    TendstoUniformlyOn
      (fun n z ↦ f ((r n : ℂ) * z + (1 - r n : ℝ) *
        ((a : ℂ) + b * Complex.I) / 2)) f atTop (ClosedRectangle a b) := by
  let S (t : unitInterval) (z : ClosedRectangle a b) : ℂ :=
    (t : ℂ) * z + (1 - (t : ℝ) : ℝ) * ((a : ℂ) + b * Complex.I) / 2
  have hS (t : unitInterval) (z : ClosedRectangle a b) : S t z ∈ ClosedRectangle a b := by
    have hx := z.property.1
    have hy := z.property.2
    have ht := t.property
    change (0 ≤ (S t z).re ∧ (S t z).re ≤ a) ∧
      (0 ≤ (S t z).im ∧ (S t z).im ≤ b)
    simp only [S, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_re, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.mul_im, Complex.div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one]
    constructor <;> constructor <;> nlinarith [mul_nonneg ht.1 hx.1,
      mul_nonneg ht.1 hy.1, mul_le_mul_of_nonneg_left hx.2 ht.1,
      mul_le_mul_of_nonneg_left hy.2 ht.1,
      mul_nonneg (sub_nonneg.mpr ht.2) ha.le,
      mul_nonneg (sub_nonneg.mpr ht.2) hb.le]
  have : CompactSpace (ClosedRectangle a b) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.reProdIm isCompact_Icc)
  let G : unitInterval → ClosedRectangle a b → ℂ := fun t z ↦ f (S t z)
  have hG : Continuous ↿G := hf.comp_continuous (by dsimp [S]; fun_prop)
    (fun tz ↦ hS tz.1 tz.2)
  have htlim : Tendsto (fun n ↦ (⟨r n, hr n⟩ : unitInterval)) atTop (𝓝 1) :=
    tendsto_subtype_rng.mpr hlim
  have hu : TendstoUniformly (fun n ↦ G ⟨r n, hr n⟩) (G 1) atTop :=
    fun s hs ↦ htlim.eventually (Continuous.tendstoUniformly G hG 1 s hs)
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  simpa [G, S, Function.comp_def] using hu


/-- The centered inner models retain the original closed rectangle parameter:
their closed parametrizations converge uniformly to its given extension.
The source moduli are exactly constant. This packages the geometric information
needed by the image diagonal, rather than just existence of inner models. -/
theorem qc_scaled_rectangle_family {Q : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hmod : HasMarkedConformalModulus Q p m)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n < 1)
    (hlim : Tendsto r atTop (𝓝 1)) :
    ∃ (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
      (e : ClosedRectangle a b ≃ₜ closure Q)
      (P : ℕ → Set ℂ) (q : ℕ → Fin 4 → ℂ)
      (E : ∀ n, ClosedRectangle a b ≃ₜ closure (P n)),
      (∀ i, (e ⟨RectangleCorner a b i,
        RectangleModelPreparation.corner_mem ha hb i⟩ : ℂ) = p i) ∧
      (∀ z : ClosedRectangle a b, (e z : ℂ) ∈ Q ↔ (z : ℂ) ∈ OpenRectangle a b) ∧
      (∀ n, IsCompact (closure (P n)) ∧ closure (P n) ⊆ Q ∧
        HasMarkedConformalModulus (P n) (q n) m ∧
        (∀ i, (E n ⟨RectangleCorner a b i,
          RectangleModelPreparation.corner_mem ha hb i⟩ : ℂ) = q n i) ∧
        ∀ z : ClosedRectangle a b, (E n z : ℂ) ∈ P n ↔ (z : ℂ) ∈ OpenRectangle a b) ∧
      TendstoUniformly (fun n z ↦ (E n z : ℂ)) (fun z ↦ (e z : ℂ)) atTop := by
  classical
  obtain ⟨a, b, ha, hb, hm, F, Fi, hF, hFi, hbij, hmaps, hFiF, hFFi,
    e, he, hcorner⟩ := hmod
  let S : ℕ → ℂ → ℂ := fun n z ↦ (r n : ℂ) * z +
    (1 - r n : ℝ) * ((a : ℂ) + b * Complex.I) / 2
  let P : ℕ → Set ℂ := fun n ↦ (F ∘ S n) '' OpenRectangle a b
  let q : ℕ → Fin 4 → ℂ := fun n i ↦ F (S n (RectangleCorner a b i))
  have hmodel (n : ℕ) := qc_scaled_rectangle_model ha hb (hr n) (hr1 n)
    F Fi hF hFi hbij hFiF
  choose E hE using fun n ↦ (hmodel n).2.2.2
  have hRsub : OpenRectangle a b ⊆ ClosedRectangle a b := by
    rw [← RectangleModelPreparation.closure_openRectangle ha hb]
    exact subset_closure
  refine ⟨a, b, ha, hb, e, P, q, E, ?_, ?_, ?_, ?_⟩
  · exact fun i ↦ hcorner i _ rfl
  · intro z
    constructor
    · intro hz
      obtain ⟨w, hw, heq⟩ := hbij.surjOn hz
      have heq' : e z = e ⟨w, hRsub hw⟩ :=
        Subtype.ext (heq.symm.trans (he ⟨w, hRsub hw⟩ hw).symm)
      have hzw := congrArg Subtype.val (e.injective heq')
      exact hzw.symm ▸ hw
    · intro hz
      rw [he z hz]
      exact hbij.mapsTo hz
  · intro n
    refine ⟨(hmodel n).1, (hmodel n).2.1, ?_, ?_, ?_⟩
    · simpa only [hm] using (hmodel n).2.2.1
    · exact fun i ↦ hE n _
    · intro z
      constructor
      · rintro ⟨w, hw, heq⟩
        have heq' : E n z = E n ⟨w, hRsub hw⟩ :=
          Subtype.ext (heq.symm.trans (hE n ⟨w, hRsub hw⟩).symm)
        have hzw := congrArg Subtype.val ((E n).injective heq')
        exact hzw.symm ▸ hw
      · intro hz
        exact ⟨z, hz, (hE n z).symm⟩
  · let f : ℂ → ℂ := Function.extend Subtype.val
      (fun z : ClosedRectangle a b ↦ (e z : ℂ)) (fun _ ↦ 0)
    have hfe (z : ClosedRectangle a b) : f z = (e z : ℂ) :=
      Subtype.val_injective.extend_apply _ _ z
    have hfc : ContinuousOn f (ClosedRectangle a b) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_subtype_val.comp e.continuous).congr (fun z ↦ (hfe z).symm)
    have hS (n : ℕ) (z : ClosedRectangle a b) : S n z ∈ OpenRectangle a b := by
      have hx := z.property.1
      have hy := z.property.2
      change (0 < (S n z).re ∧ (S n z).re < a) ∧
        (0 < (S n z).im ∧ (S n z).im < b)
      simp only [S, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_ofNat_re, Complex.I_re, Complex.I_im, Complex.add_im,
        Complex.mul_im, Complex.div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one]
      constructor <;> constructor <;> nlinarith [hr n, hr1 n,
        mul_nonneg (hr n).le hx.1, mul_nonneg (hr n).le hy.1,
        mul_le_mul_of_nonneg_left hx.2 (hr n).le,
        mul_le_mul_of_nonneg_left hy.2 (hr n).le]
    have hR : OpenRectangle a b ⊆ ClosedRectangle a b := by
      rw [← RectangleModelPreparation.closure_openRectangle ha hb]
      exact subset_closure
    have hval (n : ℕ) (z : ClosedRectangle a b) : (E n z : ℂ) = f (S n z) := by
      rw [hE n z]
      exact (he ⟨S n z, hR (hS n z)⟩ (hS n z)).symm.trans
        (hfe ⟨S n z, hR (hS n z)⟩).symm
    have hu := qc_rectangle_center_scaling_tendsto ha hb f hfc r
      (fun n ↦ ⟨(hr n).le, (hr1 n).le⟩) hlim
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at hu
    have hu' : TendstoUniformly (fun n (z : ClosedRectangle a b) ↦ f (S n z))
        (fun z : ClosedRectangle a b ↦ f z) atTop := by
      simpa only [Function.comp_def] using hu
    simpa only [← hval, hfe] using hu' 


/-- A marked rectangle model identifies the region as a nonempty open
path-connected bounded set, and identifies its interior exactly under its
closure homeomorphism. These are the elementary geometric facts needed
when restricting or transporting that model. -/
lemma qc_marked_model_geometry {Q : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hmod : HasMarkedConformalModulus Q p m) (hcompact : IsCompact (closure Q)) :
    IsOpen Q ∧ IsPathConnected Q ∧ Bornology.IsBounded Q := by
  obtain ⟨a, b, ha, hb, hm, F, Fi, hF, hFi, hbij, hmaps, hFiF, hFFi,
    e, he, hcorner⟩ := hmod
  have hR : IsOpen (OpenRectangle a b) := RectangleModelPreparation.isOpen_openRectangle a b
  have hopen : IsOpen Q := by
    rw [← hbij.image_eq]
    exact lebl_scalar_open_image hR hF hbij.injOn hR subset_rfl
  have hconv : Convex ℝ (OpenRectangle a b) := by
    change Convex ℝ (Complex.equivRealProdLm.toLinearMap ⁻¹' (Ioo 0 a ×ˢ Ioo 0 b))
    exact ((convex_Ioo (0 : ℝ) a).prod (convex_Ioo (0 : ℝ) b)).linear_preimage
      Complex.equivRealProdLm.toLinearMap
  have hne : (OpenRectangle a b).Nonempty := by
    refine ⟨(a / 2 : ℝ) + (b / 2 : ℝ) * Complex.I, ?_⟩
    simp only [OpenRectangle, Complex.mem_reProdIm, mem_Ioo, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add]
    exact ⟨⟨half_pos ha, half_lt_self ha⟩, ⟨half_pos hb, half_lt_self hb⟩⟩
  refine ⟨hopen, ?_, hcompact.isBounded.subset subset_closure⟩
  rw [← hbij.image_eq]
  exact (hconv.isPathConnected hne).image' hF.continuousOn

end HolomorphicAnosov
