import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulus
import HolomorphicAnosov.Analysis.Complex.QCRengelStripBounds
import HolomorphicAnosov.Analysis.Complex.QCRectangleHorizontalSides
import HolomorphicAnosov.Analysis.Complex.QCInsideModulusSqueeze
import HolomorphicAnosov.Analysis.Complex.QCCompactBoundaryTransport

namespace HolomorphicAnosov
open Set Filter _root_.Topology Analysis.MarkedRectangle

/-- Inside continuity of marked conformal modulus for uniformly converging
closure parametrizations. Source: Lehto--Virtanen I.Lemma 4.3 p.26, (4.15).

Fix the inverse conformal rectangle model of Q and extend it continuously to
its compact closure. Its composition with the inner closure homeomorphisms
converges uniformly to the identity rectangle coordinates. For each inner
model, compose its closure map with the inverse inner parametrization and
then the fixed inverse closure map. This is a corner-preserving rectangle
homeomorphism; the side correspondence theorems locate every open side point
on its corresponding fixed side. The uniform coordinate error puts its
actual inner conformal image in the four narrow strips. The image lies inside
the ambient rectangle, so the two Rengel strip bounds apply. The numerical
squeeze as the strip width tends to zero proves convergence of the moduli.
-/
theorem qc_inside_marked_modulus_continuity
    {Q : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hcompact : IsCompact (closure Q)) (hmod : HasMarkedConformalModulus Q p m)
    (P : ℕ → Set ℂ) (q : ℕ → Fin 4 → ℂ) (ν : ℕ → ℝ)
    (hP : ∀ n, closure (P n) ⊆ Q)
    (hnmod : ∀ n, HasMarkedConformalModulus (P n) (q n) (ν n))
    (h : ∀ n, closure Q ≃ₜ closure (P n))
    (hint : ∀ n z, (h n z : ℂ) ∈ P n ↔ (z : ℂ) ∈ Q)
    (hpcl : ∀ i, p i ∈ closure Q)
    (hmarks : ∀ n i, (h n ⟨p i, hpcl i⟩ : ℂ) = q n i)
    (hlim : TendstoUniformly (fun n z ↦ (h n z : ℂ)) (fun z ↦ (z : ℂ)) atTop) :
    Tendsto ν atTop (𝓝 m) := by
  classical
  obtain ⟨A, B, hA, hB, rfl, F, Fi, hF, hFi, hbij, hmaps, hFiF, hFFi,
    e, he, hcorner⟩ := hmod
  have hR : OpenRectangle A B ⊆ ClosedRectangle A B := by
    rw [← RectangleModelPreparation.closure_openRectangle hA hB]
    exact subset_closure
  have heint (z : ClosedRectangle A B) : (e z : ℂ) ∈ Q ↔ (z : ℂ) ∈ OpenRectangle A B := by
    constructor
    · intro hz
      obtain ⟨w, hw, heq⟩ := hbij.surjOn hz
      have heq' : e z = e ⟨w, hR hw⟩ :=
        Subtype.ext (heq.symm.trans (he ⟨w, hR hw⟩ hw).symm)
      exact (congrArg Subtype.val (e.injective heq')).symm ▸ hw
    · intro hz
      rw [he z hz]
      exact hbij.mapsTo hz
  let f : ℂ → ℂ := Function.extend Subtype.val
    (fun z : closure Q ↦ (e.symm z : ℂ)) (fun _ ↦ 0)
  have hfe (z : closure Q) : f z = (e.symm z : ℂ) :=
    Subtype.val_injective.extend_apply _ _ z
  have hfc : ContinuousOn f (closure Q) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.symm.continuous).congr (fun z ↦ (hfe z).symm)
  have hfFi (z : ℂ) (hz : z ∈ Q) : f z = Fi z :=
    (hfe ⟨z, subset_closure hz⟩).trans
      (RectangleModelPreparation.closure_inverse_agrees hR F Fi e he hmaps hFFi z hz)
  have hfinj : InjOn f (closure Q) := by
    intro z hz w hw heq
    rw [hfe ⟨z,hz⟩, hfe ⟨w,hw⟩] at heq
    exact congrArg Subtype.val (e.symm.injective (Subtype.ext heq))
  have hfmap (z : ℂ) (hz : z ∈ Q) : f z ∈ OpenRectangle A B := by
    rw [hfFi z hz]
    exact hmaps hz
  have hcoordlim : TendstoUniformly (fun n z ↦ f (h n z)) (fun z : closure Q ↦ f z) atTop := by
    have h' := qc_uniform_compact_parametrizations hcompact hfc
      (F := fun _ ↦ f) (by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        exact Filter.Eventually.of_forall (fun n z hz ↦ by simpa using hε))
      (fun z : closure Q ↦ z.property)
      (fun n z ↦ subset_closure (hP n (h n z).property)) hlim
    exact h'
  apply qc_inside_modulus_squeeze (div_pos hA hB)
  intro ε hε hcap
  have herr := Metric.tendstoUniformly_iff.mp hcoordlim (B * ε) (mul_pos hB hε)
  filter_upwards [herr] with n hn
  obtain ⟨a, b, ha, hb, hν, G, Gi, hG, hGi, hGbij, hGmaps, hGiG, hGGi,
    en, hen, hncorner⟩ := hnmod n
  have hR' : OpenRectangle a b ⊆ ClosedRectangle a b := by
    rw [← RectangleModelPreparation.closure_openRectangle ha hb]
    exact subset_closure
  have henint (z : ClosedRectangle a b) : (en z : ℂ) ∈ P n ↔ (z : ℂ) ∈ OpenRectangle a b := by
    constructor
    · intro hz
      obtain ⟨w, hw, heq⟩ := hGbij.surjOn hz
      have heq' : en z = en ⟨w, hR' hw⟩ :=
        Subtype.ext (heq.symm.trans (hen ⟨w,hR' hw⟩ hw).symm)
      exact (congrArg Subtype.val (en.injective heq')).symm ▸ hw
    · intro hz
      rw [hen z hz]
      exact hGbij.mapsTo hz
  let E : ClosedRectangle a b ≃ₜ ClosedRectangle A B := (en.trans (h n).symm).trans e.symm
  have hEint (z : ClosedRectangle a b) : (E z : ℂ) ∈ OpenRectangle A B ↔
      (z : ℂ) ∈ OpenRectangle a b := by
    change (e.symm ((h n).symm (en z)) : ℂ) ∈ OpenRectangle A B ↔ _
    rw [← heint]
    simp only [e.apply_symm_apply]
    rw [← hint n ((h n).symm (en z)), (h n).apply_symm_apply, henint]
  have hEcorn (i : Fin 4) :
      (E ⟨RectangleCorner a b i, RectangleModelPreparation.corner_mem ha hb i⟩ : ℂ) =
        RectangleCorner A B i := by
    let z : ClosedRectangle a b := ⟨RectangleCorner a b i, RectangleModelPreparation.corner_mem ha hb i⟩
    let w : ClosedRectangle A B := ⟨RectangleCorner A B i, RectangleModelPreparation.corner_mem hA hB i⟩
    have hnz : en z = h n (e w) := by
      apply Subtype.ext
      rw [hncorner i z rfl]
      have hp : e w = ⟨p i, hpcl i⟩ := Subtype.ext (hcorner i w rfl)
      rw [hp, hmarks]
    change (e.symm ((h n).symm (en z)) : ℂ) = _
    rw [hnz, (h n).symm_apply_apply, e.symm_apply_apply]
  have hsides := Analysis.marked_rectangle_coordinate_sides ha hb hA hB E hEint
    (by exact hEcorn 0)
    (by exact hEcorn 1)
    (by exact hEcorn 2)
    (by exact hEcorn 3)
  let W : ℂ → ℂ := Function.extend Subtype.val
    (fun z : ClosedRectangle a b ↦ f (en z)) (fun _ ↦ 0)
  have hW (z : ClosedRectangle a b) : W z = f (en z) :=
    Subtype.val_injective.extend_apply _ _ z
  have hWc : ContinuousOn W (ClosedRectangle a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc := hfc.comp_continuous (continuous_subtype_val.comp en.continuous)
      (fun z ↦ subset_closure (hP n (en z).property))
    exact hc.congr (fun z ↦ (hW z).symm)
  have hWeq : EqOn W (Fi ∘ G) (OpenRectangle a b) := by
    intro z hz
    rw [hW ⟨z, hR' hz⟩, hen _ hz,
      hfFi _ (hP n (subset_closure (hGbij.mapsTo hz)))]
    rfl
  have hWh : DifferentiableOn ℂ W (OpenRectangle a b) :=
    (hFi.comp hG (fun z hz ↦ hP n (subset_closure (hGbij.mapsTo hz)))).congr hWeq
  have hWmaps : MapsTo W (OpenRectangle a b) (OpenRectangle A B) := by
    intro z hz
    rw [hW ⟨z,hR' hz⟩]
    exact hfmap _ (hP n (en _).property)
  have hWi : InjOn W (OpenRectangle a b) := by
    intro z hz w hw heq
    rw [hW ⟨z,hR' hz⟩, hW ⟨w,hR' hw⟩] at heq
    have hi := hfinj (subset_closure (hP n (en ⟨z,hR' hz⟩).property))
      (subset_closure (hP n (en ⟨w,hR' hw⟩).property)) heq
    exact congrArg Subtype.val (en.injective (Subtype.ext hi))
  have herror (z : ClosedRectangle a b) : dist (W z) (E z : ℂ) < B * ε := by
    let w : closure Q := (h n).symm (en z)
    have hh := hn w
    rw [hfe w] at hh
    have hz : h n w = en z := (h n).apply_symm_apply _
    rw [hz] at hh
    exact (dist_comm _ _).trans_lt ((hW z).symm ▸ hh)
  have hv : ∀ x ∈ Ioo 0 a, (W (x : ℂ)).im ≤ B * ε ∧
      B * (1 - ε) ≤ (W ((x : ℂ) + b * Complex.I)).im := by
    intro x hx
    let z0 : ClosedRectangle a b := ⟨x, by
      change (x : ℂ).re ∈ Icc 0 a ∧ (x : ℂ).im ∈ Icc 0 b
      exact ⟨Ioo_subset_Icc_self hx, ⟨le_rfl, hb.le⟩⟩⟩
    let z1 : ClosedRectangle a b := ⟨(x : ℂ) + b * Complex.I, by
      change ((x : ℂ) + b * Complex.I).re ∈ Icc 0 a ∧ ((x : ℂ) + b * Complex.I).im ∈ Icc 0 b
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add, sub_self]
      exact ⟨Ioo_subset_Icc_self hx, ⟨hb.le, le_rfl⟩⟩⟩
    have hz0 := (hsides.2 z0 (by simpa [z0, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_add] using hx)).1 (by simp [z0])
    have hz1 := (hsides.2 z1 (by simpa [z1, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_add] using hx)).2 (by simp [z1])
    have h0 := (Complex.abs_im_le_norm (W z0 - E z0)).trans_lt (by simpa [dist_eq_norm] using herror z0)
    have h1 := (Complex.abs_im_le_norm (W z1 - E z1)).trans_lt (by simpa [dist_eq_norm] using herror z1)
    rw [Complex.sub_im] at h0 h1
    have h0' : |(W z0).im| < B * ε := by
      have hz0' : (E z0 : ℂ).im = 0 := hz0
      rw [hz0'] at h0
      simpa using h0
    have h1' : |(W z1).im - B| < B * ε := by
      have hz1' : (E z1 : ℂ).im = B := hz1
      rw [hz1'] at h1
      exact h1
    exact ⟨(le_abs_self _).trans h0'.le, by
      have hi := (abs_lt.mp h1').1
      change B * (1 - ε) ≤ (W z1).im
      have hB0 : 0 < B := hB
      nlinarith [hi, hB0]⟩
  have hh : ∀ y ∈ Ioo 0 b, (W (y * Complex.I)).re ≤ B * ε ∧
      A - B * ε ≤ (W ((a : ℂ) + y * Complex.I)).re := by
    intro y hy
    let z0 : ClosedRectangle a b := ⟨y * Complex.I, by
      change (y * Complex.I).re ∈ Icc 0 a ∧ (y * Complex.I).im ∈ Icc 0 b
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.mul_im, mul_zero, add_zero, mul_one, sub_self]
      exact ⟨⟨le_rfl, ha.le⟩, Ioo_subset_Icc_self hy⟩⟩
    let z1 : ClosedRectangle a b := ⟨(a : ℂ) + y * Complex.I, by
      change ((a : ℂ) + y * Complex.I).re ∈ Icc 0 a ∧ ((a : ℂ) + y * Complex.I).im ∈ Icc 0 b
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add, sub_self]
      exact ⟨⟨ha.le, le_rfl⟩, Ioo_subset_Icc_self hy⟩⟩
    have hz0 := (hsides.1 z0 (by simpa [z0, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_add] using hy)).1 (by simp [z0])
    have hz1 := (hsides.1 z1 (by simpa [z1, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_add] using hy)).2 (by simp [z1])
    have h0 := (Complex.abs_re_le_norm (W z0 - E z0)).trans_lt (by simpa [dist_eq_norm] using herror z0)
    have h1 := (Complex.abs_re_le_norm (W z1 - E z1)).trans_lt (by simpa [dist_eq_norm] using herror z1)
    rw [Complex.sub_re] at h0 h1
    have h0' : |(W z0).re| < B * ε := by
      have hz0' : (E z0 : ℂ).re = 0 := hz0
      rw [hz0'] at h0
      simpa using h0
    have h1' : |(W z1).re - A| < B * ε := by
      have hz1' : (E z1 : ℂ).re = A := hz1
      rw [hz1'] at h1
      exact h1
    exact ⟨(le_abs_self _).trans h0'.le, by
      have hi := (abs_lt.mp h1').1
      change A - B * ε ≤ (W z1).re
      linarith⟩
  rw [hν]
  exact qc_rengel_strip_bounds_scaled ha hb hA hB (lt_min_iff.mp hcap).1
    (lt_min_iff.mp hcap).2 hWc hWh hWi hWmaps hv hh

end HolomorphicAnosov
