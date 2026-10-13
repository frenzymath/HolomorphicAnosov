import HolomorphicAnosov.Analysis.Complex.QCNormalizedRectangleRigidity
import HolomorphicAnosov.Analysis.Complex.QCUnitSquareModel
import HolomorphicAnosov.Analysis.Complex.QCGeometricImageModulus
import HolomorphicAnosov.Analysis.Complex.QCMarkedModulusTransport

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle
open scoped _root_.Topology

/-- The local square step in the geometric 1-QC proof. Normalize the image
quadrilateral to the unit square. Transport the exact marked-modulus hypothesis
through both conformal coordinates, apply normalized rectangle rigidity, and
undo the coordinates. Partition closures need only stay in the original source. -/
lemma qc_geometric_on_square
    (g : OpenPartialHomeomorph ℂ ℂ)
    (hpres : ∀ (Q : Set ℂ) (p : Fin 4 → ℂ) (m : ℝ),
      IsCompact (closure Q) → closure Q ⊆ g.source → HasMarkedConformalModulus Q p m →
      HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m)
    (s : ℂ ≃ₜ ℂ) (hs : Differentiable ℂ s) (hsi : Differentiable ℂ s.symm)
    (hinside : s '' ClosedRectangle 1 1 ⊆ g.source) :
    DifferentiableOn ℂ g (s '' OpenRectangle 1 1) := by
  let R := OpenRectangle (1:ℝ) 1
  let C := ClosedRectangle (1:ℝ) 1
  let Q := s '' R
  let T := g '' Q
  have hR : IsOpen R := RectangleModelPreparation.isOpen_openRectangle _ _
  have hcl : closure R=C := RectangleModelPreparation.closure_openRectangle (by norm_num) (by norm_num)
  have hRc : R ⊆ C := hcl ▸ subset_closure
  have hCc : IsCompact C := isCompact_Icc.reProdIm isCompact_Icc
  have hQcl : closure Q = s '' C := by rw [← hcl,s.image_closure]
  have hQc : IsCompact (closure Q) := by rw [hQcl]; exact hCc.image s.continuous
  have hQs : closure Q ⊆ g.source := hQcl ▸ hinside
  have hQsrc : Q ⊆ g.source := subset_closure.trans hQs
  have hsc : MapsTo s C (closure Q) := by intro z hz; rw [hQcl]; exact mem_image_of_mem s hz
  have hgc : ContinuousOn g (closure Q) := g.continuousOn.mono hQs
  have hgcl : g '' closure Q=closure T := Subset.antisymm hgc.image_closure
    (closure_minimal (image_mono subset_closure) (hQc.image_of_continuousOn hgc).isClosed)
  have hgtc : MapsTo g (closure Q) (closure T) := by
    intro z hz
    rw [← hgcl]
    exact mem_image_of_mem g hz
  have hTc : IsCompact (closure T) := by rw [← hgcl]; exact hQc.image_of_continuousOn hgc
  have hQmod : HasMarkedConformalModulus Q (fun i ↦ s (RectangleCorner 1 1 i)) 1 := by
    have hh := qc_marked_modulus_image (qc_identity_rectangle_modulus (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1)) (by rw [hcl]; exact hCc) s s.symm
      s.continuous.continuousOn s.injective.injOn hs.differentiableOn hsi.differentiableOn
      (fun z _ ↦ s.symm_apply_apply z)
    simpa using hh
  have hTmod := hpres Q _ 1 hQc hQs hQmod
  obtain ⟨H,J,E,hHc,hJc,hH,hJ,hHbij,hJmap,hJH,hHJ,hEH,hEJ,hcorn⟩ := qc_unit_square_model hTmod
  have hHmap : MapsTo H C (closure T) := by
    intro z hz
    rw [← hEH ⟨z,hz⟩]
    exact (E ⟨z,hz⟩).property
  have hJmapc : MapsTo J (closure T) C := by
    intro w hw
    rw [← hEJ ⟨w,hw⟩]
    exact (E.symm ⟨w,hw⟩).property
  have hJinj : InjOn J (closure T) := by
    intro z hz w hw hh
    have hhh := congrArg H hh
    rwa [hHJ z hz,hHJ w hw] at hhh
  have hJint {w : ℂ} (hw : w ∈ closure T) : J w ∈ R ↔ w ∈ T := by
    constructor
    · intro hj
      have hh := hHbij.mapsTo hj
      rwa [hHJ w hw] at hh
    · exact fun ht ↦ hJmap ht
  let f : ℂ → ℂ := fun z ↦ g (s z)
  have hfc : ContinuousOn f C := hgc.comp s.continuous.continuousOn hsc
  have hfinj : InjOn f C := by
    intro z hz w hw hh
    exact s.injective (g.injOn (hQs (hsc hz)) (hQs (hsc hw)) hh)
  have hfimage : f '' R=T := by simp only [f,T,Q,image_image]
  obtain ⟨k₀,hk₀,hkint₀⟩ := qc_closed_rectangle_image_model (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1) f hfc hfinj
  let k := k₀.trans (Homeomorph.setCongr (congrArg closure hfimage))
  have hk (z : C) : (k z : ℂ)=f z := hk₀ z
  have hkint (z : C) : (k z : ℂ) ∈ T ↔ (z : ℂ) ∈ R := by
    rw [hk]
    have hh := hkint₀ z
    rw [hk₀] at hh
    change f (z : ℂ) ∈ f '' R ↔ (z : ℂ) ∈ R at hh
    rwa [hfimage] at hh
  let W : ℂ → ℂ := fun z ↦ J (f z)
  let e := k.trans E.symm
  have he (z : C) : (e z : ℂ)=W z := by
    change (E.symm (k z) : ℂ)=J (f z)
    rw [hEJ,hk]
  have heint (z : C) : (e z : ℂ) ∈ R ↔ (z : ℂ) ∈ R := by
    change (E.symm (k z) : ℂ) ∈ R ↔ _
    rw [hEJ,hJint (k z).property]
    exact hkint z
  have hWc : ContinuousOn W C := hJc.comp hfc (hgtc.comp hsc)
  have hWinj : InjOn W C := hJinj.comp hfinj (hgtc.comp hsc)
  have hWmap : MapsTo W C C := hJmapc.comp (hgtc.comp hsc)
  have hWmapi : MapsTo W R R := by
    intro z hz
    exact hJmap ⟨s z,⟨z,hz,rfl⟩,rfl⟩
  have hWcorn (i : Fin 4) : W (RectangleCorner 1 1 i)=RectangleCorner 1 1 i := by
    change J (g (s (RectangleCorner 1 1 i)))=_
    rw [← hcorn i]
    exact hJH _ (RectangleModelPreparation.corner_mem (by norm_num) (by norm_num) i)
  have hecorn (i : Fin 4) (z : C) (hz : (z : ℂ)=RectangleCorner 1 1 i) :
      (e z : ℂ)=RectangleCorner 1 1 i := by rw [he,hz,hWcorn]
  have hWside (i : Fin 4) : MapsTo W (ClosedRectangleSide 1 1 i) (ClosedRectangleSide 1 1 i) := by
    intro z hz
    have hzc : z ∈ C := by
      fin_cases i <;> simp only [ClosedRectangleSide,Complex.mem_reProdIm,mem_Icc,mem_singleton_iff] at hz
      all_goals change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1)
      all_goals rcases hz with ⟨h1,h2⟩
      all_goals simp_all
    simpa only [he] using qc_closed_unit_square_sides e heint hecorn i ⟨z,hzc⟩ hz
  have hTopen : IsOpen T := g.isOpen_image_of_subset_source (s.isOpenMap _ hR) hQsrc
  have hWopen (V : Set ℂ) (hV : IsOpen V) (hVR : V ⊆ R) : IsOpen (W '' V) := by
    have hsV : s '' V ⊆ Q := image_mono hVR
    have hgV := g.isOpen_image_of_subset_source (s.isOpenMap _ hV) (hsV.trans hQsrc)
    have hgVT : g '' (s '' V) ⊆ T := image_mono hsV
    have hopenJ := lebl_scalar_open_image hTopen hJ (hJinj.mono subset_closure) hgV hgVT
    simpa only [W,f,image_image,Function.comp_apply] using hopenJ
  have hWmod : MarkedModulusPreservingOn W R C := by
    intro P p m hPc hPR hPC hmP
    have hmS := qc_marked_modulus_image hmP hPc s s.symm s.continuous.continuousOn
      s.injective.injOn hs.differentiableOn hsi.differentiableOn (fun z _ ↦ s.symm_apply_apply z)
    have hcS : IsCompact (closure (s '' P)) := by rw [← s.image_closure]; exact hPc.image s.continuous
    have hiS : closure (s '' P) ⊆ closure Q := by rw [← s.image_closure,hQcl]; exact image_mono hPC
    have hmG := hpres _ _ _ hcS (hiS.trans hQs) hmS
    have hgPc : IsCompact (closure (g '' (s '' P))) := by
      have hcg : ContinuousOn g (closure (s '' P)) := g.continuousOn.mono (hiS.trans hQs)
      have heq : closure (g '' (s '' P))=g '' closure (s '' P) :=
        (Subset.antisymm hcg.image_closure (closure_minimal (image_mono subset_closure)
          (hcS.image_of_continuousOn hcg).isClosed)).symm
      rw [heq]
      exact hcS.image_of_continuousOn hcg
    have hgPT : g '' (s '' P) ⊆ T := image_mono (image_mono hPR)
    have hclPT : closure (g '' (s '' P)) ⊆ closure T := closure_mono hgPT
    have hmJ := qc_marked_modulus_image hmG hgPc J H (hJc.mono hclPT)
      (hJinj.mono hclPT) (hJ.mono hgPT)
      (hH.mono (by rintro _ ⟨w,hw,rfl⟩; exact hJmap (hgPT hw)))
      (fun w hw ↦ hHJ w (subset_closure (hgPT hw)))
    simpa only [W,f,image_image,Function.comp_apply] using hmJ
  have hWid := qc_normalized_rectangle_rigidity (by norm_num : (0:ℝ)<1) W hWc hWinj
    hWmap hWmapi hWside hWcorn hWopen hWmod
  have hEq : EqOn g (H ∘ s.symm) Q := by
    rintro w ⟨z,hz,rfl⟩
    simp only [Function.comp_apply,s.symm_apply_apply]
    have hh := hHJ (f z) (hgtc (hsc (hRc hz)))
    change H (W z)=f z at hh
    rw [hWid hz] at hh
    exact hh.symm
  apply DifferentiableOn.congr _ hEq
  exact hH.comp hsi.differentiableOn (by rintro _ ⟨z,hz,rfl⟩; simpa using hz)

/-- A positively oriented geometric 1-QC homeomorphism is holomorphic.
Source: Lehto–Virtanen (1973), I.Theorem 5.1 pp.28–29 and I.Theorem 5.1
pp.28–29. Positive boundary transport gives marked image moduli. Cyclic
reciprocity upgrades the one-sided bound to equality. Around each source
point choose a small affine square with compact closure in the source.
Its image has marked modulus one, so normalize the source and image to
the unit square with literal continuous closure coordinates. Conformal
transport preserves the exact modulus equality for each partition piece;
although its closure may touch the outer square boundary, it remains
compactly inside the original source. The two-piece equality theorem fixes
all vertical partitions, and marked-modulus uniqueness identifies their
widths. A conformal quarter-turn gives the analogous horizontal identity.
Thus the normalized map is the identity; undoing the holomorphic coordinates
proves holomorphy on the small square. Such squares surround every source
point, so differentiability holds throughout the original open source. -/
theorem qc_geometric_one_conformal
    (U : Set ℂ) (hU : IsOpen U) (_hU_connected : IsConnected U)
    (g : OpenPartialHomeomorph ℂ ℂ) (hg_source : g.source = U)
    (hg_positive : ∀ a : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall a r ⊆ U →
      ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
          Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) = (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
        θ 1 = θ 0 + 2 * Real.pi)
    (hBound : ∀ (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ),
      IsCompact (closure Q) → closure Q ⊆ U →
      HasMarkedConformalModulus Q p m →
      HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m' → m' ≤ m) : DifferentiableOn ℂ g U := by
  have hpres (Q : Set ℂ) (p : Fin 4 → ℂ) (m : ℝ)
      (hQc : IsCompact (closure Q)) (hQs : closure Q ⊆ g.source)
      (hmod : HasMarkedConformalModulus Q p m) :
      HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m := by
    apply qc_geometric_preserves_marked_modulus g
      (by simpa only [hg_source] using hg_positive)
      (by simpa only [hg_source] using hBound) hQc hQs hmod
  intro z hz
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU z hz
  let d : ℝ := r/2
  have hd : 0 < d := half_pos hr
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  let c : ℂ := ⟨1/2,1/2⟩
  let s : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (d : ℂ) hdC).trans
    (Homeomorph.addLeft (z-(d : ℂ)*c))
  have hsval (w : ℂ) : s w=z+(d : ℂ)*(w-c) := by change z-(d : ℂ)*c+(d : ℂ)*w=_; ring
  have hs : Differentiable ℂ s := by
    change Differentiable ℂ (fun w ↦ z-(d : ℂ)*c+(d : ℂ)*w)
    fun_prop
  have hsi : Differentiable ℂ s.symm := by
    change Differentiable ℂ (fun w ↦ (d : ℂ)⁻¹ * (-(z-(d : ℂ)*c)+w))
    fun_prop
  have hinside : s '' ClosedRectangle 1 1 ⊆ g.source := by
    rintro w ⟨v,hv,rfl⟩
    rw [hg_source]
    apply hrU
    have hre : |(v-c).re| ≤ (1:ℝ)/2 := by
      apply abs_le.mpr
      change -(1/2 : ℝ) ≤ v.re-1/2 ∧ v.re-1/2 ≤ 1/2
      exact ⟨by linarith [hv.1.1],by linarith [hv.1.2]⟩
    have him : |(v-c).im| ≤ (1:ℝ)/2 := by
      apply abs_le.mpr
      change -(1/2 : ℝ) ≤ v.im-1/2 ∧ v.im-1/2 ≤ 1/2
      exact ⟨by linarith [hv.2.1],by linarith [hv.2.2]⟩
    have hnorm : ‖v-c‖ ≤ 1 := (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)
    rw [Metric.mem_ball,dist_eq_norm,hsval,add_sub_cancel_left,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    have hb := mul_le_mul_of_nonneg_left hnorm hd.le
    dsimp [d] at hb ⊢
    linarith
  have hc : c ∈ OpenRectangle 1 1 := by
    change (0 < (1/2:ℝ) ∧ (1/2:ℝ) < 1) ∧ (0 < (1/2:ℝ) ∧ (1/2:ℝ) < 1)
    norm_num
  have hzQ : z ∈ s '' OpenRectangle 1 1 := ⟨c,hc,by rw [hsval]; simp⟩
  have hQopen := s.isOpenMap _ (RectangleModelPreparation.isOpen_openRectangle 1 1)
  exact ((qc_geometric_on_square g hpres s hs hsi hinside).differentiableAt
    (hQopen.mem_nhds hzQ)).differentiableWithinAt

end HolomorphicAnosov
