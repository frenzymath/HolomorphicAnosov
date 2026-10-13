import HolomorphicAnosov.Analysis.Complex.QCVerticalPartitionImages

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle
open scoped Pointwise

/-- Preservation of the literal marked modulus for quadrilaterals in an open
region whose compact closures lie in its specified closed carrier. -/
def MarkedModulusPreservingOn (f : ℂ → ℂ) (R C : Set ℂ) : Prop :=
  ∀ (Q : Set ℂ) (p : Fin 4 → ℂ) (m : ℝ), IsCompact (closure Q) →
    Q ⊆ R → closure Q ⊆ C → HasMarkedConformalModulus Q p m →
    HasMarkedConformalModulus (f '' Q) (fun i ↦ f (p i)) m

lemma qc_marked_preservation_conjugation {f : ℂ → ℂ} {R C : Set ℂ}
    (hf : MarkedModulusPreservingOn f R C) (e : ℂ ≃ₜ ℂ)
    (he : Differentiable ℂ e) (hei : Differentiable ℂ e.symm) :
    MarkedModulusPreservingOn (fun z ↦ e.symm (f (e z))) (e ⁻¹' R) (e ⁻¹' C) := by
  intro Q p m hcompact hQR hQC hmod
  have hmodE := qc_marked_modulus_image hmod hcompact e e.symm
    e.continuous.continuousOn e.injective.injOn he.differentiableOn hei.differentiableOn
    (fun z _ ↦ e.symm_apply_apply z)
  have hEc : IsCompact (closure (e '' Q)) := by
    rw [← e.image_closure]
    exact hcompact.image e.continuous
  have hER : e '' Q ⊆ R := by rintro _ ⟨z,hz,rfl⟩; exact hQR hz
  have hEC : closure (e '' Q) ⊆ C := by
    rw [← e.image_closure]
    rintro _ ⟨z,hz,rfl⟩
    exact hQC hz
  have hmF := hf _ _ _ hEc hER hEC hmodE
  have hcF : IsCompact (closure (f '' (e '' Q))) := by
    obtain ⟨a,b,ha,hb,hm,F,G,hF,hG,hbij,hmap,hGF,hFG,E,hE,hp⟩ := hmF
    have : CompactSpace (ClosedRectangle a b) :=
      isCompact_iff_compactSpace.mp (isCompact_Icc.reProdIm isCompact_Icc)
    exact isCompact_iff_compactSpace.mpr E.compactSpace
  have hresult := qc_marked_modulus_image hmF hcF e.symm e
    e.symm.continuous.continuousOn e.symm.injective.injOn hei.differentiableOn he.differentiableOn
    (fun z _ ↦ e.apply_symm_apply z)
  simpa only [image_image,Function.comp_apply] using hresult

lemma qc_rectangle_real_of_modulus
    {M : ℝ} (hM : 0 < M) (f : ℂ → ℂ)
    (hfc : ContinuousOn f (ClosedRectangle M 1))
    (hinj : InjOn f (ClosedRectangle M 1))
    (hmap : MapsTo f (ClosedRectangle M 1) (ClosedRectangle M 1))
    (hmapi : MapsTo f (OpenRectangle M 1) (OpenRectangle M 1))
    (hbottom : MapsTo f (ClosedRectangleSide M 1 0) (ClosedRectangleSide M 1 0))
    (htop : MapsTo f (ClosedRectangleSide M 1 2) (ClosedRectangleSide M 1 2))
    (h0 : f 0 = 0) (hI : f Complex.I = Complex.I)
    (hopen : ∀ V : Set ℂ, IsOpen V → V ⊆ OpenRectangle M 1 → IsOpen (f '' V))
    (hmod : MarkedModulusPreservingOn f (OpenRectangle M 1) (ClosedRectangle M 1)) :
    ∀ z ∈ OpenRectangle M 1, (f z).re = z.re := by
  have hRc : OpenRectangle M 1 ⊆ ClosedRectangle M 1 := by
    rw [← RectangleModelPreparation.closure_openRectangle hM (by norm_num)]
    exact subset_closure
  apply qc_rectangle_real_of_left_images hmapi (hinj.mono hRc)
  apply qc_vertical_partition_images hM f hfc hinj hmap hbottom htop h0 hI hopen
  intro x hx
  have hmx : 0 < M-x := sub_pos.mpr hx.2
  have hc (a : ℝ) (ha : 0 < a) : IsCompact (closure (OpenRectangle a 1)) := by
    rw [RectangleModelPreparation.closure_openRectangle ha (by norm_num)]
    exact isCompact_Icc.reProdIm isCompact_Icc
  have hLo : OpenRectangle x 1 ⊆ OpenRectangle M 1 := by
    intro z hz
    exact ⟨⟨hz.1.1,hz.1.2.trans hx.2⟩,hz.2⟩
  have hRo : (x : ℂ) +ᵥ OpenRectangle (M-x) 1 ⊆ OpenRectangle M 1 := by
    rintro z ⟨w,hw,rfl⟩
    change (0 < ((x : ℂ)+w).re ∧ ((x : ℂ)+w).re < M) ∧
      (0 < ((x : ℂ)+w).im ∧ ((x : ℂ)+w).im < 1)
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,zero_add]
    exact ⟨⟨by linarith [hw.1.1,hx.1],by linarith [hw.1.2]⟩,hw.2⟩
  have hinside (V : Set ℂ) (hV : V ⊆ OpenRectangle M 1) : closure V ⊆ ClosedRectangle M 1 := by
    rw [← RectangleModelPreparation.closure_openRectangle hM (by norm_num)]
    exact closure_mono hV
  constructor
  · apply hmod _ _ _ (hc x hx.1) hLo (hinside _ hLo)
    simpa using qc_identity_rectangle_modulus hx.1 (by norm_num : (0:ℝ)<1)
  · have hrect := qc_identity_rectangle_modulus hmx (by norm_num : (0:ℝ)<1)
    have ht := qc_marked_modulus_image hrect (hc (M-x) hmx)
      (fun z : ℂ ↦ (x : ℂ)+z) (fun z : ℂ ↦ z-(x : ℂ))
      (continuous_const.add continuous_id).continuousOn
      (fun z _ w _ h ↦ add_left_cancel h)
      ((differentiable_const _).add differentiable_id).differentiableOn
      (differentiable_id.sub (differentiable_const _)).differentiableOn
      (fun z _ ↦ by simp)
    have himage : (fun z : ℂ ↦ (x : ℂ)+z) '' OpenRectangle (M-x) 1 =
        (x : ℂ) +ᵥ OpenRectangle (M-x) 1 := by rw [← image_vadd]; rfl
    rw [himage] at ht
    have hcompact : IsCompact (closure ((x : ℂ) +ᵥ OpenRectangle (M-x) 1)) := by
      rw [closure_vadd]
      exact (hc (M-x) hmx).vadd _
    exact hmod _ _ _ hcompact hRo (hinside _ hRo) (by simpa using ht)

lemma qc_rectangle_quarter_turn {M : ℝ} (hM : 0 < M) :
    ∃ e : ℂ ≃ₜ ℂ, Differentiable ℂ e ∧ Differentiable ℂ e.symm ∧
      (∀ z, e z ∈ OpenRectangle M 1 ↔ z ∈ OpenRectangle M⁻¹ 1) ∧
      (∀ z, e z ∈ ClosedRectangle M 1 ↔ z ∈ ClosedRectangle M⁻¹ 1) ∧
      (∀ (i : Fin 4) z, e z ∈ ClosedRectangleSide M 1 (i+1) ↔
        z ∈ ClosedRectangleSide M⁻¹ 1 i) ∧
      (∀ i : Fin 4, e (RectangleCorner M⁻¹ 1 i) = RectangleCorner M 1 (i+1)) ∧
      ∀ z, (e z).im = M * z.re := by
  have hMn : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
  let e := (Homeomorph.mulLeft₀ ((M : ℂ)*Complex.I) (mul_ne_zero hMn Complex.I_ne_zero)).trans
    (Homeomorph.addLeft (M : ℂ))
  have heq (z : ℂ) : e z = (M : ℂ) + ((M : ℂ)*Complex.I)*z := rfl
  have hre (z : ℂ) : (e z).re = M - M*z.im := by simp [heq,Complex.mul_re,Complex.mul_im,sub_eq_add_neg]
  have him (z : ℂ) : (e z).im = M*z.re := by simp [heq,Complex.mul_re,Complex.mul_im]
  have he : Differentiable ℂ e := by
    change Differentiable ℂ (fun z ↦ (M : ℂ)+((M : ℂ)*Complex.I)*z)
    fun_prop
  have hei : Differentiable ℂ e.symm := by
    change Differentiable ℂ (fun z ↦ ((M : ℂ)*Complex.I)⁻¹ * (-(M : ℂ)+z))
    fun_prop
  have hMul : M*M⁻¹=1 := mul_inv_cancel₀ hM.ne'
  have ho (z : ℂ) : e z ∈ OpenRectangle M 1 ↔ z ∈ OpenRectangle M⁻¹ 1 := by
    change (0 < (e z).re ∧ (e z).re < M) ∧ (0 < (e z).im ∧ (e z).im < 1) ↔
      (0 < z.re ∧ z.re < M⁻¹) ∧ (0 < z.im ∧ z.im < 1)
    rw [hre,him]
    constructor
    · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      exact ⟨⟨by nlinarith,by nlinarith⟩,⟨by nlinarith,by nlinarith⟩⟩
    · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      exact ⟨⟨by nlinarith,by nlinarith⟩,⟨by nlinarith,by nlinarith⟩⟩
  have hc (z : ℂ) : e z ∈ ClosedRectangle M 1 ↔ z ∈ ClosedRectangle M⁻¹ 1 := by
    change (0 ≤ (e z).re ∧ (e z).re ≤ M) ∧ (0 ≤ (e z).im ∧ (e z).im ≤ 1) ↔
      (0 ≤ z.re ∧ z.re ≤ M⁻¹) ∧ (0 ≤ z.im ∧ z.im ≤ 1)
    rw [hre,him]
    constructor
    · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      exact ⟨⟨by nlinarith,by nlinarith⟩,⟨by nlinarith,by nlinarith⟩⟩
    · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      exact ⟨⟨by nlinarith,by nlinarith⟩,⟨by nlinarith,by nlinarith⟩⟩
  refine ⟨e,he,hei,ho,hc,?_,?_,him⟩
  · intro i z
    fin_cases i
    · change (e z).re = M ∧ (0 ≤ (e z).im ∧ (e z).im ≤ 1) ↔
        (0 ≤ z.re ∧ z.re ≤ M⁻¹) ∧ z.im = 0
      rw [hre,him]
      constructor
      · rintro ⟨h1,h2,h3⟩
        exact ⟨⟨by nlinarith,by nlinarith⟩,by nlinarith⟩
      · rintro ⟨⟨h1,h2⟩,h3⟩
        exact ⟨by nlinarith,by nlinarith,by nlinarith⟩
    · change (0 ≤ (e z).re ∧ (e z).re ≤ M) ∧ (e z).im = 1 ↔
        z.re = M⁻¹ ∧ (0 ≤ z.im ∧ z.im ≤ 1)
      rw [hre,him]
      constructor
      · rintro ⟨⟨h1,h2⟩,h3⟩
        exact ⟨by nlinarith,by nlinarith,by nlinarith⟩
      · rintro ⟨h1,h2,h3⟩
        exact ⟨⟨by nlinarith,by nlinarith⟩,by nlinarith⟩
    · change (e z).re = 0 ∧ (0 ≤ (e z).im ∧ (e z).im ≤ 1) ↔
        (0 ≤ z.re ∧ z.re ≤ M⁻¹) ∧ z.im = 1
      rw [hre,him]
      constructor
      · rintro ⟨h1,h2,h3⟩
        exact ⟨⟨by nlinarith,by nlinarith⟩,by nlinarith⟩
      · rintro ⟨⟨h1,h2⟩,h3⟩
        exact ⟨by nlinarith,by nlinarith,by nlinarith⟩
    · change (0 ≤ (e z).re ∧ (e z).re ≤ M) ∧ (e z).im = 0 ↔
        z.re = 0 ∧ (0 ≤ z.im ∧ z.im ≤ 1)
      rw [hre,him]
      constructor
      · rintro ⟨⟨h1,h2⟩,h3⟩
        exact ⟨by nlinarith,by nlinarith,by nlinarith⟩
      · rintro ⟨h1,h2,h3⟩
        exact ⟨⟨by nlinarith,by nlinarith⟩,by nlinarith⟩
  · intro i
    fin_cases i <;> apply Complex.ext <;> simp [hre,him,RectangleCorner,hMul]

/-- A marked-modulus-preserving normalized rectangle map fixing its four corners
is the identity. Vertical partition rigidity fixes real coordinates. Conjugate
by the holomorphic scaled quarter-turn from the reciprocal-width rectangle;
marked modulus is preserved under this conformal change. The same real-coordinate
argument there fixes the original imaginary coordinates. Source: Lehto–Virtanen
I.Theorem 5.1, pp.28–29. -/
theorem qc_normalized_rectangle_rigidity
    {M : ℝ} (hM : 0 < M) (f : ℂ → ℂ)
    (hfc : ContinuousOn f (ClosedRectangle M 1))
    (hinj : InjOn f (ClosedRectangle M 1))
    (hmap : MapsTo f (ClosedRectangle M 1) (ClosedRectangle M 1))
    (hmapi : MapsTo f (OpenRectangle M 1) (OpenRectangle M 1))
    (hside : ∀ i : Fin 4, MapsTo f (ClosedRectangleSide M 1 i) (ClosedRectangleSide M 1 i))
    (hcorn : ∀ i : Fin 4, f (RectangleCorner M 1 i) = RectangleCorner M 1 i)
    (hopen : ∀ V : Set ℂ, IsOpen V → V ⊆ OpenRectangle M 1 → IsOpen (f '' V))
    (hmod : MarkedModulusPreservingOn f (OpenRectangle M 1) (ClosedRectangle M 1)) :
    EqOn f id (OpenRectangle M 1) := by
  have hzero : f 0=0 := hcorn 0
  have hunit : f Complex.I=Complex.I := by simpa [RectangleCorner] using hcorn 3
  have hreal := qc_rectangle_real_of_modulus hM f hfc hinj hmap hmapi
    (hside 0) (hside 2) hzero hunit hopen hmod
  obtain ⟨e,he,hei,heo,hec,hes,hecorn,heim⟩ := qc_rectangle_quarter_turn hM
  let f' : ℂ → ℂ := fun z ↦ e.symm (f (e z))
  have hpreR : e ⁻¹' OpenRectangle M 1 = OpenRectangle M⁻¹ 1 := Set.ext heo
  have hpreC : e ⁻¹' ClosedRectangle M 1 = ClosedRectangle M⁻¹ 1 := Set.ext hec
  have hf'c : ContinuousOn f' (ClosedRectangle M⁻¹ 1) :=
    e.symm.continuous.comp_continuousOn
      (hfc.comp e.continuous.continuousOn (fun z hz ↦ (hec z).mpr hz))
  have hi' : InjOn f' (ClosedRectangle M⁻¹ 1) := by
    intro z hz w hw hh
    apply e.injective
    apply hinj ((hec z).mpr hz) ((hec w).mpr hw)
    exact e.symm.injective hh
  have hm' : MapsTo f' (ClosedRectangle M⁻¹ 1) (ClosedRectangle M⁻¹ 1) := by
    intro z hz
    apply (hec (f' z)).mp
    simpa [f'] using hmap ((hec z).mpr hz)
  have hmi' : MapsTo f' (OpenRectangle M⁻¹ 1) (OpenRectangle M⁻¹ 1) := by
    intro z hz
    apply (heo (f' z)).mp
    simpa [f'] using hmapi ((heo z).mpr hz)
  have hs' (i : Fin 4) : MapsTo f' (ClosedRectangleSide M⁻¹ 1 i)
      (ClosedRectangleSide M⁻¹ 1 i) := by
    intro z hz
    apply (hes i (f' z)).mp
    simpa [f'] using hside (i+1) ((hes i z).mpr hz)
  have hc' (i : Fin 4) : f' (RectangleCorner M⁻¹ 1 i) = RectangleCorner M⁻¹ 1 i := by
    apply e.injective
    change e (e.symm (f (e _))) = e _
    rw [e.apply_symm_apply,hecorn,hcorn]
  have ho' (V : Set ℂ) (hV : IsOpen V) (hVR : V ⊆ OpenRectangle M⁻¹ 1) :
      IsOpen (f' '' V) := by
    have hoE := e.isOpenMap _ hV
    have hin : e '' V ⊆ OpenRectangle M 1 := by
      rintro _ ⟨z,hz,rfl⟩
      exact (heo z).mpr (hVR hz)
    have hoF := hopen _ hoE hin
    have hfinal := e.symm.isOpenMap _ hoF
    simpa only [image_image,Function.comp_apply] using hfinal
  have hmod' : MarkedModulusPreservingOn f' (OpenRectangle M⁻¹ 1) (ClosedRectangle M⁻¹ 1) := by
    simpa only [hpreR,hpreC] using qc_marked_preservation_conjugation hmod e he hei
  have hz' : f' 0 = 0 := hc' 0
  have hiunit' : f' Complex.I = Complex.I := by simpa [RectangleCorner] using hc' 3
  have hr' := qc_rectangle_real_of_modulus (inv_pos.mpr hM) f' hf'c hi' hm' hmi'
    (hs' 0) (hs' 2) hz' hiunit' ho' hmod'
  intro z hz
  apply Complex.ext (hreal z hz)
  have hw : e.symm z ∈ OpenRectangle M⁻¹ 1 := by
    apply (heo _).mp
    simpa using hz
  have hreal' : (e.symm (f z)).re = (e.symm z).re := by
    simpa [f'] using hr' _ hw
  calc
    (f z).im = M * (e.symm (f z)).re := by simpa using heim (e.symm (f z))
    _ = M * (e.symm z).re := by rw [hreal']
    _ = z.im := by simpa using (heim (e.symm z)).symm

lemma qc_closed_unit_square_sides
    (e : ClosedRectangle 1 1 ≃ₜ ClosedRectangle 1 1)
    (hint : ∀ z, (e z : ℂ) ∈ OpenRectangle 1 1 ↔ (z : ℂ) ∈ OpenRectangle 1 1)
    (hc : ∀ (i : Fin 4) (z : ClosedRectangle 1 1),
      (z : ℂ)=RectangleCorner 1 1 i → (e z : ℂ)=RectangleCorner 1 1 i) :
    ∀ (i : Fin 4) (z : ClosedRectangle 1 1), (z : ℂ) ∈ ClosedRectangleSide 1 1 i →
      (e z : ℂ) ∈ ClosedRectangleSide 1 1 i := by
  have hh := qc_closed_rectangle_horizontal_sides (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) e hint hc
  have hv := (Analysis.marked_rectangle_coordinate_sides (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) e hint (hc 0 _ rfl) (hc 1 _ rfl)
    (hc 2 _ rfl) (hc 3 _ rfl)).1
  intro i z hz
  fin_cases i
  · exact hh.1 z hz
  · change (z : ℂ).re = 1 ∧ (z : ℂ).im ∈ Icc 0 1 at hz
    have hre : (e z : ℂ).re=1 := by
      by_cases h0 : (z : ℂ).im=0
      · have hz' : (z : ℂ)=RectangleCorner 1 1 1 := Complex.ext hz.1 h0
        exact congrArg Complex.re (hc 1 z hz')
      by_cases h1 : (z : ℂ).im=1
      · have hz' : (z : ℂ)=RectangleCorner 1 1 2 := Complex.ext (by simpa [RectangleCorner] using hz.1) (by simpa [RectangleCorner] using h1)
        simpa [RectangleCorner] using congrArg Complex.re (hc 2 z hz')
      exact (hv z ⟨lt_of_le_of_ne hz.2.1 (Ne.symm h0),lt_of_le_of_ne hz.2.2 h1⟩).2 hz.1
    exact ⟨hre,(e z).property.2⟩
  · exact hh.2 z hz
  · change (z : ℂ).re = 0 ∧ (z : ℂ).im ∈ Icc 0 1 at hz
    have hre : (e z : ℂ).re=0 := by
      by_cases h0 : (z : ℂ).im=0
      · have hz' : (z : ℂ)=RectangleCorner 1 1 0 := Complex.ext hz.1 h0
        exact congrArg Complex.re (hc 0 z hz')
      by_cases h1 : (z : ℂ).im=1
      · have hz' : (z : ℂ)=RectangleCorner 1 1 3 := Complex.ext (by simpa [RectangleCorner] using hz.1) (by simpa [RectangleCorner] using h1)
        simpa [RectangleCorner] using congrArg Complex.re (hc 3 z hz')
      exact (hv z ⟨lt_of_le_of_ne hz.2.1 (Ne.symm h0),lt_of_le_of_ne hz.2.2 h1⟩).1 hz.1
    exact ⟨hre,(e z).property.2⟩

end HolomorphicAnosov
