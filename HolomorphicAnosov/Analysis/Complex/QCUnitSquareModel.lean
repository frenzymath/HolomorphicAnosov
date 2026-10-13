import HolomorphicAnosov.Analysis.Complex.QCMarkedModulusTransport

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle

/-- A marked quadrilateral of modulus one has a unit-square conformal model
whose two total maps agree literally with mutually inverse closure
homeomorphisms. Rescale its square rectangle by its positive side length,
then extend the closure homeomorphism and its inverse arbitrarily outside
their closed carriers. On the interiors these extensions agree with the
rescaled holomorphic model and inverse. Source: Lehto–Virtanen I.§2.4, p.15. -/
theorem qc_unit_square_model {Q : Set ℂ} {p : Fin 4 → ℂ}
    (hmod : HasMarkedConformalModulus Q p 1) :
    ∃ (F G : ℂ → ℂ) (E : ClosedRectangle 1 1 ≃ₜ closure Q),
      ContinuousOn F (ClosedRectangle 1 1) ∧ ContinuousOn G (closure Q) ∧
      DifferentiableOn ℂ F (OpenRectangle 1 1) ∧ DifferentiableOn ℂ G Q ∧
      BijOn F (OpenRectangle 1 1) Q ∧ MapsTo G Q (OpenRectangle 1 1) ∧
      (∀ z ∈ ClosedRectangle 1 1, G (F z) = z) ∧
      (∀ w ∈ closure Q, F (G w) = w) ∧
      (∀ z, (E z : ℂ) = F z) ∧ (∀ w, (E.symm w : ℂ) = G w) ∧
      ∀ i : Fin 4, F (RectangleCorner 1 1 i) = p i := by
  classical
  obtain ⟨a,b,ha,hb,hm,F₀,G₀,hF₀,hG₀,hbij,hGmap,hGF,hFG,e,he,hp⟩ := hmod
  have hab : a=b := (div_eq_one_iff_eq hb.ne').mp hm.symm
  subst a
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hmul (z : ℂ) : (b : ℂ)*z ∈ OpenRectangle b b ↔ z ∈ OpenRectangle 1 1 := by
    simp only [OpenRectangle,Complex.mem_reProdIm,mem_Ioo,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    rw [mul_pos_iff_of_pos_left hb,← lt_div_iff₀' hb,div_self hb.ne',
      mul_pos_iff_of_pos_left hb,← lt_div_iff₀' hb,div_self hb.ne']
  have hmulc (z : ℂ) : (b : ℂ)*z ∈ ClosedRectangle b b ↔ z ∈ ClosedRectangle 1 1 := by
    simp only [ClosedRectangle,Complex.mem_reProdIm,mem_Icc,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    rw [mul_nonneg_iff_of_pos_left hb,← le_div_iff₀' hb,div_self hb.ne',
      mul_nonneg_iff_of_pos_left hb,← le_div_iff₀' hb,div_self hb.ne']
  have hdiv (z : ℂ) : (b : ℂ)*(z/b)=z := by field_simp
  let t : ClosedRectangle 1 1 ≃ₜ ClosedRectangle b b :=
    { toFun := fun z ↦ ⟨(b : ℂ)*z,(hmulc z).mpr z.property⟩
      invFun := fun z ↦ ⟨(z : ℂ)/b,(hmulc _).mp (by rw [hdiv]; exact z.property)⟩
      left_inv := fun z ↦ Subtype.ext (by simp [hbC])
      right_inv := fun z ↦ Subtype.ext (hdiv z)
      continuous_toFun := ((continuous_const.mul continuous_subtype_val)).subtype_mk _
      continuous_invFun := (continuous_subtype_val.div_const _).subtype_mk _ }
  let E := t.trans e
  let F : ℂ → ℂ := Function.extend Subtype.val
    (fun z : ClosedRectangle 1 1 ↦ (E z : ℂ)) (fun _ ↦ 0)
  let G : ℂ → ℂ := Function.extend Subtype.val
    (fun w : closure Q ↦ (E.symm w : ℂ)) (fun _ ↦ 0)
  have hFE (z : ClosedRectangle 1 1) : F z = (E z : ℂ) :=
    Subtype.val_injective.extend_apply _ _ z
  have hGE (w : closure Q) : G w = (E.symm w : ℂ) :=
    Subtype.val_injective.extend_apply _ _ w
  have hRc : OpenRectangle 1 1 ⊆ ClosedRectangle 1 1 := by
    rw [← RectangleModelPreparation.closure_openRectangle (by norm_num : (0:ℝ)<1) (by norm_num)]
    exact subset_closure
  have hRbc : OpenRectangle b b ⊆ ClosedRectangle b b := by
    rw [← RectangleModelPreparation.closure_openRectangle hb hb]
    exact subset_closure
  have hFval : EqOn F (fun z ↦ F₀ ((b : ℂ)*z)) (OpenRectangle 1 1) := by
    intro z hz
    rw [hFE ⟨z,hRc hz⟩]
    exact he (t ⟨z,hRc hz⟩) ((hmul z).mpr hz)
  have hGval : EqOn G (fun w ↦ G₀ w / b) Q := by
    intro w hw
    rw [hGE ⟨w,subset_closure hw⟩]
    change (e.symm ⟨w,subset_closure hw⟩ : ℂ)/b = G₀ w/b
    rw [RectangleModelPreparation.closure_inverse_agrees hRbc F₀ G₀ e he hGmap hFG _ hw]
  have hFbij : BijOn F (OpenRectangle 1 1) Q := by
    have hscale : BijOn (fun z : ℂ ↦ (b : ℂ)*z) (OpenRectangle 1 1) (OpenRectangle b b) := by
      refine ⟨fun z hz ↦ (hmul z).mpr hz,fun _ _ _ _ hh ↦ mul_left_cancel₀ hbC hh,?_⟩
      intro w hw
      exact ⟨w/b,(hmul _).mp (by rwa [hdiv]),hdiv w⟩
    exact (hbij.comp hscale).congr hFval.symm
  have hGmaps : MapsTo G Q (OpenRectangle 1 1) := by
    intro w hw
    rw [hGval hw]
    apply (hmul _).mp
    rw [hdiv]
    exact hGmap hw
  refine ⟨F,G,E,?_,?_,?_,?_,hFbij,hGmaps,?_,?_,fun z ↦ (hFE z).symm,
    fun w ↦ (hGE w).symm,?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp E.continuous).congr (fun z ↦ (hFE z).symm)
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp E.symm.continuous).congr (fun z ↦ (hGE z).symm)
  · exact (hF₀.comp ((differentiable_const _).mul differentiable_id).differentiableOn
      (fun z hz ↦ (hmul z).mpr hz)).congr hFval
  · exact (hG₀.div_const _).congr hGval
  · intro z hz
    rw [hFE ⟨z,hz⟩,hGE (E ⟨z,hz⟩),E.symm_apply_apply]
  · intro w hw
    rw [hGE ⟨w,hw⟩,hFE (E.symm ⟨w,hw⟩),E.apply_symm_apply]
  · intro i
    let z : ClosedRectangle 1 1 := ⟨RectangleCorner 1 1 i,
      RectangleModelPreparation.corner_mem (by norm_num) (by norm_num) i⟩
    rw [hFE z]
    apply hp i (t z)
    change (b : ℂ)*RectangleCorner 1 1 i=RectangleCorner b b i
    fin_cases i <;> simp [RectangleCorner]
    ring

end HolomorphicAnosov
