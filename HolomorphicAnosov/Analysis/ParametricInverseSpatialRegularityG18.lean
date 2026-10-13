import HolomorphicAnosov.Analysis.ParametricInverseNeighborhoodG2
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

noncomputable section
open Set Filter
open scoped _root_.Topology
namespace HolomorphicAnosov.Analysis

/-- Spatial derivatives of a continuous inverse family vary continuously with
both parameter and target point. The actual inverse equation gives its derivative
by the local-left-inverse theorem. The derivative equals the inverse of the given
jointly continuous spatial derivative, composed with the same continuous inverse
family; inversion is continuous at every invertible operator. No parameter
smoothness is required. -/
theorem continuous_parametric_inverse_spatial_derivative_g18
    {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P → E → F) (g : P → F → E)
    (D : P × E → E →L[ℝ] F)
    (U : Set (P × E)) (V : Set (P × F)) (hV : IsOpen V)
    (hg : ContinuousOn (fun z : P × F ↦ g z.1 z.2) V)
    (hD : ContinuousOn D U)
    (hder : ∀ z ∈ U, HasFDerivAt (f z.1) (D z) z.2)
    (hinv : ∀ z ∈ V, f z.1 (g z.1 z.2) = z.2)
    (hmem : ∀ z ∈ V, (z.1, g z.1 z.2) ∈ U)
    (hiso : ∀ z ∈ V, (D (z.1, g z.1 z.2)).IsInvertible) :
    (∀ z ∈ V, HasFDerivAt (g z.1) (D (z.1, g z.1 z.2)).inverse z.2) ∧
      ContinuousOn (fun z : P × F ↦ fderiv ℝ (g z.1) z.2) V ∧
      ∀ p : P, ContDiffOn ℝ 1 (g p) {w | (p,w) ∈ V} := by
  have hd (z : P × F) (hz : z ∈ V) :
      HasFDerivAt (g z.1) (D (z.1, g z.1 z.2)).inverse z.2 := by
    obtain ⟨e, he⟩ := hiso z hz
    have hgc : ContinuousAt (g z.1) z.2 :=
      (hg.continuousAt (hV.mem_nhds hz)).comp
        (f := fun w : F ↦ (z.1, w)) (continuousAt_const.prodMk continuousAt_id)
    have hfg : ∀ᶠ w in 𝓝 z.2, f z.1 (g z.1 w) = w := by
      have hnear : ∀ᶠ w in 𝓝 z.2, (z.1, w) ∈ V :=
        (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hz)
      filter_upwards [hnear] with w hw
      exact hinv (z.1,w) hw
    have hf := hder (z.1, g z.1 z.2) (hmem z hz)
    rw [← he] at hf ⊢
    rw [ContinuousLinearMap.inverse_equiv]
    exact HasFDerivAt.of_local_left_inverse hgc hf hfg
  refine ⟨hd, ?_⟩
  have hc : ContinuousOn (fun z : P × F ↦ D (z.1, g z.1 z.2)) V :=
    hD.comp (continuous_fst.continuousOn.prodMk hg) hmem
  have hi : ContinuousOn (fun z : P × F ↦ (D (z.1, g z.1 z.2)).inverse) V := by
    intro z hz
    exact ((hiso z hz).contDiffAt_map_inverse (n := (0 : WithTop ℕ∞))).continuousAt.comp_continuousWithinAt (f := fun z : P × F ↦ D (z.1, g z.1 z.2)) (hc z hz)
  have hcont : ContinuousOn (fun z : P × F ↦ fderiv ℝ (g z.1) z.2) V :=
    hi.congr (fun z hz ↦ (hd z hz).fderiv)
  refine ⟨hcont, ?_⟩
  intro p
  have hopen : IsOpen {w : F | (p,w) ∈ V} :=
    hV.preimage (continuous_const.prodMk continuous_id)
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp,
    contDiffOn_succ_iff_fderiv_of_isOpen hopen]
  refine ⟨fun w hw ↦ (hd (p,w) hw).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · exact contDiffOn_zero.mpr (hcont.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hw ↦ hw))

/-- A normalized family with a continuous spatial derivative has genuine C¹
inverse maps on one common receiving ball. Restrict the source neighborhood to
the open invertibility locus, use the continuous-parameter inverse theorem,
and recover each fibre map from its product homeomorphism. Its continuous
inverse has derivative equal to the inverse spatial derivative, hence is C¹. -/
theorem parametric_c1_inverse_neighborhood_g18
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (f : P → E → E) (D : P × E → E →L[ℝ] E)
    (S : Set (P × E)) (hS : IsOpen S) (p₀ : P) (hp₀ : (p₀, 0) ∈ S)
    (hf : ContinuousOn (fun z : P × E ↦ f z.1 z.2) S)
    (hD : ContinuousOn D S)
    (hd : ∀ z ∈ S, HasFDerivAt (f z.1) (D z) z.2)
    (hzero : f p₀ 0 = 0) (hid : D (p₀, 0) = ContinuousLinearMap.id ℝ E) :
    ∃ Q : TopologicalSpace.Opens P, ∃ hpQ : p₀ ∈ Q, ∃ r : ℝ, 0 < r ∧
      ∃ e : Q → OpenPartialHomeomorph E E,
        (∀ p : Q, (e p : E → E) = f p.1 ∧
          (e p).source = {w | w ∈ Metric.ball 0 r ∧ f p.1 w ∈ Metric.ball 0 (r/8)} ∧
          (e p).target = Metric.ball 0 (r/8) ∧
          ContDiffOn ℝ 1 (e p) (e p).source ∧
          ContDiffOn ℝ 1 (e p).symm (e p).target ∧
          ∀ w ∈ (e p).source, (p.1,w) ∈ S) ∧
        ContinuousOn (fun z : Q × E ↦ (e z.1).symm z.2)
          (Set.univ ×ˢ Metric.ball 0 (r/8)) ∧
        ContinuousOn (fun z : Q × E ↦ fderiv ℝ (e z.1).symm z.2)
          (Set.univ ×ˢ Metric.ball 0 (r/8)) ∧
        0 ∈ (e ⟨p₀,hpQ⟩).source ∧
        IsOpen {z : Q × E | z.2 ∈ (e z.1).source} := by
  classical
  let S' := S ∩ {z | (D z).IsInvertible}
  have hS' : IsOpen S' :=
    hD.isOpen_inter_preimage hS ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hpS' : (p₀,0) ∈ S' := by
    refine ⟨hp₀, ?_⟩
    change (D (p₀,0)).IsInvertible
    rw [hid]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  obtain ⟨Q, hpQ, r, hr, hU, hcenter, hsub, c, hc⟩ :=
    parametric_inverse_neighborhood f D S' hS' p₀ hpS'
      (hf.mono inter_subset_left) (hD.mono inter_subset_left)
      (fun z hz ↦ hd z hz.1) hzero hid
  let B := Metric.ball (0 : E) (r/8)
  let U : Set (Q × E) := {z | z.2 ∈ Metric.ball 0 r ∧ f z.1.1 z.2 ∈ B}
  have hcp (p : Q) (w : B) : (c.symm (w,p)).1.1 = p := by
    have h := (hc (c.symm (w,p))).2
    simpa only [c.apply_symm_apply] using h.symm
  have hcf (p : Q) (w : B) : f p.1 (c.symm (w,p)).1.2 = w.1 := by
    have h := (hc (c.symm (w,p))).1
    rw [c.apply_symm_apply] at h
    simpa only [hcp] using h.symm
  let g (p : Q) (w : E) : E := if hw : w ∈ B then (c.symm (⟨w,hw⟩,p)).1.2 else 0
  have hg_eq (p : Q) (w : E) (hw : w ∈ B) :
      g p w = (c.symm (⟨w,hw⟩,p)).1.2 := by simp only [g, dite_eq_left hw]
  have hgm (p : Q) (w : E) (hw : w ∈ B) : (p,g p w) ∈ U := by
    rw [hg_eq p w hw]
    have h := (c.symm (⟨w,hw⟩,p)).property
    change (c.symm (⟨w,hw⟩,p)).1.2 ∈ Metric.ball 0 r ∧
      f (c.symm (⟨w,hw⟩,p)).1.1.1 (c.symm (⟨w,hw⟩,p)).1.2 ∈ B at h
    simpa only [U, Set.mem_ofPred_eq, hcp] using h
  have hgr (p : Q) (w : E) (hw : w ∈ B) : f p.1 (g p w) = w := by
    rw [hg_eq p w hw]
    exact hcf p ⟨w,hw⟩
  have hgl (p : Q) (w : E) (hw : (p,w) ∈ U) : g p (f p.1 w) = w := by
    rw [hg_eq p (f p.1 w) hw.2]
    have he : c (⟨(p,w),hw⟩ : U) = (⟨f p.1 w,hw.2⟩,p) := by
      exact Prod.ext (Subtype.ext (hc _).1) (hc _).2
    have he' := congrArg (fun z ↦ (c.symm z).1.2) he
    simpa only [c.symm_apply_apply] using he'.symm
  have hg : ContinuousOn (fun z : Q × E ↦ g z.1 z.2) (univ ×ˢ B) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hh : Continuous (fun z : (univ ×ˢ B : Set (Q × E)) ↦
        ((⟨z.1.2,z.2.2⟩ : B),z.1.1)) :=
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_fst.comp continuous_subtype_val)
    have hh' := continuous_snd.comp (continuous_subtype_val.comp (c.symm.continuous.comp hh))
    exact hh'.congr (fun z ↦ (hg_eq z.1.1 z.1.2 z.2.2).symm)
  let e (p : Q) : OpenPartialHomeomorph E E :=
    { toFun := f p.1
      invFun := g p
      source := {w | (p,w) ∈ U}
      target := B
      map_source' := fun _ hw ↦ hw.2
      map_target' := hgm p
      left_inv' := hgl p
      right_inv' := hgr p
      open_source := hU.preimage (continuous_const.prodMk continuous_id)
      open_target := Metric.isOpen_ball
      continuousOn_toFun := hf.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun w hw ↦ (hsub ⟨(p,w),hw⟩).1)
      continuousOn_invFun := hg.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun w hw ↦ ⟨mem_univ _, hw⟩) }
  have hDo : ContinuousOn (fun z : Q × E ↦ D (z.1.1,z.2)) U := by
    exact hD.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun z hz ↦ (hsub ⟨z,hz⟩).1)
  obtain ⟨hgd, hgD, hgC⟩ := continuous_parametric_inverse_spatial_derivative_g18
    (fun p : Q ↦ f p.1) g (fun z : Q × E ↦ D (z.1.1,z.2)) U (univ ×ˢ B)
    (isOpen_univ.prod Metric.isOpen_ball) hg hDo
    (fun z hz ↦ hd _ (hsub ⟨z,hz⟩).1)
    (fun z hz ↦ hgr z.1 z.2 hz.2)
    (fun z hz ↦ hgm z.1 z.2 hz.2)
    (fun z hz ↦ (hsub ⟨(z.1,g z.1 z.2), hgm z.1 z.2 hz.2⟩).2)
  refine ⟨Q, hpQ, r, hr, e, ?_, hg, hgD, hcenter, hU⟩
  intro p
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · have hopen : IsOpen {w | (p,w) ∈ U} :=
      hU.preimage (continuous_const.prodMk continuous_id)
    change ContDiffOn ℝ 1 (f p.1) {w | (p,w) ∈ U}
    rw [show (1 : WithTop ℕ∞) = 0+1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen hopen]
    refine ⟨fun w hw ↦ (hd _ (hsub ⟨(p,w),hw⟩).1).differentiableAt.differentiableWithinAt,
      by simp, contDiffOn_zero.mpr ?_⟩
    exact (hDo.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw ↦ hw)).congr (fun w hw ↦ (hd _ (hsub ⟨(p,w),hw⟩).1).fderiv)
  · change ContDiffOn ℝ 1 (g p) B
    simpa only [Set.mem_prod, Set.mem_univ, true_and, Set.ofPred_mem_eq] using hgC p
  · exact fun w hw ↦ (hsub ⟨(p,w),hw⟩).1

/-- The common C¹ receiving-neighborhood theorem without a normalization of the
ambient derivative or target value. Conjugate the outputs of the normalized
construction by the fixed affine homeomorphism w↦A(w)+f(p₀,0). Every resulting
partial homeomorphism is literally the original map on the whole source type. -/
theorem parametric_c1_inverse_at_equiv_g18
    {P E F : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P → E → F) (D : P × E → E →L[ℝ] F)
    (S : Set (P × E)) (hS : IsOpen S) (p₀ : P) (hp₀ : (p₀, 0) ∈ S)
    (hf : ContinuousOn (fun z : P × E ↦ f z.1 z.2) S)
    (hD : ContinuousOn D S)
    (hd : ∀ z ∈ S, HasFDerivAt (f z.1) (D z) z.2)
    (A : E ≃L[ℝ] F) (hA : D (p₀,0) = A.toContinuousLinearMap) :
    ∃ Q : TopologicalSpace.Opens P, ∃ hpQ : p₀ ∈ Q,
      ∃ V : Set F, IsOpen V ∧ f p₀ 0 ∈ V ∧
      ∃ e : Q → OpenPartialHomeomorph E F,
        (∀ p : Q, (e p : E → F) = f p.1 ∧ (e p).target = V ∧
          ContDiffOn ℝ 1 (e p) (e p).source ∧
          ContDiffOn ℝ 1 (e p).symm (e p).target ∧
          ∀ w ∈ (e p).source, (p.1,w) ∈ S) ∧
        ContinuousOn (fun z : Q × F ↦ (e z.1).symm z.2) (univ ×ˢ V) ∧
        ContinuousOn (fun z : Q × F ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ V) ∧ 0 ∈ (e ⟨p₀,hpQ⟩).source ∧
        IsOpen {z : Q × E | z.2 ∈ (e z.1).source} := by
  let f₀ : P → E → E := fun p w ↦ A.symm (f p w - f p₀ 0)
  let D₀ : P × E → E →L[ℝ] E := fun z ↦ A.symm.toContinuousLinearMap.comp (D z)
  have hf₀ : ContinuousOn (fun z : P × E ↦ f₀ z.1 z.2) S :=
    A.symm.continuous.comp_continuousOn (hf.sub continuousOn_const)
  have hD₀ : ContinuousOn D₀ S := continuousOn_const.clm_comp hD
  have hd₀ (z) (hz : z ∈ S) : HasFDerivAt (f₀ z.1) (D₀ z) z.2 :=
    A.symm.toContinuousLinearMap.hasFDerivAt.comp z.2 ((hd z hz).sub_const _)
  have hz₀ : f₀ p₀ 0 = 0 := by simp [f₀]
  have hA₀ : D₀ (p₀,0) = ContinuousLinearMap.id ℝ E := by
    simp [D₀,hA]
  obtain ⟨Q,hpQ,r,hr,e₀,he₀,hg₀,hgD₀,hcenter₀,hopen₀⟩ :=
    parametric_c1_inverse_neighborhood_g18 f₀ D₀ S hS p₀ hp₀ hf₀ hD₀ hd₀ hz₀ hA₀
  let B : E ≃ₜ F := A.toHomeomorph.trans (Homeomorph.addRight (f p₀ 0))
  have hBs : ContDiff ℝ 1 B := A.contDiff.add contDiff_const
  have hBsi : ContDiff ℝ 1 B.symm := by
    change ContDiff ℝ 1 (fun w : F ↦ A.symm (w + -(f p₀ 0)))
    exact A.symm.contDiff.comp (contDiff_id.add contDiff_const)
  have hBd (w : F) : HasFDerivAt B.symm A.symm.toContinuousLinearMap w := by
    change HasFDerivAt (fun w : F ↦ A.symm (w + -(f p₀ 0))) A.symm.toContinuousLinearMap w
    have h := A.symm.toContinuousLinearMap.hasFDerivAt.comp w
      ((hasFDerivAt_id w).add_const (-(f p₀ 0)))
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id,
      ContinuousLinearEquiv.coe_coe] using h
  let V : Set F := B.symm ⁻¹' Metric.ball 0 (r/8)
  have hV : IsOpen V := Metric.isOpen_ball.preimage B.symm.continuous
  have hbV : f p₀ 0 ∈ V := by
    change A.symm (f p₀ 0 + -(f p₀ 0)) ∈ Metric.ball 0 (r/8)
    simp only [add_neg_cancel,map_zero]
    exact Metric.mem_ball_self (by positivity)
  let e (p : Q) := (e₀ p).trans B.toOpenPartialHomeomorph
  have hes (p : Q) : (e p).source = (e₀ p).source := by
    simp [e]
  have het (p : Q) : (e p).target = V := by
    simp [e,(he₀ p).2.2.1,V]
  have heg (p : Q) : ((e p).symm : F → E) = (e₀ p).symm ∘ B.symm := rfl
  have hφ : Continuous (fun z : Q × F ↦ (z.1,B.symm z.2)) :=
    continuous_fst.prodMk (B.symm.continuous.comp continuous_snd)
  have hm : MapsTo (fun z : Q × F ↦ (z.1,B.symm z.2))
      (univ ×ˢ V) (univ ×ˢ Metric.ball 0 (r/8)) := fun _ hz ↦ ⟨mem_univ _,hz.2⟩
  refine ⟨Q,hpQ,V,hV,hbV,e,?_,hg₀.comp hφ.continuousOn hm,?_,?_,?_⟩
  · intro p
    refine ⟨?_,het p,?_,?_,?_⟩
    · funext w
      change A (e₀ p w) + f p₀ 0 = f p.1 w
      rw [(he₀ p).1]
      simp [f₀]
    · rw [hes]
      exact hBs.comp_contDiffOn (he₀ p).2.2.2.1
    · rw [het,heg]
      exact ((he₀ p).2.2.2.2.1).comp hBsi.contDiffOn
        (fun w hw ↦ by rw [(he₀ p).2.2.1]; exact hw)
    · rw [hes]
      exact (he₀ p).2.2.2.2.2
  · have hcont := (hgD₀.comp hφ.continuousOn hm).clm_comp
      (continuousOn_const (c := A.symm.toContinuousLinearMap))
    apply hcont.congr
    intro z hz
    change fderiv ℝ (e z.1).symm z.2 =
      (fderiv ℝ (e₀ z.1).symm (B.symm z.2)).comp A.symm.toContinuousLinearMap
    rw [heg]
    have ht : B.symm z.2 ∈ (e₀ z.1).target := by rw [(he₀ z.1).2.2.1]; exact hz.2
    rw [fderiv_comp z.2
      (((he₀ z.1).2.2.2.2.1.contDiffAt ((e₀ z.1).open_target.mem_nhds ht)).differentiableAt (by simp))
      (hBd z.2).differentiableAt, (hBd z.2).fderiv]

  · rw [hes]
    exact hcenter₀
  · simpa only [hes] using hopen₀

end HolomorphicAnosov.Analysis
