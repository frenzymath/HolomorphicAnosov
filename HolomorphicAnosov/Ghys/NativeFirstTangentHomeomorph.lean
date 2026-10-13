import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.Manifold.OpenSubsetInclusionTangentG9
import HolomorphicAnosov.Analysis.HolomorphicSliceFrameContinuity
import HolomorphicAnosov.Ghys.CurveScaleTangent
import HolomorphicAnosov.Ghys.CurveContactTangent
import HolomorphicAnosov.Ghys.NativeHolomorphicCurveTangency
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Ghys.CurveParamGermTangent
import HolomorphicAnosov.Ghys.NativeLeafwiseJetFlowboxContinuity

/-! First-jet tangent identification for native holomorphic flowboxes. Source: Ghys §3 pp.591–592. -/
noncomputable section
namespace HolomorphicAnosov.Ghys
open Set _root_.Topology TopologicalSpace Bundle
open scoped ContDiff Manifold
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real
variable {ι : Type u} (L : ι → Type u)
variable [∀ i, TopologicalSpace (L i)] [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]
variable [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
variable [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]

/-- Genuine first parametrization jets are the punctured selected tangent line. Source: Ghys §3 pp.591–592. -/
theorem native_first_tangent_homeomorph_coordinates_with_frames
    {D : RealTangentDistribution (realModel d) M}
    (hRank : HasComplexRankOne D)
    (U : HPS.LeafPartition D ι L (fun _ ↦ 2))
    (himm : ∀ i, ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z))
    {n : ℕ} (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
    (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
    (parametrization : ∀ i (t : T i),
      Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
        (⟨{z | (z, t.val) ∈ (c i).target},
          (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
        (branch i t) ∞)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (htarget : ∀ i p, p ∈ (c i).target → p.2 ∈ T i)
    (hparam : ∀ i (t : T i) (z : (⟨{z | (z, t.val) ∈ (c i).target},
        (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)),
      (c i).symm (z.val, t.val) =
        (U.leaf (label i t)).inclusion ((parametrization i t z).val)) :
    let K := fun x : M ↦ (hRank x).choose
    let E := fun x : M ↦ ↥(K x)
    letI : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    let P := {v : TotalSpace ℂ E // v.snd ≠ 0}
    letI := nativeLeafwiseJet1Topology L U c
    ∃ (firstTangent : NativeLeafwiseJet1 L ≃ₜ P),
    (∀ j, (firstTangent j).val.proj = nativeLeafwiseJet1Base L U j) ∧
    (∀ i (gamma : CurveParamGerm (L i)),
      let j : NativeLeafwiseJet1 L := ⟨i, curveJet1Class (L i) gamma⟩
      let representative := fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z)
      (⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩ :
        TangentBundle (complexModel d) M) =
      ⟨representative 0, mfderiv 𝓘(ℂ) (complexModel d) representative 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩) ∧
    (∀ (omega : ℂˣ) j,
      (firstTangent (nativeLeafwiseJet1Scale L omega j)).val =
        ⟨(firstTangent j).val.proj, (omega : ℂ) • (firstTangent j).val.snd⟩) ∧
    (∀ (k : Fin n) (x : M) (j : NativeLeafwiseJet1 L),
      nativeLeafwiseJet1Base L U j ∈ (c k).source →
      nativeLeafwiseJet1Base L U j ∈ (chartAt (ComplexModel d) x).source →
      (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
        (⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩ :
          TangentBundle (complexModel d) M)).2 =
        (nativeLeafwiseJet1Coeff L U (c k) j).2 •
          deriv (fun z ↦ chartAt (ComplexModel d) x
            ((c k).symm (z, (c k (nativeLeafwiseJet1Base L U j)).2)))
            (c k (nativeLeafwiseJet1Base L U j)).1) ∧
    (∀ (k : Fin n) (ψ : OpenPartialHomeomorph M (ComplexModel d)),
      ψ ∈ IsManifold.maximalAtlas (complexModel d) ∞ M →
      ContinuousOn
        (fun p : ℂ × (Fin (2*d-2) → ℝ) ↦
          deriv (fun z ↦ ψ ((c k).symm (z, p.2))) p.1)
        ((c k).target ∩ (c k).symm ⁻¹' ψ.source)) ∧
    (∀ x : M, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ frame : O → P, Continuous frame ∧ ∀ y, (frame y).val.proj = y.val) := by
  let K := fun x : M ↦ (hRank x).choose
  let E := fun x : M ↦ ↥(K x)
  let P := {v : TotalSpace ℂ E // v.snd ≠ 0}
  have htangent_mem (i : ι) (gamma : CurveParamGerm (L i)) :
      mfderiv 𝓘(ℂ) (complexModel d)
          ((U.leaf i).inclusion ∘ gamma.val.out) 0
          ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1) ∈
        K ((U.leaf i).inclusion (gamma.val.out 0)) :=
    native_holomorphic_curve_tangent_mem hRank (U.leaf i) (himm i).1 gamma _
  have htangent_nonzero (i : ι) (gamma : CurveParamGerm (L i)) :
      mfderiv 𝓘(ℂ) (complexModel d)
          ((U.leaf i).inclusion ∘ gamma.val.out) 0
          ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1) ≠ 0 :=
    curveParamGerm_immersion_tangent_ne_zero (I := complexModel d)
      (U.leaf i).inclusion (himm i).1 (himm i).2 gamma
  let representativeTangent (i : ι) (gamma : CurveParamGerm (L i)) : P :=
    ⟨⟨(U.leaf i).inclusion (gamma.val.out 0),
      ⟨mfderiv 𝓘(ℂ) (complexModel d)
          ((U.leaf i).inclusion ∘ gamma.val.out) 0
          ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1), htangent_mem i gamma⟩⟩,
      fun h ↦ htangent_nonzero i gamma (congrArg Subtype.val h)⟩
  have hline_injective : Function.Injective
      (fun v : TotalSpace ℂ E ↦
        (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) := by
    rintro ⟨x, v⟩ ⟨y, w⟩ h
    have hb : x = y := congrArg TotalSpace.proj h
    subst y
    have hv : v.val = w.val := TotalSpace.mk_injective x h
    have he : v = w := Subtype.ext hv
    cases he
    rfl
  have hrepresentative_contact (i : ι) (γ δ : CurveParamGerm (L i))
      (h : CurveContact1 (L i) γ δ) :
      representativeTangent i γ = representativeTangent i δ := by
    apply Subtype.ext
    apply hline_injective
    exact curveContact1_ambient_tangent_eq (complexModel d)
      (U.leaf i).inclusion (himm i).1 γ δ h
  let tangentMap : NativeLeafwiseJet1 L → P := fun j ↦
    Quotient.lift (representativeTangent j.1) (hrepresentative_contact j.1) j.2
  have htangent_representative (i : ι) (γ : CurveParamGerm (L i)) :
      tangentMap ⟨i, curveJet1Class (L i) γ⟩ = representativeTangent i γ := rfl
  have htangent_base (j : NativeLeafwiseJet1 L) :
      (tangentMap j).val.proj = nativeLeafwiseJet1Base L U j := by
    rcases j with ⟨i, j⟩
    refine Quotient.inductionOn j ?_
    intro γ
    change (U.leaf i).inclusion (γ.val.out 0) =
      (U.leaf i).inclusion (curveJet1Base (L i) (curveJet1Class (L i) γ))
    rw [(leaf_jet_complex_manifold (L i)).2.1 γ |>.1]
    apply congrArg (U.leaf i).inclusion
    conv_rhs => rw [← Quotient.out_eq γ.val]
    rfl
  have htangent_injective : Function.Injective tangentMap := by
    rintro ⟨i, j⟩ ⟨k, q⟩ h
    have hb : nativeLeafwiseJet1Base L U ⟨i, j⟩ =
        nativeLeafwiseJet1Base L U ⟨k, q⟩ := by
      rw [← htangent_base, ← htangent_base, h]
    have hik : i = k := U.disjoint i k _ _ hb
    subst k
    apply congrArg (fun t : CurveJet1 (L i) ↦ (⟨i, t⟩ : NativeLeafwiseJet1 L))
    revert h
    refine Quotient.inductionOn₂ j q ?_
    intro γ δ h
    apply Quotient.sound
    apply (curveContact1_iff_ambient_tangent_eq (complexModel d)
      (U.leaf i).inclusion (himm i).1 (U.leaf i).injective (himm i).2 γ δ).mpr
    exact congrArg (fun v : P ↦
      (⟨v.val.proj, v.val.snd.val⟩ : TangentBundle (complexModel d) M)) h
  have htangent_scale (omega : ℂˣ) (j : NativeLeafwiseJet1 L) :
      (tangentMap (nativeLeafwiseJet1Scale L omega j)).val =
        ⟨(tangentMap j).val.proj, (omega : ℂ) • (tangentMap j).val.snd⟩ := by
    apply hline_injective
    rcases j with ⟨i, j⟩
    refine Quotient.inductionOn j ?_
    intro γ
    exact curveParamGerm_scale_ambient_tangent (complexModel d)
      (U.leaf i).inclusion (himm i).1 γ omega
  have htangent_surjective : Function.Surjective tangentMap := by
    rintro ⟨⟨x, v⟩, hv⟩
    obtain ⟨i, z, hz⟩ := U.cover x
    let chart := chartAt ℂ z
    obtain ⟨e, he0, he, hei, heb, _, _⟩ :=
      curve_quadratic_parametrization chart (IsManifold.chart_mem_maximalAtlas z)
        (chart z) 1 0 (chart.map_source (mem_chart_source ℂ z)) one_ne_zero
    let γ : CurveParamGerm (L i) :=
      ⟨((e : ℂ → L i) : CurveGerm (L i)), e, he0, he, hei, rfl⟩
    let j : NativeLeafwiseJet1 L := ⟨i, curveJet1Class (L i) γ⟩
    have hjbase : nativeLeafwiseJet1Base L U j = x := by
      change (U.leaf i).inclusion (curveJet1Base (L i) (curveJet1Class (L i) γ)) = x
      rw [(leaf_jet_complex_manifold (L i)).2.1 γ |>.1]
      have hγbase : curveGermBase (L i) γ.val = z := by
        change e 0 = z
        rw [heb, chart.left_inv (mem_chart_source ℂ z)]
      rw [hγbase, hz]
    have hj : (tangentMap j).val.proj = x := (htangent_base j).trans hjbase
    generalize hq : tangentMap j = q at hj
    rcases q with ⟨⟨y, w⟩, hw⟩
    change y = x at hj
    subst y
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      (hRank x).choose_spec.1 hw v
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      apply hv
      simpa only [zero_smul] using ha.symm
    refine ⟨nativeLeafwiseJet1Scale L (Units.mk0 a ha0) j, ?_⟩
    apply Subtype.ext
    rw [htangent_scale, hq]
    exact TotalSpace.ext rfl (heq_of_eq ha)
  let tangentEquiv : NativeLeafwiseJet1 L ≃ P :=
    Equiv.ofBijective tangentMap ⟨htangent_injective, htangent_surjective⟩
  have hslice (k : Fin n) (t : T k) :
      ContMDiff 𝓘(ℂ) (complexModel d) ∞
        (fun z : (⟨{z | (z, t.val) ∈ (c k).target},
          (c k).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ) ↦
          (c k).symm (z.val, t.val)) := by
    have hp := contMDiff_subtype_val.comp (parametrization k t).contMDiff
    convert (himm (label k t)).1.comp hp using 1
    funext z
    exact hparam k t z
  have hslice_on (k : Fin n) (t : T k) :
      ContMDiffOn 𝓘(ℂ) (complexModel d) ∞
        (fun z : ℂ ↦ (c k).symm (z, t.val)) {z | (z, t.val) ∈ (c k).target} := by
    intro z hz
    exact ((contMDiffAt_subtype_iff (I := 𝓘(ℂ)) (I' := complexModel d)
      (U := (⟨{z | (z, t.val) ∈ (c k).target},
        (c k).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ))
      (f := fun z : ℂ ↦ (c k).symm (z, t.val))).mp
      ((hslice k t).contMDiffAt (x := ⟨z, hz⟩))).contMDiffWithinAt
  have hslice_injective (k : Fin n) (t : T k) (z : ℂ)
      (hz : (z, t.val) ∈ (c k).target) :
      Function.Injective (mfderiv 𝓘(ℂ) (complexModel d)
        (fun w : ℂ ↦ (c k).symm (w, t.val)) z) := by
    let V : Opens ℂ := ⟨{w | (w, t.val) ∈ (c k).target},
      (c k).open_target.preimage (continuous_id.prodMk continuous_const)⟩
    let z' : V := ⟨z, hz⟩
    let e := parametrization k t
    have he : Function.Bijective (mfderiv 𝓘(ℂ) 𝓘(ℂ) e z') :=
      (e.toOpenPartialHomeomorph_mdifferentiable
        (show (∞ : WithTop ℕ∞) ≠ 0 by simp)).mfderiv_bijective (by simp)
    have hbranch := openSubsetInclusion_mfderiv_bijective 𝓘(ℂ) (branch k t) (e z')
    have hdomain := openSubsetInclusion_mfderiv_bijective 𝓘(ℂ) V z'
    have hrestricted : Function.Injective (mfderiv 𝓘(ℂ) (complexModel d)
        (fun w : V ↦ (c k).symm (w.val, t.val)) z') := by
      have hf : (fun w : V ↦ (c k).symm (w.val, t.val)) =
          (U.leaf (label k t)).inclusion ∘ ((Subtype.val : branch k t → L (label k t)) ∘ e) :=
        funext (hparam k t)
      rw [hf, mfderiv_comp z' ((himm _).1.mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp) _)
        ((contMDiff_subtype_val.comp e.contMDiff).mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp) _),
        mfderiv_comp z' (contMDiff_subtype_val.mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp) _)
          (e.mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp) _)]
      exact ((himm _).2 _).comp (hbranch.injective.comp he.injective)
    have hd := ((hslice_on k t).contMDiffAt (V.isOpen.mem_nhds hz)).mdifferentiableAt
      (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    change Function.Injective (mfderiv 𝓘(ℂ) (complexModel d)
      ((fun w : ℂ ↦ (c k).symm (w, t.val)) ∘ (Subtype.val : V → ℂ)) z') at hrestricted
    rw [mfderiv_comp z' hd (contMDiff_subtype_val.mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp) _)] at hrestricted
    exact Function.Injective.of_comp_right hrestricted hdomain.surjective
  have hframe_nonzero (k : Fin n) (ψ : OpenPartialHomeomorph M (ComplexModel d))
      (hψ : ψ ∈ IsManifold.maximalAtlas (complexModel d) ∞ M)
      (p : ℂ × (Fin (2*d-2) → ℝ))
      (hp : p ∈ (c k).target ∩ (c k).symm ⁻¹' ψ.source) :
      deriv (fun z ↦ ψ ((c k).symm (z, p.2))) p.1 ≠ 0 := by
    let t : T k := ⟨p.2, htarget k p hp.1⟩
    have hψd : ψ.MDifferentiable (complexModel d) 𝓘(ℂ, ComplexModel d) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas hψ).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas hψ).mdifferentiableOn (by simp)⟩
    have hd := ((hslice_on k t).contMDiffAt
      (((c k).open_target.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp.1)).mdifferentiableAt
      (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    have hi : Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ, ComplexModel d)
        (fun z ↦ ψ ((c k).symm (z, p.2))) p.1) := by
      change Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ, ComplexModel d)
        (ψ ∘ (fun z ↦ (c k).symm (z, p.2))) p.1)
      rw [mfderiv_comp p.1 (hψd.mdifferentiableAt hp.2) hd]
      exact (hψd.mfderiv_injective hp.2).comp (hslice_injective k t p.1 hp.1)
    rw [mfderiv_eq_fderiv] at hi
    intro hzero
    have hunit : (1 : ℂ) = 0 := hi (hzero.trans (map_zero _).symm)
    exact one_ne_zero hunit
  have hframe_coordinates (k : Fin n) (ψ : OpenPartialHomeomorph M (ComplexModel d))
      (hψ : ψ ∈ IsManifold.maximalAtlas (complexModel d) ∞ M) :
      ContinuousOn
        (fun p : ℂ × (Fin (2*d-2) → ℝ) ↦
          deriv (fun z ↦ ψ ((c k).symm (z, p.2))) p.1)
        ((c k).target ∩ (c k).symm ⁻¹' ψ.source) := by
    have hopen : IsOpen ((c k).target ∩ (c k).symm ⁻¹' ψ.source) :=
      (c k).symm.continuousOn.isOpen_inter_preimage (c k).open_target ψ.open_source
    have hcont : ContinuousOn (fun p ↦ ψ ((c k).symm p))
        ((c k).target ∩ (c k).symm ⁻¹' ψ.source) :=
      ψ.continuousOn.comp ((c k).symm.continuousOn.mono inter_subset_left)
        (fun _ hp ↦ hp.2)
    apply holomorphic_slice_vector_derivative_continuousOn _ hopen _ hcont
    intro t
    by_cases ht : t ∈ T k
    · exact (contMDiffOn_iff_contDiffOn.mp
        ((contMDiffOn_of_mem_maximalAtlas hψ).comp
          ((hslice_on k ⟨t, ht⟩).mono (fun _ hz ↦ hz.1))
          (fun _ hz ↦ hz.2))).differentiableOn (by simp)
    · intro z hz
      exact (ht (htarget k (z, t) hz.1)).elim
  have hframe_formula (k : Fin n) (ψ : OpenPartialHomeomorph M (ComplexModel d))
      (hψ : ψ ∈ IsManifold.maximalAtlas (complexModel d) ∞ M)
      (i : ι) (γ : CurveParamGerm (L i))
      (hz : (U.leaf i).inclusion (curveGermBase (L i) γ.val) ∈ (c k).source)
      (hchart : (U.leaf i).inclusion (curveGermBase (L i) γ.val) ∈ ψ.source) :
      deriv (fun z ↦ ψ ((U.leaf i).inclusion (γ.val.out z))) 0 =
        germFirst (γ.val.map (nativeLeafFlowboxScalar L U (c k) i)) •
          deriv (fun z ↦ ψ ((c k).symm
            (z, (c k ((U.leaf i).inclusion (curveGermBase (L i) γ.val))).2)))
            (c k ((U.leaf i).inclusion (curveGermBase (L i) γ.val))).1 := by
    let t : T k := ⟨(c k ((U.leaf i).inclusion (curveGermBase (L i) γ.val))).2,
      htarget k _ ((c k).map_source hz)⟩
    let w : (⟨{w | (w, t.val) ∈ (c k).target},
        (c k).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ) :=
      ⟨(c k ((U.leaf i).inclusion (curveGermBase (L i) γ.val))).1,
        (c k).map_source hz⟩
    have hw : (U.leaf (label k t)).inclusion ((parametrization k t w).val) =
        (U.leaf i).inclusion (curveGermBase (L i) γ.val) := by
      rw [← hparam k t w]
      exact (c k).left_inv hz
    have htw : c k ((U.leaf i).inclusion (curveGermBase (L i) γ.val)) =
        (w.val, t.val) := rfl
    have hi : label k t = i := U.disjoint _ _ _ _ hw
    clear_value w t
    cases hi
    have hpoint : (parametrization k t w).val =
        curveGermBase (L (label k t)) γ.val := (U.leaf _).injective hw
    have hbranch : curveGermBase (L (label k t)) γ.val ∈ branch k t :=
      hpoint ▸ (parametrization k t w).property
    let φ := nativeLeafFlowboxScalar L U (c k) (label k t)
    have hflow (y : branch k t) :
        c k ((U.leaf (label k t)).inclusion y.val) =
          (((parametrization k t).symm y).val, t.val) := by
      have hp := hparam k t ((parametrization k t).symm y)
      rw [(parametrization k t).apply_symm_apply] at hp
      rw [← hp]
      exact (c k).right_inv ((parametrization k t).symm y).property
    have hφ (y : branch k t) : φ y.val = ((parametrization k t).symm y).val :=
      congrArg Prod.fst (hflow y)
    have hfactor (y : branch k t) :
        (U.leaf (label k t)).inclusion y.val = (c k).symm (φ y.val, t.val) := by
      rw [hφ y, hparam k t ((parametrization k t).symm y),
        (parametrization k t).apply_symm_apply]
    have hb : γ.val.out 0 = curveGermBase (L (label k t)) γ.val := by
      conv_rhs => rw [← Quotient.out_eq γ.val]
      rfl
    have hγ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) γ.val.out 0 :=
      mdifferentiableAt_of_mfderiv_injective (curveParamGerm_mfderiv_bijective γ).injective
    have hφsmooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (γ.val.out 0) := by
      rw [hb]
      exact contMDiffAt_subtype_iff.mp
        (((contMDiff_subtype_val.comp (parametrization k t).symm.contMDiff).congr hφ).contMDiffAt
          (x := ⟨curveGermBase (L (label k t)) γ.val, hbranch⟩))
    have hφγ : DifferentiableAt ℂ (φ ∘ γ.val.out) 0 :=
      mdifferentiableAt_iff_differentiableAt.mp
        ((hφsmooth.mdifferentiableAt (by simp)).comp 0 hγ)
    have hφbase : φ (γ.val.out 0) = w.val := by
      rw [hb]
      exact congrArg Prod.fst htw
    have hs : DifferentiableAt ℂ (fun z ↦ ψ ((c k).symm (z, t.val))) w.val := by
      have hsmooth := (hslice_on k t).contMDiffAt
        (((c k).open_target.preimage (continuous_id.prodMk continuous_const)).mem_nhds w.property)
      have hmem : (c k).symm (w.val, t.val) ∈ ψ.source := by
        rw [hparam k t w, hpoint]
        exact hchart
      have hψsmooth := (contMDiffOn_of_mem_maximalAtlas hψ).contMDiffAt
        (ψ.open_source.mem_nhds hmem)
      exact (hψsmooth.comp w.val hsmooth).contDiffAt.differentiableAt (by simp)
    have hevent : (fun z ↦ ψ ((U.leaf (label k t)).inclusion (γ.val.out z))) =ᶠ[𝓝 0]
        (fun z ↦ ψ ((c k).symm (z, t.val))) ∘ (φ ∘ γ.val.out) := by
      filter_upwards [hγ.continuousAt.preimage_mem_nhds
        ((branch k t).isOpen.mem_nhds (hb ▸ hbranch))] with z hz'
      exact congrArg ψ (hfactor ⟨γ.val.out z, hz'⟩)
    have hcoef : germFirst (γ.val.map φ) = deriv (φ ∘ γ.val.out) 0 := by
      conv_lhs => rw [← Quotient.out_eq γ.val]
      rfl
    rw [hevent.deriv_eq, htw]
    change deriv ((fun z ↦ ψ ((c k).symm (z, t.val))) ∘ (φ ∘ γ.val.out)) 0 =
      germFirst (γ.val.map φ) • deriv (fun z ↦ ψ ((c k).symm (z, t.val))) w.val
    rw [hcoef]
    exact (hs.hasDerivAt.scomp_of_eq 0 hφγ.hasDerivAt hφbase.symm).deriv
  let ambient : NativeLeafwiseJet1 L → TangentBundle (complexModel d) M :=
    fun j ↦ ⟨(tangentMap j).val.proj, (tangentMap j).val.snd.val⟩
  have hambient_base (j : NativeLeafwiseJet1 L) :
      (ambient j).proj = nativeLeafwiseJet1Base L U j := htangent_base j
  have hcoord (k : Fin n) (x : M) (j : NativeLeafwiseJet1 L)
      (hj : nativeLeafwiseJet1Base L U j ∈ (c k).source)
      (hx : nativeLeafwiseJet1Base L U j ∈ (chartAt (ComplexModel d) x).source) :
      (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x (ambient j)).2 =
        (nativeLeafwiseJet1Coeff L U (c k) j).2 •
          deriv (fun z ↦ chartAt (ComplexModel d) x
            ((c k).symm (z, (c k (nativeLeafwiseJet1Base L U j)).2)))
            (c k (nativeLeafwiseJet1Base L U j)).1 := by
    let ψ := chartAt (ComplexModel d) x
    have hψ : ψ ∈ IsManifold.maximalAtlas (complexModel d) ∞ M :=
      IsManifold.chart_mem_maximalAtlas x
    rw [TangentBundle.trivializationAt_apply]
    change tangentCoordChange (complexModel d) (ambient j).proj x (ambient j).proj
      (ambient j).snd = _
    rw [← mfderiv_chartAt_eq_tangentCoordChange (I := complexModel d)
      (hambient_base j ▸ hx)]
    rcases j with ⟨i, q⟩
    let γ := q.out
    have hq : curveJet1Class (L i) γ = q := Quotient.out_eq q
    have hb : nativeLeafwiseJet1Base L U ⟨i, q⟩ =
        (U.leaf i).inclusion (curveGermBase (L i) γ.val) := by
      rw [← hq]
      exact congrArg (U.leaf i).inclusion
        ((leaf_jet_complex_manifold (L i)).2.1 γ |>.1)
    have hb0 : γ.val.out 0 = curveGermBase (L i) γ.val := by
      conv_rhs => rw [← Quotient.out_eq γ.val]
      rfl
    have ha : ambient ⟨i, q⟩ =
        (⟨(U.leaf i).inclusion (γ.val.out 0),
          mfderiv 𝓘(ℂ) (complexModel d) ((U.leaf i).inclusion ∘ γ.val.out) 0
            ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩ :
          TangentBundle (complexModel d) M) := by
      rw [← hq]
      rfl
    rw [ha]
    have hdγ := mdifferentiableAt_of_mfderiv_injective
      (curveParamGerm_mfderiv_bijective γ).injective
    have hd := ((himm i).1.mdifferentiable (by simp) _).comp 0 hdγ
    have hψd : MDifferentiableAt (complexModel d) 𝓘(ℂ, ComplexModel d) ψ
        ((U.leaf i).inclusion (γ.val.out 0)) :=
      ((contMDiffOn_of_mem_maximalAtlas hψ).contMDiffAt
        (ψ.open_source.mem_nhds (by simpa only [hb, hb0] using hx))).mdifferentiableAt
        (by simp)
    have hderiv := mfderiv_comp (I := 𝓘(ℂ)) (I' := complexModel d)
      (I'' := 𝓘(ℂ, ComplexModel d)) 0 hψd hd
    have heq := congrArg (fun f ↦ f ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)) hderiv
    rw [mfderiv_eq_fderiv] at heq
    change deriv (ψ ∘ ((U.leaf i).inclusion ∘ γ.val.out)) 0 = _ at heq
    refine heq.symm.trans ?_
    have hf := hframe_formula k ψ hψ i γ (hb ▸ hj) (hb ▸ hx)
    simpa only [nativeLeafwiseJet1Coeff, hb, γ, Function.comp_def] using hf
  let frame (k : Fin n) (x y : M) : ComplexModel d :=
    deriv (fun z ↦ chartAt (ComplexModel d) x ((c k).symm (z, (c k y).2))) (c k y).1
  have hframeOn (k : Fin n) (x : M) : ContinuousOn (frame k x)
      ((c k).source ∩ (chartAt (ComplexModel d) x).source) := by
    apply (hframe_coordinates k (chartAt (ComplexModel d) x)
      (IsManifold.chart_mem_maximalAtlas x)).comp
      ((c k).continuousOn.mono inter_subset_left)
    intro y hy
    exact ⟨(c k).map_source hy.1, by simpa only [Set.mem_preimage, (c k).left_inv hy.1] using hy.2⟩
  have hframeNe (k : Fin n) (x y : M)
      (hy : y ∈ (c k).source ∩ (chartAt (ComplexModel d) x).source) : frame k x y ≠ 0 := by
    exact hframe_nonzero k (chartAt (ComplexModel d) x)
      (IsManifold.chart_mem_maximalAtlas x) (c k y)
      ⟨(c k).map_source hy.1, by simpa only [Set.mem_preimage, (c k).left_inv hy.1] using hy.2⟩
  let lineInclusion : TotalSpace ℂ E → TangentBundle (complexModel d) M :=
    fun v ↦ ⟨v.proj, v.snd.val⟩
  let : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced lineInclusion inferInstance
  let := nativeLeafwiseJet1Topology L U c
  have hflow := nativeLeafwiseJet_flowbox_continuity L U c
  have hbaseCont : Continuous (nativeLeafwiseJet1Base L U) := (hflow.2.2 hcover).1
  have hambientCont : Continuous ambient := by
    rw [continuous_iff_continuousAt]
    intro j
    apply (FiberBundle.continuousAt_totalSpace (ComplexModel d) ambient).mpr
    refine ⟨hbaseCont.continuousAt.congr (Filter.Eventually.of_forall (fun q ↦
      (hambient_base q).symm)), ?_⟩
    let x := (ambient j).proj
    obtain ⟨k, hk⟩ := hcover (nativeLeafwiseJet1Base L U j)
    have hx : nativeLeafwiseJet1Base L U j ∈ (chartAt (ComplexModel d) x).source := by
      rw [← hambient_base]
      exact mem_chart_source _ _
    have hf := (hframeOn k x).continuousAt
      (((c k).open_source.inter (chartAt (ComplexModel d) x).open_source).mem_nhds ⟨hk, hx⟩)
    have ha := ((hflow.1 k).2.continuousAt ((hflow.1 k).1.mem_nhds hk)).snd
    apply (ha.smul (hf.comp hbaseCont.continuousAt)).congr
    filter_upwards [(hflow.1 k).1.mem_nhds hk,
      hbaseCont.continuousAt.preimage_mem_nhds
        ((chartAt (ComplexModel d) x).open_source.mem_nhds hx)] with q hq hqx
    exact (hcoord k x q hq hqx).symm
  have htangentCont : Continuous tangentEquiv := by
    apply Continuous.subtype_mk
    exact continuous_induced_rng.mpr hambientCont
  have hinclusionCont : Continuous (fun v : P ↦ lineInclusion v.val) :=
    (show Continuous lineInclusion from continuous_induced_dom).comp
      (continuous_subtype_val : Continuous (Subtype.val : P → TotalSpace ℂ E))
  have hbaseInv : Continuous (fun v : P ↦ nativeLeafwiseJet1Base L U (tangentEquiv.symm v)) := by
    have h := (FiberBundle.continuous_proj (ComplexModel d) (TangentSpace (complexModel d))).comp hinclusionCont
    convert h using 1
    funext v
    rw [← htangent_base]
    change (tangentEquiv (tangentEquiv.symm v)).val.proj = v.val.proj
    rw [tangentEquiv.apply_symm_apply]
  have hbInv (v : P) : nativeLeafwiseJet1Base L U (tangentEquiv.symm v) = v.val.proj := by
    rw [← htangent_base]
    change (tangentEquiv (tangentEquiv.symm v)).val.proj = v.val.proj
    rw [tangentEquiv.apply_symm_apply]
  have haInv (v : P) : ambient (tangentEquiv.symm v) = lineInclusion v.val := by
    change lineInclusion (tangentEquiv (tangentEquiv.symm v)).val = _
    rw [tangentEquiv.apply_symm_apply]
  have hcoeffInv (k : Fin n) :
      ContinuousOn (fun v : P ↦ nativeLeafwiseJet1Coeff L U (c k) (tangentEquiv.symm v))
        {v | nativeLeafwiseJet1Base L U (tangentEquiv.symm v) ∈ (c k).source} := by
    intro v hv
    have hfirst := ((c k).continuousAt hv).comp (x := v) hbaseInv.continuousAt
    have hsecond : ContinuousAt
        (fun w : P ↦ (nativeLeafwiseJet1Coeff L U (c k) (tangentEquiv.symm w)).2) v := by
      let x := v.val.proj
      have hx : nativeLeafwiseJet1Base L U (tangentEquiv.symm v) ∈
          (chartAt (ComplexModel d) x).source := by
        rw [hbInv]
        exact mem_chart_source _ _
      have hf := ((hframeOn k x).continuousAt
        (((c k).open_source.inter (chartAt (ComplexModel d) x).open_source).mem_nhds
          ⟨hv, hx⟩)).comp (x := v) hbaseInv.continuousAt
      obtain ⟨l, hl⟩ : ∃ l : Fin d,
          frame k x (nativeLeafwiseJet1Base L U (tangentEquiv.symm v)) l ≠ 0 := by
        by_contra! h
        apply hframeNe k x _ ⟨hv, hx⟩
        funext l
        exact h l
      let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
      have he : lineInclusion v.val ∈ e.source := by
        change v.val.proj ∈ (chartAt (ComplexModel d) x).source
        exact mem_chart_source _ _
      have ht := (e.continuousAt he).comp (x := v) hinclusionCont.continuousAt
      have hnum := (continuous_apply l).continuousAt.comp ht.snd
      have hden := (continuous_apply l).continuousAt.comp hf
      apply (hnum.div hden hl).congr
      filter_upwards [hbaseInv.continuousAt.preimage_mem_nhds ((c k).open_source.mem_nhds hv),
        hbaseInv.continuousAt.preimage_mem_nhds
          ((chartAt (ComplexModel d) x).open_source.mem_nhds hx),
        hden.eventually_ne hl] with w hw hwx hwn
      have h := congrArg (fun a : ComplexModel d ↦ a l)
        (hcoord k x (tangentEquiv.symm w) hw hwx)
      rw [haInv] at h
      change (e (lineInclusion w.val)).2 l =
        (nativeLeafwiseJet1Coeff L U (c k) (tangentEquiv.symm w)).2 *
          frame k x (nativeLeafwiseJet1Base L U (tangentEquiv.symm w)) l at h
      exact ((eq_div_iff hwn).mpr h.symm).symm
    exact (hfirst.prodMk hsecond).continuousWithinAt
  have hinvCont : Continuous tangentEquiv.symm := by
    apply continuous_generateFrom_iff.mpr
    rintro O ⟨k, W, hW, rfl⟩
    exact (hcoeffInv k).isOpen_inter_preimage
      ((c k).open_source.preimage hbaseInv) hW
  have hlocalFrame : ∀ x : M, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ fr : O → P, Continuous fr ∧ ∀ y, (fr y).val.proj = y.val := by
    intro x
    obtain ⟨k, hk⟩ := hcover x
    let O : Set M := (c k).source ∩ (chartAt (ComplexModel d) x).source
    have hO : IsOpen O := (c k).open_source.inter (chartAt (ComplexModel d) x).open_source
    let w (y : M) : E y :=
      (Module.nonempty_linearEquiv_of_finrank_eq_one (hRank y).choose_spec.1).some 1
    have hw (y : M) : w y ≠ 0 :=
      (Module.nonempty_linearEquiv_of_finrank_eq_one
        (hRank y).choose_spec.1).some.map_ne_zero_iff.mpr one_ne_zero
    let v (y : M) : P := ⟨⟨y,w y⟩, hw y⟩
    let j (y : M) := tangentEquiv.symm (v y)
    have hj (y : M) : nativeLeafwiseJet1Base L U (j y) = y := hbInv (v y)
    have hjamb (y : M) : ambient (j y) = lineInclusion (v y).val := haInv (v y)
    let a (y : M) := (nativeLeafwiseJet1Coeff L U (c k) (j y)).2
    let et := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
    have hcoords (y : O) :
        (et (lineInclusion (v y.val).val)).2 = a y.val • frame k x y.val := by
      have hh := hcoord k x (j y.val) (by rw [hj]; exact y.property.1)
        (by rw [hj]; exact y.property.2)
      rw [hjamb, hj] at hh
      exact hh
    have ha (y : O) : a y.val ≠ 0 := by
      intro hz
      have hh := hcoords y
      rw [hz, zero_smul] at hh
      apply hw y.val
      apply Subtype.ext
      have hlin := (et.linearEquivAt ℂ y.val y.property.2).injective
      apply hlin
      change (et (lineInclusion (v y.val).val)).2 = _
      exact hh.trans ((et.linearEquivAt ℂ y.val y.property.2).map_zero).symm
    let fr (y : O) : P :=
      ⟨⟨y.val, (a y.val)⁻¹ • w y.val⟩, smul_ne_zero (inv_ne_zero (ha y)) (hw y.val)⟩
    have hfrcoord (y : O) :
        (et (lineInclusion (fr y).val)).2 = frame k x y.val := by
      change et.linearEquivAt ℂ y.val y.property.2 ((a y.val)⁻¹ • (w y.val).val) = _
      rw [map_smul]
      change (a y.val)⁻¹ • (et (lineInclusion (v y.val).val)).2 = _
      rw [hcoords, smul_smul, inv_mul_cancel₀ (ha y), one_smul]
    have hfrCont : Continuous (fun y : O ↦ lineInclusion (fr y).val) := by
      have hc : Continuous (fun y : O ↦ (y.val, frame k x y.val)) :=
        continuous_subtype_val.prodMk (continuousOn_iff_continuous_domRestrict.mp (hframeOn k x))
      have hc' := et.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous hc
        (fun y : O ↦ et.mem_target.mpr y.property.2)
      apply hc'.congr
      intro y
      have he : lineInclusion (fr y).val ∈ et.source := et.mem_source.mpr y.property.2
      have hpair : et (lineInclusion (fr y).val) = (y.val, frame k x y.val) := by
        apply Prod.ext
        · exact et.coe_fst he
        · exact hfrcoord y
      change et.toOpenPartialHomeomorph.symm (y.val, frame k x y.val) = _
      rw [← hpair]
      exact et.toOpenPartialHomeomorph.left_inv he
    refine ⟨O, hO, ⟨hk, mem_chart_source _ _⟩, fr, ?_, fun y ↦ rfl⟩
    apply Continuous.subtype_mk
    exact continuous_induced_rng.mpr hfrCont
  refine ⟨⟨tangentEquiv, htangentCont, hinvCont⟩, htangent_base, ?_, htangent_scale,
    hcoord, hframe_coordinates, hlocalFrame⟩
  intro i γ
  rfl

/-- The original local-frame interface, obtained from the joint coordinate and frame theorem. -/
theorem native_first_tangent_homeomorph_with_frames
    {D : RealTangentDistribution (realModel d) M}
    (hRank : HasComplexRankOne D)
    (U : HPS.LeafPartition D ι L (fun _ ↦ 2))
    (himm : ∀ i, ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z))
    {n : ℕ} (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
    (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
    (parametrization : ∀ i (t : T i),
      Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
        (⟨{z | (z, t.val) ∈ (c i).target},
          (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
        (branch i t) ∞)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (htarget : ∀ i p, p ∈ (c i).target → p.2 ∈ T i)
    (hparam : ∀ i (t : T i) (z : (⟨{z | (z, t.val) ∈ (c i).target},
        (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)),
      (c i).symm (z.val, t.val) =
        (U.leaf (label i t)).inclusion ((parametrization i t z).val)) :
    let K := fun x : M ↦ (hRank x).choose
    let E := fun x : M ↦ ↥(K x)
    letI : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    let P := {v : TotalSpace ℂ E // v.snd ≠ 0}
    letI := nativeLeafwiseJet1Topology L U c
    ∃ (firstTangent : NativeLeafwiseJet1 L ≃ₜ P),
    (∀ j, (firstTangent j).val.proj = nativeLeafwiseJet1Base L U j) ∧
    (∀ i (gamma : CurveParamGerm (L i)),
      let j : NativeLeafwiseJet1 L := ⟨i, curveJet1Class (L i) gamma⟩
      let representative := fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z)
      (⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩ :
        TangentBundle (complexModel d) M) =
      ⟨representative 0, mfderiv 𝓘(ℂ) (complexModel d) representative 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩) ∧
    (∀ (omega : ℂˣ) j,
      (firstTangent (nativeLeafwiseJet1Scale L omega j)).val =
        ⟨(firstTangent j).val.proj, (omega : ℂ) • (firstTangent j).val.snd⟩) ∧
    (∀ x : M, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ frame : O → P, Continuous frame ∧ ∀ y, (frame y).val.proj = y.val) := by
  obtain ⟨e, hb, hr, hs, _, _, hf⟩ := native_first_tangent_homeomorph_coordinates_with_frames L hRank U himm
    T c label branch parametrization hcover htarget hparam
  exact ⟨e, hb, hr, hs, hf⟩

/-- The first-tangent homeomorphism with its actual flowbox coefficient formula and continuous slice derivative. -/
theorem native_first_tangent_homeomorph_coordinates
    {D : RealTangentDistribution (realModel d) M}
    (hRank : HasComplexRankOne D)
    (U : HPS.LeafPartition D ι L (fun _ ↦ 2))
    (himm : ∀ i, ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z))
    {n : ℕ} (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
    (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
    (parametrization : ∀ i (t : T i),
      Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
        (⟨{z | (z, t.val) ∈ (c i).target},
          (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
        (branch i t) ∞)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (htarget : ∀ i p, p ∈ (c i).target → p.2 ∈ T i)
    (hparam : ∀ i (t : T i) (z : (⟨{z | (z, t.val) ∈ (c i).target},
        (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)),
      (c i).symm (z.val, t.val) =
        (U.leaf (label i t)).inclusion ((parametrization i t z).val)) :
    let K := fun x : M ↦ (hRank x).choose
    let E := fun x : M ↦ ↥(K x)
    letI : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    let P := {v : TotalSpace ℂ E // v.snd ≠ 0}
    letI := nativeLeafwiseJet1Topology L U c
    ∃ (firstTangent : NativeLeafwiseJet1 L ≃ₜ P),
    (∀ j, (firstTangent j).val.proj = nativeLeafwiseJet1Base L U j) ∧
    (∀ i (gamma : CurveParamGerm (L i)),
      let j : NativeLeafwiseJet1 L := ⟨i, curveJet1Class (L i) gamma⟩
      let representative := fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z)
      (⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩ :
        TangentBundle (complexModel d) M) =
      ⟨representative 0, mfderiv 𝓘(ℂ) (complexModel d) representative 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩) ∧
    (∀ (omega : ℂˣ) j,
      (firstTangent (nativeLeafwiseJet1Scale L omega j)).val =
        ⟨(firstTangent j).val.proj, (omega : ℂ) • (firstTangent j).val.snd⟩) ∧
    (∀ (k : Fin n) (x : M) (j : NativeLeafwiseJet1 L),
      nativeLeafwiseJet1Base L U j ∈ (c k).source →
      nativeLeafwiseJet1Base L U j ∈ (chartAt (ComplexModel d) x).source →
      (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
        (⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩ :
          TangentBundle (complexModel d) M)).2 =
        (nativeLeafwiseJet1Coeff L U (c k) j).2 •
          deriv (fun z ↦ chartAt (ComplexModel d) x
            ((c k).symm (z, (c k (nativeLeafwiseJet1Base L U j)).2)))
            (c k (nativeLeafwiseJet1Base L U j)).1) ∧
    (∀ (k : Fin n) (ψ : OpenPartialHomeomorph M (ComplexModel d)),
      ψ ∈ IsManifold.maximalAtlas (complexModel d) ∞ M →
      ContinuousOn
        (fun p : ℂ × (Fin (2*d-2) → ℝ) ↦
          deriv (fun z ↦ ψ ((c k).symm (z, p.2))) p.1)
        ((c k).target ∩ (c k).symm ⁻¹' ψ.source)) := by
  obtain ⟨e, hb, hr, hs, hc, hd, _⟩ := native_first_tangent_homeomorph_coordinates_with_frames L hRank U himm
    T c label branch parametrization hcover htarget hparam
  exact ⟨e, hb, hr, hs, hc, hd⟩

/-- The first-tangent homeomorphism, retaining the original interface. Source: Ghys §3 pp.591–592. -/
theorem native_first_tangent_homeomorph
    {D : RealTangentDistribution (realModel d) M}
    (hRank : HasComplexRankOne D)
    (U : HPS.LeafPartition D ι L (fun _ ↦ 2))
    (himm : ∀ i, ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z))
    {n : ℕ} (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
    (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
    (parametrization : ∀ i (t : T i),
      Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
        (⟨{z | (z, t.val) ∈ (c i).target},
          (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
        (branch i t) ∞)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (htarget : ∀ i p, p ∈ (c i).target → p.2 ∈ T i)
    (hparam : ∀ i (t : T i) (z : (⟨{z | (z, t.val) ∈ (c i).target},
        (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)),
      (c i).symm (z.val, t.val) =
        (U.leaf (label i t)).inclusion ((parametrization i t z).val)) :
    let K := fun x : M ↦ (hRank x).choose
    let E := fun x : M ↦ ↥(K x)
    letI : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    let P := {v : TotalSpace ℂ E // v.snd ≠ 0}
    letI := nativeLeafwiseJet1Topology L U c
    ∃ (firstTangent : NativeLeafwiseJet1 L ≃ₜ P),
    (∀ j, (firstTangent j).val.proj = nativeLeafwiseJet1Base L U j) ∧
    (∀ i (gamma : CurveParamGerm (L i)),
      let j : NativeLeafwiseJet1 L := ⟨i, curveJet1Class (L i) gamma⟩
      let representative := fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z)
      (⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩ :
        TangentBundle (complexModel d) M) =
      ⟨representative 0, mfderiv 𝓘(ℂ) (complexModel d) representative 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩) ∧
    (∀ (omega : ℂˣ) j,
      (firstTangent (nativeLeafwiseJet1Scale L omega j)).val =
        ⟨(firstTangent j).val.proj, (omega : ℂ) • (firstTangent j).val.snd⟩) := by
  obtain ⟨e, hb, hr, hs, _⟩ := native_first_tangent_homeomorph_with_frames L hRank U himm
    T c label branch parametrization hcover htarget hparam
  exact ⟨e, hb, hr, hs⟩

end HolomorphicAnosov.Ghys
