import HolomorphicAnosov.Ghys.CurveJetScalarReparamCoefficients
import HolomorphicAnosov.Ghys.CurveJetTruncationBase
import HolomorphicAnosov.Ghys.CurveOpenCoordinateFirstNonzero
import HolomorphicAnosov.Ghys.NativeFirstTangentHomeomorph
import HolomorphicAnosov.Ghys.NativeLeafFibreShift
import HolomorphicAnosov.Ghys.NativeLeafwiseJetTruncationContinuous
import HolomorphicAnosov.Paper.Ghys.ComplexCovectorExt
import HolomorphicAnosov.Paper.Ghys.SectionTransport

/-! This file identifies native first jets with the punctured tangent line and describes the covector torsor of homogeneous second-jet sections (Ghys, §3). -/

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

/-- On a holomorphic rank-one native leaf cover, first parametrization jets identify with the punctured tangent line, and continuous homogeneous two-jet sections form its continuous covector torsor. (Ghys, §3; Hatcher, Lemma 1.1) -/
theorem native_jet_tangent_covector_torsor
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
    letI := nativeLeafwiseJet2Topology L U c
    ∃ (hp : Continuous (nativeLeafwiseJetTruncation L)),
    let p : C(NativeLeafwiseJet2 L, NativeLeafwiseJet1 L) :=
      ⟨nativeLeafwiseJetTruncation L, hp⟩
    let S := SectionTransport.Section p (nativeLeafwiseJet1Scale L)
      (fun omega ↦ nativeLeafwiseJet2Reparametrize L (.scale omega))
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
    ∃ (alpha : S → S → ∀ x : M, E x →L[ℂ] ℂ),
      (∀ s t, Continuous (fun v : TotalSpace ℂ E ↦ alpha s t v.proj v.snd)) ∧
      (∀ s t (v : NativeLeafwiseJet1 L),
        nativeLeafwiseJet2Reparametrize L
          ⟨1, alpha s t (firstTangent v).val.proj (firstTangent v).val.snd⟩ (s.val v) =
        t.val v) ∧
      (∀ s, alpha s s = 0) ∧
      (∀ s t, alpha t s = -alpha s t) ∧
      (∀ s t r, alpha s r = alpha s t + alpha t r) ∧
      (∀ (s : S) (beta : ∀ x : M, E x →L[ℂ] ℂ),
        Continuous (fun v : TotalSpace ℂ E ↦ beta v.proj v.snd) →
        ∃! t : S, alpha s t = beta) := by
  have hscalar : ∀ k i z, (U.leaf i).inclusion z ∈ (c k).source →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (nativeLeafFlowboxScalar L U (c k) i) z := by
    intro k i z hz
    let t : T k := ⟨(c k ((U.leaf i).inclusion z)).2,
      htarget k _ ((c k).map_source hz)⟩
    let w : (⟨{w | (w, t.val) ∈ (c k).target},
        (c k).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ) :=
      ⟨(c k ((U.leaf i).inclusion z)).1, (c k).map_source hz⟩
    have hw : (U.leaf (label k t)).inclusion ((parametrization k t w).val) =
        (U.leaf i).inclusion z := by
      rw [← hparam k t w]
      exact (c k).left_inv hz
    have hi : label k t = i := U.disjoint _ _ _ _ hw
    clear_value w t
    cases hi
    have hpoint : (parametrization k t w).val = z := (U.leaf _).injective hw
    have hbranch : z ∈ branch k t := hpoint ▸ (parametrization k t w).property
    have hformula (y : branch k t) :
        nativeLeafFlowboxScalar L U (c k) (label k t) y.val =
          ((parametrization k t).symm y).val := by
      let a := (parametrization k t).symm y
      have he := hparam k t a
      rw [(parametrization k t).apply_symm_apply] at he
      change (c k ((U.leaf (label k t)).inclusion y.val)).1 = a.val
      rw [← he, (c k).right_inv a.property]
    have hs : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
        (fun y : branch k t ↦ nativeLeafFlowboxScalar L U (c k) (label k t) y.val) := by
      have hh := contMDiff_subtype_val.comp (parametrization k t).symm.contMDiff
      exact hh.congr hformula
    exact (contMDiffAt_subtype_iff (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
      (U := branch k t) (f := nativeLeafFlowboxScalar L U (c k) (label k t))).mp
        (hs.contMDiffAt (x := ⟨z, hbranch⟩))
  refine ⟨nativeLeafwiseJetTruncation_continuous L U c hscalar, ?_⟩
  have hnonzero (i : ι) (gamma : CurveParamGerm (L i)) :
      mfderiv 𝓘(ℂ) (complexModel d)
          (fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z)) 0
          ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1) ≠ 0 :=
    curveParamGerm_immersion_tangent_ne_zero
      (I := complexModel d) (U.leaf i).inclusion
      (himm i).1 (himm i).2 gamma
  have hbase_scale (omega : ℂˣ) (j : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Scale L omega j) =
        nativeLeafwiseJet1Base L U j := by
    rcases j with ⟨i, j⟩
    simp only [nativeLeafwiseJet1Base, nativeLeafwiseJet1Scale]
    refine Quotient.inductionOn j ?_
    intro γ
    change (U.leaf i).inclusion
        (curveJet1Base (L i) (curveJet1Scale (L i) omega (curveJet1Class (L i) γ))) = _
    rw [show curveJet1Scale (L i) omega (curveJet1Class (L i) γ) =
      curveJet1Class (L i) (curveParamGermReparametrize (L i) (.scale omega) γ) from rfl]
    change (U.leaf i).inclusion
        (curveJet1Base (L i) (curveJet1Class (L i) (curveParamGermReparametrize (L i) (.scale omega) γ))) =
      (U.leaf i).inclusion (curveJet1Base (L i) (curveJet1Class (L i) γ))
    have hb := (leaf_jet_complex_manifold (L i)).2.1
    rw [hb (curveParamGermReparametrize (L i) (.scale omega) γ) |>.1, hb γ |>.1]
    exact congrArg (U.leaf i).inclusion (base_reparam (L i) (.scale omega) γ.1)
  have hbase_rep (i : ι) (gamma : CurveParamGerm (L i)) :
      nativeLeafwiseJet1Base L U ⟨i, curveJet1Class (L i) gamma⟩ =
        (U.leaf i).inclusion (gamma.val.out 0) := by
    simp only [nativeLeafwiseJet1Base]
    rw [(leaf_jet_complex_manifold (L i)).2.1 gamma |>.1]
    calc
      (U.leaf i).inclusion (curveGermBase (L i) gamma.val) =
          (U.leaf i).inclusion (curveGermBase (L i) ((gamma.val.out : ℂ → L i) : CurveGerm (L i))) :=
        congrArg (U.leaf i).inclusion (congrArg (curveGermBase (L i)) (Quotient.out_eq gamma.val).symm)
      _ = (U.leaf i).inclusion (gamma.val.out 0) :=
        congrArg (U.leaf i).inclusion (base_coe (L i) gamma.val.out)
  have hfirst_scale (omega : ℂˣ) (i : ι) (gamma : CurveParamGerm (L i))
      (c0 : LeafChart (L i)) (hbase : curveGermBase (L i) gamma.1 ∈ c0.1.source) :
      curveGermFirst (L i) c0
          (curveParamGermReparametrize (L i) (.scale omega) gamma) =
        (omega : ℂ) * curveGermFirst (L i) c0 gamma := by
    rw [curve_first_reparam (L i) (.scale omega) gamma c0 hbase]
    have hd : HasDerivAt (fun z : ℂ => (omega : ℂ) * z) (omega : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (omega : ℂ)
    have hderiv : deriv (CurveJetReparametrization.scale omega).apply 0 = (omega : ℂ) := by
      change deriv (fun z : ℂ => (omega : ℂ) * z / (1 + 0 * z)) 0 = _
      simp only [zero_mul, add_zero, div_one]
      exact hd.deriv
    rw [hderiv]
  have hscaled_rep (omega : ℂˣ) (i : ι) (gamma : CurveParamGerm (L i)) :
      nativeLeafwiseJet1Base L U
          ⟨i, curveJet1Scale (L i) omega (curveJet1Class (L i) gamma)⟩ =
        (U.leaf i).inclusion (gamma.val.out 0) := by
    change nativeLeafwiseJet1Base L U
      (nativeLeafwiseJet1Scale L omega ⟨i, curveJet1Class (L i) gamma⟩) = _
    rw [hbase_scale]
    exact hbase_rep i gamma
  have hnonzero_scaled (omega : ℂˣ) (i : ι) (gamma : CurveParamGerm (L i)) :
      mfderiv 𝓘(ℂ) (complexModel d)
          (fun z : ℂ ↦ (U.leaf i).inclusion
            ((curveParamGermReparametrize (L i) (.scale omega) gamma).val.out z)) 0
          ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1) ≠ 0 := by
    exact hnonzero i (curveParamGermReparametrize (L i) (.scale omega) gamma)
  have hscale_one (j : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet1Scale L 1 j = j := by
    rcases j with ⟨i, j⟩
    apply congrArg (fun q : CurveJet1 (L i) => (⟨i, q⟩ : NativeLeafwiseJet1 L))
    exact (curve_jet_reparametrization (L i)).2.2.2.2.2.1 j
  have hscale_comp (o e : ℂˣ) (j : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet1Scale L o (nativeLeafwiseJet1Scale L e j) =
        nativeLeafwiseJet1Scale L (e * o) j := by
    rcases j with ⟨i, j⟩
    apply congrArg (fun q : CurveJet1 (L i) => (⟨i, q⟩ : NativeLeafwiseJet1 L))
    exact (curve_jet_reparametrization (L i)).2.2.2.2.2.2.2.1 o e j
  have htrunc_scale (o : ℂˣ) (q : NativeLeafwiseJet2 L) :
      nativeLeafwiseJetTruncation L
          (nativeLeafwiseJet2Reparametrize L (.scale o) q) =
        nativeLeafwiseJet1Scale L o (nativeLeafwiseJetTruncation L q) := by
    rcases q with ⟨i,q⟩
    apply congrArg (fun j : CurveJet1 (L i) => (⟨i,j⟩ : NativeLeafwiseJet1 L))
    change curveJetTruncation (L i) (curveJet2Reparametrize (L i) (.scale o) q) =
      curveJet1Scale (L i) o (curveJetTruncation (L i) q)
    exact ((curve_jet_reparametrization (L i)).2.2.1 (.scale o) q).2.1
  have hbase2_reparam (p0 : CurveJetReparametrization) (q : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Base L U (nativeLeafwiseJet2Reparametrize L p0 q) =
        nativeLeafwiseJet2Base L U q := by
    rcases q with ⟨i,q⟩
    apply congrArg (U.leaf i).inclusion
    change curveJet2Base (L i) (curveJet2Reparametrize (L i) p0 q) = curveJet2Base (L i) q
    exact ((curve_jet_reparametrization (L i)).2.2.1 p0 q).1
  have htrunc_reparam (p0 : CurveJetReparametrization) (q : NativeLeafwiseJet2 L) :
      nativeLeafwiseJetTruncation L
          (nativeLeafwiseJet2Reparametrize L p0 q) =
        nativeLeafwiseJet1Scale L p0.omega (nativeLeafwiseJetTruncation L q) := by
    rcases q with ⟨i,q⟩
    apply congrArg (fun j : CurveJet1 (L i) => (⟨i,j⟩ : NativeLeafwiseJet1 L))
    change curveJetTruncation (L i) (curveJet2Reparametrize (L i) p0 q) =
      curveJet1Scale (L i) p0.omega (curveJetTruncation (L i) q)
    exact ((curve_jet_reparametrization (L i)).2.2.1 p0 q).2.1
  have htrunc_base (q : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L q) =
        nativeLeafwiseJet2Base L U q := by
    rcases q with ⟨i,q⟩
    change (U.leaf i).inclusion (curveJet1Base (L i) (curveJetTruncation (L i) q)) = _
    rw [curve_jet_truncation_base]
    rfl
  have hnative_inverse (p0 : CurveJetReparametrization) (q : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L p0.inverse
          (nativeLeafwiseJet2Reparametrize L p0 q) = q := by
    rcases q with ⟨i,q⟩
    apply congrArg (fun r : CurveJet2 (L i) => (⟨i,r⟩ : NativeLeafwiseJet2 L))
    exact ((curve_jet_reparametrization (L i)).2.2.2.2.2.2.2.2.1 p0 q).1
  have hnative_inverse' (p0 : CurveJetReparametrization) (q : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L p0
          (nativeLeafwiseJet2Reparametrize L p0.inverse q) = q := by
    rcases q with ⟨i,q⟩
    apply congrArg (fun r : CurveJet2 (L i) => (⟨i,r⟩ : NativeLeafwiseJet2 L))
    exact ((curve_jet_reparametrization (L i)).2.2.2.2.2.2.2.2.1 p0 q).2
  have hparam_inverse_left (p0 : CurveJetReparametrization) :
      p0.inverse.compose p0 = CurveJetReparametrization.scale 1 := by
    cases p0 with
    | mk omega mu =>
      simp [CurveJetReparametrization.compose, CurveJetReparametrization.inverse,
        CurveJetReparametrization.scale, div_eq_mul_inv]
  have hparam_inverse_right (p0 : CurveJetReparametrization) :
      p0.compose p0.inverse = CurveJetReparametrization.scale 1 := by
    cases p0 with
    | mk omega mu =>
      simp [CurveJetReparametrization.compose, CurveJetReparametrization.inverse,
        CurveJetReparametrization.scale, div_eq_mul_inv]
  have hnative_comp (p0 q0 : CurveJetReparametrization) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L p0
          (nativeLeafwiseJet2Reparametrize L q0 j) =
        nativeLeafwiseJet2Reparametrize L (p0.compose q0) j := by
    rcases j with ⟨i,j⟩
    apply congrArg (fun r : CurveJet2 (L i) => (⟨i,r⟩ : NativeLeafwiseJet2 L))
    exact (curve_jet_reparametrization (L i)).2.2.2.2.2.2.1 p0 q0 j
  have hnative_scale_inverse (o : ℂˣ) (j : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet1Scale L o⁻¹ (nativeLeafwiseJet1Scale L o j) = j := by
    rw [hscale_comp o⁻¹ o j]
    simpa using hscale_one j
  have hnative_scale_inverse' (o : ℂˣ) (j : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet1Scale L o (nativeLeafwiseJet1Scale L o⁻¹ j) = j := by
    rw [hscale_comp o o⁻¹ j]
    simpa using hscale_one j
  have hnative_second_inverse (p0 : CurveJetReparametrization) (q : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L p0.inverse
          (nativeLeafwiseJet2Reparametrize L p0 q) = q := hnative_inverse p0 q
  have hnative_second_inverse' (p0 : CurveJetReparametrization) (q : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L p0
          (nativeLeafwiseJet2Reparametrize L p0.inverse q) = q := hnative_inverse' p0 q
  have htrunc_comp (p0 q0 : CurveJetReparametrization) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJetTruncation L
          (nativeLeafwiseJet2Reparametrize L p0
            (nativeLeafwiseJet2Reparametrize L q0 j)) =
        nativeLeafwiseJet1Scale L (q0.omega * p0.omega)
          (nativeLeafwiseJetTruncation L j) := by
    rw [hnative_comp]
    rw [htrunc_reparam]
    rfl
  have hnative_shift_unique (j k : NativeLeafwiseJet2 L)
      (htrunc : nativeLeafwiseJetTruncation L j =
        nativeLeafwiseJetTruncation L k) :
      ∃! mu : ℂ,
        nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j = k := by
    rcases j with ⟨i, j⟩
    rcases k with ⟨i', k⟩
    have hi : i = i' := congrArg Sigma.fst htrunc
    cases hi
    have htrunc'' := (Sigma.mk.inj htrunc).2
    have htrunc' : curveJetTruncation (L i) j = curveJetTruncation (L i) k := by
      exact eq_of_heq htrunc''
    simpa [nativeLeafwiseJet2Reparametrize] using
      (nativeLeafFibreShiftUnique i htrunc')
  have hnative_shift_choose (j k : NativeLeafwiseJet2 L)
      (htrunc : nativeLeafwiseJetTruncation L j =
        nativeLeafwiseJetTruncation L k) :
      nativeLeafwiseJet2Reparametrize L
          ⟨1, Classical.choose (hnative_shift_unique j k htrunc)⟩ j = k := by
    exact (Classical.choose_spec (hnative_shift_unique j k htrunc)).1
  have hnative_shift_choose_unique (j k : NativeLeafwiseJet2 L)
      (htrunc : nativeLeafwiseJetTruncation L j =
        nativeLeafwiseJetTruncation L k) (mu : ℂ)
      (hmu : nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j = k) :
      Classical.choose (hnative_shift_unique j k htrunc) = mu := by
    exact ((Classical.choose_spec (hnative_shift_unique j k htrunc)).2 mu hmu).symm
  have hshift_comp (mu nu : ℂ) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩
          (nativeLeafwiseJet2Reparametrize L ⟨1, nu⟩ j) =
        nativeLeafwiseJet2Reparametrize L ⟨1, mu + nu⟩ j := by
    rw [hnative_comp]
    congr 1
    cases mu
    cases nu
    simp [CurveJetReparametrization.compose]
  have hshift_zero (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L ⟨1, 0⟩ j = j := by
    rcases j with ⟨i, j⟩
    apply congrArg (fun q : CurveJet2 (L i) => (⟨i, q⟩ : NativeLeafwiseJet2 L))
    simpa [CurveJetReparametrization.scale] using
      (curve_jet_reparametrization (L i)).2.2.2.2.1 j
  have hshift_neg (mu : ℂ) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L ⟨1, -mu⟩
          (nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j) = j := by
    rw [hshift_comp]
    simpa using hshift_zero j
  have hshift_trunc (mu : ℂ) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJetTruncation L
          (nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j) =
        nativeLeafwiseJetTruncation L j := by
    rw [htrunc_reparam]
    simpa using hscale_one (nativeLeafwiseJetTruncation L j)
  have hshift_base (mu : ℂ) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Base L U
          (nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j) =
        nativeLeafwiseJet2Base L U j := by
    exact hbase2_reparam ⟨1, mu⟩ j
  have hshift_trunc_base (mu : ℂ) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet1Base L U
          (nativeLeafwiseJetTruncation L
            (nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j)) =
        nativeLeafwiseJet2Base L U j := by
    rw [htrunc_base, hshift_base]
  have hscale_shift (o : ℂˣ) (mu : ℂ) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L (CurveJetReparametrization.scale o)
          (nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j) =
        nativeLeafwiseJet2Reparametrize L ⟨o, mu * (o : ℂ)⟩ j := by
    rw [hnative_comp]
    congr 1
    simp [CurveJetReparametrization.scale, CurveJetReparametrization.compose]
  have hshift_scale (o : ℂˣ) (mu : ℂ) (j : NativeLeafwiseJet2 L) :
      nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩
          (nativeLeafwiseJet2Reparametrize L (CurveJetReparametrization.scale o) j) =
        nativeLeafwiseJet2Reparametrize L ⟨o, mu⟩ j := by
    rw [hnative_comp]
    congr 1
    simp [CurveJetReparametrization.scale, CurveJetReparametrization.compose]
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  have hflowbox_cont := nativeLeafwiseJet_flowbox_continuity L U c
  let p0 : C(NativeLeafwiseJet2 L, NativeLeafwiseJet1 L) :=
    ⟨nativeLeafwiseJetTruncation L, nativeLeafwiseJetTruncation_continuous L U c hscalar⟩
  let S0 := SectionTransport.Section p0 (nativeLeafwiseJet1Scale L)
    (fun o ↦ nativeLeafwiseJet2Reparametrize L (.scale o))
  have hsection_base (s : S0) (v : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet2Base L U (s.val v) = nativeLeafwiseJet1Base L U v := by
    rw [← htrunc_base]
    exact congrArg (nativeLeafwiseJet1Base L U) (s.property.1 v)
  have hsection_coeff_cont (s : S0) (k : Fin n) :
      ContinuousOn (fun v ↦ nativeLeafwiseJet2Coeff L U (c k) (s.val v))
        {v | nativeLeafwiseJet1Base L U v ∈ (c k).source} := by
    apply (hflowbox_cont.2.1 k).2.comp s.val.continuous.continuousOn
    intro v hv
    change nativeLeafwiseJet2Base L U (s.val v) ∈ (c k).source
    rwa [hsection_base]
  have hcoeff_nonzero (k : Fin n) (i : ι) (gamma : CurveParamGerm (L i))
      (hz : (U.leaf i).inclusion (curveGermBase (L i) gamma.1) ∈ (c k).source) :
      germFirst (gamma.1.map (nativeLeafFlowboxScalar L U (c k) i)) ≠ 0 := by
    let t : T k := ⟨(c k ((U.leaf i).inclusion (curveGermBase (L i) gamma.1))).2,
      htarget k _ ((c k).map_source hz)⟩
    let w : (⟨{w | (w, t.val) ∈ (c k).target},
        (c k).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ) :=
      ⟨(c k ((U.leaf i).inclusion (curveGermBase (L i) gamma.1))).1,
        (c k).map_source hz⟩
    have hw : (U.leaf (label k t)).inclusion ((parametrization k t w).val) =
        (U.leaf i).inclusion (curveGermBase (L i) gamma.1) := by
      rw [← hparam k t w]
      exact (c k).left_inv hz
    have hi : label k t = i := U.disjoint _ _ _ _ hw
    clear_value w t
    cases hi
    have hpoint : (parametrization k t w).val =
        curveGermBase (L (label k t)) gamma.1 :=
      (U.leaf _).injective hw
    have hbranch : curveGermBase (L (label k t)) gamma.1 ∈ branch k t :=
      hpoint ▸ (parametrization k t w).property
    have hphi : ∀ y : branch k t,
        nativeLeafFlowboxScalar L U (c k) (label k t) y.val =
          ((parametrization k t).symm y).val := by
      intro y
      let a := (parametrization k t).symm y
      have he := hparam k t a
      rw [(parametrization k t).apply_symm_apply] at he
      change (c k ((U.leaf (label k t)).inclusion y.val)).1 = a.val
      rw [← he, (c k).right_inv a.property]
    exact curveParamGerm_openCoordinate_first_ne_zero (L := L (label k t))
      (branch k t) _ (parametrization k t).symm
      (nativeLeafFlowboxScalar L U (c k) (label k t)) hphi gamma hbranch
  have hcoeff_nonzero_jet (k : Fin n) (j : NativeLeafwiseJet2 L)
      (hj : nativeLeafwiseJet2Base L U j ∈ (c k).source) :
      (nativeLeafwiseJet2Coeff L U (c k) j).1.2 ≠ 0 := by
    exact hcoeff_nonzero k j.1 j.2.out hj
  have hsame (s t : S0) (v : NativeLeafwiseJet1 L) :
      nativeLeafwiseJetTruncation L (s.val v) =
        nativeLeafwiseJetTruncation L (t.val v) :=
    (s.property.1 v).trans (t.property.1 v).symm
  let delta (s t : S0) (v : NativeLeafwiseJet1 L) : ℂ :=
    Classical.choose (hnative_shift_unique (s.val v) (t.val v) (hsame s t v))
  have hdelta (s t : S0) (v : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet2Reparametrize L ⟨1, delta s t v⟩ (s.val v) = t.val v :=
    hnative_shift_choose (s.val v) (t.val v) (hsame s t v)
  have hcoeff_reparam (k : Fin n) (p : CurveJetReparametrization)
      (j : NativeLeafwiseJet2 L)
      (hj : nativeLeafwiseJet2Base L U j ∈ (c k).source) :
      (nativeLeafwiseJet2Coeff L U (c k)
        (nativeLeafwiseJet2Reparametrize L p j)).2 =
      (p.omega : ℂ) ^ 2 * (nativeLeafwiseJet2Coeff L U (c k) j).2 -
        (p.omega : ℂ) * p.mu * (nativeLeafwiseJet2Coeff L U (c k) j).1.2 := by
    exact (curveJet2_scalar_reparam_coefficients (L j.1) p j.2
      (nativeLeafFlowboxScalar L U (c k) j.1) (hscalar k j.1 _ hj)).2
  have hcoeff_shift (k : Fin n) (mu : ℂ) (j : NativeLeafwiseJet2 L)
      (hj : nativeLeafwiseJet2Base L U j ∈ (c k).source) :
      nativeLeafwiseJet2Coeff L U (c k)
          (nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j) =
        ((nativeLeafwiseJet2Coeff L U (c k) j).1,
          (nativeLeafwiseJet2Coeff L U (c k) j).2 -
            mu * (nativeLeafwiseJet2Coeff L U (c k) j).1.2) := by
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (c k) (hshift_base mu j)
      · have he : (nativeLeafwiseJet2Coeff L U (c k)
            (nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ j)).1.2 =
              (1 : ℂ) * (nativeLeafwiseJet2Coeff L U (c k) j).1.2 :=
          (curveJet2_scalar_reparam_coefficients (L j.1) ⟨1, mu⟩ j.2
            (nativeLeafFlowboxScalar L U (c k) j.1) (hscalar k j.1 _ hj)).1
        simpa only [one_mul] using he
    · simpa using hcoeff_reparam k ⟨1, mu⟩ j hj
  have hshifted_continuous (s : S0) (F : NativeLeafwiseJet1 L → ℂ)
      (hF : Continuous F) : Continuous (fun v ↦
        nativeLeafwiseJet2Reparametrize L ⟨1, F v⟩ (s.val v)) := by
    apply continuous_generateFrom_iff.mpr
    rintro O ⟨k, W, hW, rfl⟩
    have hc := (hsection_coeff_cont s k).fst.prodMk
      ((hsection_coeff_cont s k).snd.sub
        (hF.continuousOn.mul (hsection_coeff_cont s k).fst.snd))
    have hopen := hc.isOpen_inter_preimage (hflowbox_cont.1 k).1 hW
    convert hopen using 1
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [hshift_base, hsection_base]
    apply and_congr_right
    intro hv
    rw [hcoeff_shift k (F v) (s.val v) (by rwa [hsection_base])]
    rfl
  have hdelta_coeff (s t : S0) (k : Fin n) (v : NativeLeafwiseJet1 L)
      (hv : nativeLeafwiseJet1Base L U v ∈ (c k).source) :
      (nativeLeafwiseJet2Coeff L U (c k) (t.val v)).2 =
        (nativeLeafwiseJet2Coeff L U (c k) (s.val v)).2 -
          delta s t v * (nativeLeafwiseJet2Coeff L U (c k) (s.val v)).1.2 := by
    have hs : nativeLeafwiseJet2Base L U (s.val v) ∈ (c k).source := by
      rwa [hsection_base]
    rw [← hdelta s t v]
    simpa using hcoeff_reparam k ⟨1, delta s t v⟩ (s.val v) hs
  have hdelta_formula (s t : S0) (k : Fin n) (v : NativeLeafwiseJet1 L)
      (hv : nativeLeafwiseJet1Base L U v ∈ (c k).source)
      (ha : (nativeLeafwiseJet2Coeff L U (c k) (s.val v)).1.2 ≠ 0) :
      delta s t v =
        ((nativeLeafwiseJet2Coeff L U (c k) (s.val v)).2 -
          (nativeLeafwiseJet2Coeff L U (c k) (t.val v)).2) /
          (nativeLeafwiseJet2Coeff L U (c k) (s.val v)).1.2 := by
    apply (eq_div_iff ha).mpr
    linear_combination hdelta_coeff s t k v hv
  have hdelta_continuous (s t : S0)
      (ha : ∀ (k : Fin n) (v : NativeLeafwiseJet1 L),
        nativeLeafwiseJet1Base L U v ∈ (c k).source →
          (nativeLeafwiseJet2Coeff L U (c k) (s.val v)).1.2 ≠ 0) :
      Continuous (delta s t) := by
    rw [continuous_iff_continuousAt]
    intro v
    obtain ⟨k, hv⟩ := hcover (nativeLeafwiseJet1Base L U v)
    have hn := (hflowbox_cont.1 k).1.mem_nhds hv
    have hs := (hsection_coeff_cont s k).continuousAt hn
    have ht := (hsection_coeff_cont t k).continuousAt hn
    have hc := (hs.snd.sub ht.snd).div hs.fst.snd (ha k v hv)
    apply hc.congr
    filter_upwards [hn] with w hw
    exact (hdelta_formula s t k w hw (ha k w hw)).symm
  have hdelta_continuous_actual (s t : S0) : Continuous (delta s t) := by
    apply hdelta_continuous s t
    intro k v hv
    apply hcoeff_nonzero_jet k (s.val v)
    rwa [hsection_base]
  have hdelta_unique (s t : S0) (v : NativeLeafwiseJet1 L) (mu : ℂ)
      (hmu : nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ (s.val v) = t.val v) :
      delta s t v = mu :=
    hnative_shift_choose_unique (s.val v) (t.val v) (hsame s t v) mu hmu
  have hdelta_zero (s : S0) (v : NativeLeafwiseJet1 L) : delta s s v = 0 :=
    hdelta_unique s s v 0 (hshift_zero (s.val v))
  have hdelta_neg (s t : S0) (v : NativeLeafwiseJet1 L) :
      delta t s v = -delta s t v := by
    apply hdelta_unique
    rw [← hdelta s t v]
    exact hshift_neg (delta s t v) (s.val v)
  have hdelta_add (s t r : S0) (v : NativeLeafwiseJet1 L) :
      delta s r v = delta s t v + delta t r v := by
    apply hdelta_unique
    rw [add_comm, ← hshift_comp, hdelta, hdelta]
  have hdelta_scale (s t : S0) (o : ℂˣ) (v : NativeLeafwiseJet1 L) :
      delta s t (nativeLeafwiseJet1Scale L o v) = (o : ℂ) * delta s t v := by
    apply hdelta_unique
    rw [s.property.2 o v, t.property.2 o v, hshift_scale]
    rw [mul_comm, ← hscale_shift, hdelta]
  have hdelta_injective (s : S0) : Function.Injective (delta s) := by
    intro t r h
    apply Subtype.ext
    apply ContinuousMap.ext
    intro v
    have hv := congrFun h v
    exact (hdelta s t v).symm.trans ((congrArg
      (fun mu ↦ nativeLeafwiseJet2Reparametrize L ⟨1, mu⟩ (s.val v)) hv).trans
        (hdelta s r v))
  have hdelta_eq_zero (s t : S0) : delta s t = 0 ↔ s = t := by
    constructor
    · intro h
      apply (hdelta_injective s)
      funext v
      exact (hdelta_zero s v).trans (congrFun h v).symm
    · rintro rfl
      funext v
      exact hdelta_zero s v
  have hdelta_orbit_covector (s t : S0) (v : NativeLeafwiseJet1 L) :
      ∃! A : ℂ →L[ℂ] ℂ, ∀ o : ℂˣ,
        A (o : ℂ) = delta s t (nativeLeafwiseJet1Scale L o v) := by
    apply homogeneous_complex_covector_extension
    intro a b
    rw [mul_comm a b, ← hscale_comp, hdelta_scale]
  have hdelta_reconstruct (s : S0) (F : NativeLeafwiseJet1 L → ℂ)
      (hF : ∀ (o : ℂˣ) v,
        F (nativeLeafwiseJet1Scale L o v) = (o : ℂ) * F v)
      (hcont : Continuous F) :
      ∃! t : S0, delta s t = F := by
    let t0 : C(NativeLeafwiseJet1 L, NativeLeafwiseJet2 L) :=
      ⟨fun v ↦ nativeLeafwiseJet2Reparametrize L ⟨1, F v⟩ (s.val v),
        hshifted_continuous s F hcont⟩
    have ht0 : t0 ∈ SectionTransport.sections p0 (nativeLeafwiseJet1Scale L)
        (fun o ↦ nativeLeafwiseJet2Reparametrize L (.scale o)) := by
      constructor
      · intro v
        change nativeLeafwiseJetTruncation L
          (nativeLeafwiseJet2Reparametrize L ⟨1, F v⟩ (s.val v)) = v
        rw [hshift_trunc]
        exact s.property.1 v
      · intro o v
        change nativeLeafwiseJet2Reparametrize L
          ⟨1, F (nativeLeafwiseJet1Scale L o v)⟩
          (s.val (nativeLeafwiseJet1Scale L o v)) =
          nativeLeafwiseJet2Reparametrize L (.scale o)
            (nativeLeafwiseJet2Reparametrize L ⟨1, F v⟩ (s.val v))
        rw [hF, s.property.2 o v, hshift_scale, hscale_shift, mul_comm]
    let t : S0 := ⟨t0, ht0⟩
    have ht : delta s t = F := by
      funext v
      exact hdelta_unique s t v (F v) rfl
    refine ⟨t, ht, ?_⟩
    intro r hr
    exact hdelta_injective s (hr.trans ht.symm)
  have hfirst := native_first_tangent_homeomorph_with_frames L hRank U himm T c label branch
      parametrization hcover htarget hparam
  classical
  let K := fun x : M ↦ (hRank x).choose
  let E := fun x : M ↦ ↥(K x)
  let : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
    (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let P := {v : TotalSpace ℂ E // v.snd ≠ 0}
  obtain ⟨e, heBase, heRep, heScale, hlocalFrame⟩ := hfirst
  let F (s t : S0) (v : P) : ℂ := delta s t (e.symm v)
  let scale (o : ℂˣ) (v : P) : P :=
    ⟨⟨v.val.proj, (o : ℂ) • v.val.snd⟩, smul_ne_zero o.ne_zero v.property⟩
  have heScaleInv (o : ℂˣ) (v : P) :
      e.symm (scale o v) = nativeLeafwiseJet1Scale L o (e.symm v) := by
    apply e.injective
    apply Subtype.ext
    rw [e.apply_symm_apply, heScale, e.apply_symm_apply]
  have hFhom (s t : S0) (o : ℂˣ) (v : P) :
      F s t (scale o v) = (o : ℂ) * F s t v := by
    dsimp only [F]
    rw [heScaleInv, hdelta_scale]
  have hFcont (s t : S0) : Continuous (F s t) :=
    (hdelta_continuous_actual s t).comp e.symm.continuous
  have hfibre (s t : S0) (x : M) :
      ∃ A : E x →L[ℂ] ℂ, ∀ (v : E x) (hv : v ≠ 0),
        A v = F s t ⟨⟨x, v⟩, hv⟩ := by
    let A : E x ≃ₗ[ℂ] ℂ :=
      (Module.nonempty_linearEquiv_of_finrank_eq_one (hRank x).choose_spec.1).some.symm
    let Ac : E x ≃L[ℂ] ℂ := A.toContinuousLinearEquiv
    let V (a : ℂˣ) : P :=
      ⟨⟨x, A.symm (a : ℂ)⟩, A.symm.map_ne_zero_iff.mpr a.ne_zero⟩
    have hV (a b : ℂˣ) : V (a * b) = scale a (V b) := by
      apply Subtype.ext
      change (⟨x, A.symm ((a : ℂ) * (b : ℂ))⟩ : TotalSpace ℂ E) =
        ⟨x, (a : ℂ) • A.symm (b : ℂ)⟩
      congr 1
      exact A.symm.map_smul (a : ℂ) (b : ℂ)
    obtain ⟨B, hB, _⟩ := homogeneous_complex_covector_extension
      (fun a ↦ F s t (V a)) (fun a b ↦ by rw [hV]; exact hFhom s t a (V b))
    refine ⟨B.comp Ac.toContinuousLinearMap, ?_⟩
    intro v hv
    let a : ℂˣ := Units.mk0 (A v) (A.map_ne_zero_iff.mpr hv)
    have ha : (a : ℂ) = A v := rfl
    have hVa : V a = (⟨⟨x, v⟩, hv⟩ : P) := by
      apply Subtype.ext
      change (⟨x, A.symm (A v)⟩ : TotalSpace ℂ E) = ⟨x, v⟩
      rw [A.symm_apply_apply]
    change B (A v) = _
    rw [← ha, hB a, hVa]
  choose alpha halpha using hfibre
  have halphaF (s t : S0) (v : P) : alpha s t v.val.proj v.val.snd = F s t v :=
    halpha s t v.val.proj v.val.snd v.property
  have halphaDelta (s t : S0) (v : NativeLeafwiseJet1 L) :
      alpha s t (e v).val.proj (e v).val.snd = delta s t v := by
    rw [halphaF]
    exact congrArg (delta s t) (e.symm_apply_apply v)
  have halphaCont (s t : S0) :
      Continuous (fun v : TotalSpace ℂ E ↦ alpha s t v.proj v.snd) := by
    let inc : TotalSpace ℂ E → TangentBundle (complexModel d) M :=
      fun v ↦ ⟨v.proj, v.snd.val⟩
    have hinc : Continuous inc := continuous_induced_dom
    have hproj : Continuous (fun v : TotalSpace ℂ E ↦ v.proj) :=
      (FiberBundle.continuous_proj (ComplexModel d) (TangentSpace (complexModel d))).comp hinc
    rw [continuous_iff_continuousAt]
    intro v0
    obtain ⟨O, hO, hx, fr, hfr, hfrbase⟩ := hlocalFrame v0.proj
    let et := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) v0.proj
    let Q : Set (TotalSpace ℂ E) :=
      {v | v.proj ∈ O ∩ et.baseSet}
    have hQ : IsOpen Q := (hO.inter et.open_baseSet).preimage hproj
    have hv0 : v0 ∈ Q := ⟨hx, FiberBundle.mem_baseSet_trivializationAt _ _ _⟩
    have hOn : ContinuousOn (fun v : TotalSpace ℂ E ↦ alpha s t v.proj v.snd) Q := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      let b (v : Q) : O := ⟨v.val.proj, v.property.1⟩
      have hb : Continuous b := (hproj.comp continuous_subtype_val).subtype_mk _
      have hf : Continuous (fr ∘ b) := hfr.comp hb
      have hfa : Continuous (fun z : Q ↦ inc (fr (b z)).val) :=
        hinc.comp (continuous_subtype_val.comp hf)
      have hfc : Continuous (fun z : Q ↦ et (inc (fr (b z)).val)) :=
        et.continuousOn.comp_continuous hfa (fun z ↦ et.mem_source.mpr (by
          change (fr (b z)).val.proj ∈ et.baseSet
          rw [hfrbase]
          exact z.property.2))
      have hvc : Continuous (fun z : Q ↦ et (inc z.val)) :=
        et.continuousOn.comp_continuous (hinc.comp continuous_subtype_val)
          (fun z ↦ et.mem_source.mpr z.property.2)
      have hFf : Continuous (fun z : Q ↦ F s t (fr (b z))) := (hFcont s t).comp hf
      have hcoordNe (z : Q) : (et (inc (fr (b z)).val)).2 ≠ 0 := by
        intro hz
        apply (fr (b z)).property
        apply Subtype.ext
        have hbase : (fr (b z)).val.proj ∈ et.baseSet := by
          rw [hfrbase]
          exact z.property.2
        apply (et.linearEquivAt ℂ _ hbase).injective
        exact hz.trans ((et.linearEquivAt ℂ _ hbase).map_zero).symm
      rw [continuous_iff_continuousAt]
      intro z
      obtain ⟨l, hl⟩ : ∃ l : Fin d, (et (inc (fr (b z)).val)).2 l ≠ 0 := by
        by_contra! h
        apply hcoordNe z
        funext l
        exact h l
      have hden := (continuous_apply l).comp hfc.snd
      have hnum := (continuous_apply l).comp hvc.snd
      apply ((hnum.continuousAt.div hden.continuousAt hl).mul hFf.continuousAt).congr
      filter_upwards [hden.continuousAt.eventually_ne hl] with w hw
      change (et (inc w.val)).2 l / (et (inc (fr (b w)).val)).2 l *
        F s t (fr (b w)) = alpha s t w.val.proj w.val.snd
      change (et (inc (fr (b w)).val)).2 l ≠ 0 at hw
      have hfb := hfrbase (b w)
      have hval := halphaF s t (fr (b w))
      generalize hq : fr (b w) = q at hfb hval hw ⊢
      rcases q with ⟨⟨y, v⟩, hv⟩
      change y = w.val.proj at hfb
      subst y
      obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
        (hRank w.val.proj).choose_spec.1 hv w.val.snd
      have hcoeff : (et (inc w.val)).2 l = a * (et (inc ⟨w.val.proj,v⟩)).2 l := by
        have hlin := congrArg (fun v : TangentSpace (complexModel d) w.val.proj ↦
          et.linearEquivAt ℂ w.val.proj w.property.2 v) (congrArg Subtype.val ha)
        change et.linearEquivAt ℂ w.val.proj w.property.2 (a • v.val) =
          et.linearEquivAt ℂ w.val.proj w.property.2 w.val.snd.val at hlin
        rw [map_smul] at hlin
        exact congrArg (fun z : ComplexModel d ↦ z l) hlin.symm
      rw [hcoeff, mul_div_cancel_right₀ _ hw]
      change a * F s t ⟨⟨w.val.proj,v⟩,hv⟩ = alpha s t w.val.proj w.val.snd
      rw [← hval, ← ha, map_smul, smul_eq_mul]
    exact hOn.continuousAt (hQ.mem_nhds hv0)
  refine ⟨e, heBase, heRep, heScale, alpha, halphaCont, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t v
    rw [halphaDelta]
    exact hdelta s t v
  · intro s
    funext x
    apply ContinuousLinearMap.ext
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · rw [halpha s s x v hv]
      exact hdelta_zero s (e.symm ⟨⟨x,v⟩,hv⟩)
  · intro s t
    funext x
    apply ContinuousLinearMap.ext
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · change alpha t s x v = -alpha s t x v
      rw [halpha t s x v hv, halpha s t x v hv]
      exact hdelta_neg s t (e.symm ⟨⟨x,v⟩,hv⟩)
  · intro s t r
    funext x
    apply ContinuousLinearMap.ext
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · change alpha s r x v = alpha s t x v + alpha t r x v
      rw [halpha s r x v hv, halpha s t x v hv, halpha t r x v hv]
      exact hdelta_add s t r (e.symm ⟨⟨x,v⟩,hv⟩)
  · intro s beta hbeta
    let Fb (v : NativeLeafwiseJet1 L) : ℂ := beta (e v).val.proj (e v).val.snd
    have hFb : Continuous Fb := hbeta.comp (continuous_subtype_val.comp e.continuous)
    have hFbhom (o : ℂˣ) (v : NativeLeafwiseJet1 L) :
        Fb (nativeLeafwiseJet1Scale L o v) = (o : ℂ) * Fb v := by
      exact (congrArg (fun z : TotalSpace ℂ E ↦ beta z.proj z.snd)
        (heScale o v)).trans ((beta _).map_smul (o : ℂ) _)
    obtain ⟨t, ht, huniq⟩ := hdelta_reconstruct s Fb hFbhom hFb
    have hat : alpha s t = beta := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · rw [halpha s t x v hv]
        change delta s t (e.symm ⟨⟨x,v⟩,hv⟩) = beta x v
        rw [ht]
        exact congrArg (fun q : P ↦ beta q.val.proj q.val.snd)
          (e.apply_symm_apply ⟨⟨x,v⟩,hv⟩)
    refine ⟨t, hat, ?_⟩
    intro r hr
    apply huniq
    funext v
    rw [← halphaDelta, hr]

end HolomorphicAnosov.Ghys
