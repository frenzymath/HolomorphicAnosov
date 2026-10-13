import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Paper.Ghys.NativeJetTangentCovectorTorsor
import HolomorphicAnosov.Ghys.JetDynamicsTotalMaps
import HolomorphicAnosov.Paper.Ghys.NativeUnstableLineNormComparisonCompatible
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineVectorBundle
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineMetric
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalNormComparison
import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import HolomorphicAnosov.Analysis.ContinuousLineCovectorNorm
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology TopologicalSpace
open scoped ContDiff Manifold Bundle
universe u
set_option maxHeartbeats 800000
set_option autoImplicit false
attribute [local instance] complex_isManifold_real

/-- Any continuous homogeneous invariant jet section on the native carrier is uniquely determined. (Ghys, Lemma 3.3) -/
theorem native_invariant_jet_section_unique_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (τ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (hτtrunc : ∀ j, nativeLeafwiseJetTruncation L (τ j) = j)
    (hτhom : ∀ (omega : ℂˣ) j, τ (nativeLeafwiseJet1Scale L omega j) =
      nativeLeafwiseJet2Reparametrize L (CurveJetReparametrization.scale omega) (τ j))
    (hτcontinuous : @Continuous _ _ (nativeLeafwiseJet1Topology L U G.box)
      (nativeLeafwiseJet2Topology L U G.box) τ)
    (hτinvariant : ∀ i (γ η : CurveParamGerm (L i)),
      τ (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ)) =
        nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) η) →
      ∃ δ θ : CurveParamGerm (L (G.permutation i)),
        δ.1 = γ.1.map (G.leafMap i : L i → L (G.permutation i)) ∧
        θ.1 = η.1.map (G.leafMap i : L i → L (G.permutation i)) ∧
        τ (nativeLeafwiseJet1Inclusion L (G.permutation i)
            (curveJet1Class (L (G.permutation i)) δ)) =
          nativeLeafwiseJet2Inclusion L (G.permutation i)
            (curveJet2Class (L (G.permutation i)) θ)) : τ = G.jetSection := by
  classical
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let := nativeLeafwiseJet1Topology L U G.box
  let := nativeLeafwiseJet2Topology L U G.box
  let hRank := G.rankOne
  let himm := G.holomorphic_inclusion
  obtain ⟨hp, firstTangent, hfirstBase, hfirstRep, hfirstScale,
    alpha, halphaContinuous, halphaShift, halphaZero, halphaNeg,
    halphaAdd, halphaTranslate⟩ :=
    native_jet_tangent_covector_torsor L hRank U himm G.transverse G.box G.label
      G.branch G.parametrization G.box_cover G.transverse_contains G.parametrization_inclusion
  let p : C(NativeLeafwiseJet2 L, NativeLeafwiseJet1 L) :=
    ⟨nativeLeafwiseJetTruncation L, hp⟩
  let Sections := SectionTransport.Section p (nativeLeafwiseJet1Scale L)
    (fun omega ↦ nativeLeafwiseJet2Reparametrize L (.scale omega))
  let s : Sections := ⟨⟨τ,hτcontinuous⟩,hτtrunc,hτhom⟩
  let t : Sections := ⟨⟨G.jetSection,G.section_continuous⟩,
    G.section_truncation,G.section_homogeneous⟩
  let Φ₁ := familyJet1Equiv G.permutation G.leafMap
  let Φ₂ := familyJet2Equiv G.permutation G.leafMap
  have hinvariant (r : Sections)
      (hr : ∀ i (γ η : CurveParamGerm (L i)),
        r.val (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ)) =
          nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) η) →
        ∃ δ θ : CurveParamGerm (L (G.permutation i)),
          δ.1 = γ.1.map (G.leafMap i : L i → L (G.permutation i)) ∧
          θ.1 = η.1.map (G.leafMap i : L i → L (G.permutation i)) ∧
          r.val (nativeLeafwiseJet1Inclusion L (G.permutation i)
              (curveJet1Class (L (G.permutation i)) δ)) =
            nativeLeafwiseJet2Inclusion L (G.permutation i)
              (curveJet2Class (L (G.permutation i)) θ)) :
      ∀ j, r.val (Φ₁ j) = Φ₂ (r.val j) := by
    rintro ⟨i,j⟩
    induction j using Quotient.inductionOn with
    | h γ =>
      obtain ⟨k,w,hw⟩ := Sigma.exists.mp (show ∃ z, r.val ⟨i,curveJet1Class (L i) γ⟩ = z from ⟨_,rfl⟩)
      have hki : k = i := congrArg Sigma.fst ((congrArg (nativeLeafwiseJetTruncation L) hw).symm.trans (r.property.1 _))
      subst k
      obtain ⟨η,rfl⟩ := Quotient.exists_rep w
      change r.val ⟨i,curveJet1Class (L i) γ⟩ = ⟨i,curveJet2Class (L i) η⟩ at hw
      obtain ⟨δ,θ,hδ,hθ,he⟩ := hr i γ η hw
      have hd : δ = curveParamGermPostcompose (G.leafMap i) γ := Subtype.ext hδ
      have ht : θ = curveParamGermPostcompose (G.leafMap i) η := Subtype.ext hθ
      change r.val (familyJet1Equiv G.permutation G.leafMap ⟨i,curveJet1Class (L i) γ⟩) =
        familyJet2Equiv G.permutation G.leafMap (r.val ⟨i,curveJet1Class (L i) γ⟩)
      rw [familyJet1Equiv_class G.permutation G.leafMap i γ,hw,
        familyJet2Equiv_class G.permutation G.leafMap i η]
      simpa only [hd,ht,nativeLeafwiseJet1Inclusion,nativeLeafwiseJet2Inclusion] using he
  have hs := hinvariant s hτinvariant
  have ht := hinvariant t G.section_invariant
  let Δ : NativeLeafwiseJet1 L → ℂ :=
    fun j ↦ alpha s t (firstTangent j).val.proj (firstTangent j).val.snd
  have hshift (j : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet2Reparametrize L ⟨1, Δ j⟩ (s.val j) = t.val j :=
    halphaShift s t j
  have hΦshift (μ : ℂ) (j : NativeLeafwiseJet2 L) :
      Φ₂ (nativeLeafwiseJet2Reparametrize L ⟨1,μ⟩ j) =
        nativeLeafwiseJet2Reparametrize L ⟨1,μ⟩ (Φ₂ j) := by
    rcases j with ⟨i,j⟩
    induction j using Quotient.inductionOn with
    | h γ =>
      change familyJet2Equiv G.permutation G.leafMap
        ⟨i,curveJet2Class (L i) (curveParamGermReparametrize (L i) ⟨1,μ⟩ γ)⟩ = _
      rw [familyJet2Equiv_class]
      change _ = nativeLeafwiseJet2Reparametrize L ⟨1,μ⟩
        (familyJet2Equiv G.permutation G.leafMap ⟨i,curveJet2Class (L i) γ⟩)
      rw [familyJet2Equiv_class,curveParamGermPostcompose_reparametrize]
      rfl
  have hΔforward (j : NativeLeafwiseJet1 L) : Δ (Φ₁ j) = Δ j := by
    have huniq (z w : NativeLeafwiseJet2 L)
        (hzw : nativeLeafwiseJetTruncation L z = nativeLeafwiseJetTruncation L w) :
        ∃! μ : ℂ, nativeLeafwiseJet2Reparametrize L ⟨1,μ⟩ z = w := by
      rcases z with ⟨i,z⟩
      rcases w with ⟨k,w⟩
      have hik : i = k := congrArg Sigma.fst hzw
      subst k
      obtain ⟨μ,hμ,huniq⟩ := nativeLeafFibreShiftUnique i (eq_of_heq (Sigma.mk.inj hzw).2)
      exact ⟨μ,congrArg (Sigma.mk i) hμ,fun a ha ↦ huniq a (eq_of_heq (Sigma.mk.inj ha).2)⟩
    obtain ⟨μ,hμ,hu⟩ := huniq (s.val (Φ₁ j)) (t.val (Φ₁ j))
      ((s.property.1 _).trans (t.property.1 _).symm)
    apply (hu _ (hshift (Φ₁ j))).trans
    symm
    apply hu
    rw [hs,ht,← hΦshift,hshift]
  have hΔiterate (n : ℕ) (j : NativeLeafwiseJet1 L) :
      Δ ((Φ₁.symm : _ → _)^[n] j) = Δ j := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hh := hΔforward (Φ₁.symm ((Φ₁.symm : _ → _)^[n] j))
      rw [Φ₁.apply_symm_apply] at hh
      exact hh.symm.trans ih
  let tangent : NativeLeafwiseJet1 L → TangentBundle (complexModel d) M :=
    fun j ↦ ⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩
  have hforwardTangent (j : NativeLeafwiseJet1 L) :
      tangent (Φ₁ j) = tangentMap (complexModel d) (complexModel d) f (tangent j) := by
    rcases j with ⟨i,j⟩
    induction j using Quotient.inductionOn with
    | h γ =>
      change tangent (familyJet1Equiv G.permutation G.leafMap ⟨i,curveJet1Class (L i) γ⟩) = _
      rw [familyJet1Equiv_class G.permutation G.leafMap i γ]
      let δ := curveParamGermPostcompose (G.leafMap i) γ
      change (⟨(firstTangent ⟨G.permutation i,curveJet1Class (L (G.permutation i)) δ⟩).val.proj,
        (firstTangent ⟨G.permutation i,curveJet1Class (L (G.permutation i)) δ⟩).val.snd.val⟩ :
          TangentBundle (complexModel d) M) = _
      rw [hfirstRep (G.permutation i) δ]
      change _ = tangentMap (complexModel d) (complexModel d) f
        ⟨(firstTangent ⟨i,curveJet1Class (L i) γ⟩).val.proj,
          (firstTangent ⟨i,curveJet1Class (L i) γ⟩).val.snd.val⟩
      rw [hfirstRep i γ]
      have hevent : δ.val.out =ᶠ[𝓝 (0 : ℂ)] (G.leafMap i) ∘ γ.val.out := by
        apply Filter.Germ.coe_eq.mp
        exact (Quotient.out_eq δ.val).trans
          ((congrArg (fun g : Filter.Germ (𝓝 (0 : ℂ)) (L i) ↦
            g.map (G.leafMap i : L i → L (G.permutation i)))
            (Quotient.out_eq γ.val).symm).trans (Filter.Germ.map_coe _ _))
      have hamb : (fun z : ℂ ↦ (U.leaf (G.permutation i)).inclusion (δ.val.out z))
          =ᶠ[𝓝 (0 : ℂ)] (fun z : ℂ ↦ f ((U.leaf i).inclusion (γ.val.out z))) := by
        filter_upwards [hevent] with z hz
        rw [hz]
        exact G.leafMap_inclusion i _
      have hγ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) γ.val.out 0 :=
        mdifferentiableAt_of_mfderiv_injective (curveParamGerm_mfderiv_bijective γ).injective
      have hinc : MDifferentiableAt 𝓘(ℂ) (complexModel d)
          (fun z : ℂ ↦ (U.leaf i).inclusion (γ.val.out z)) 0 :=
        ((himm i).1.mdifferentiable (by simp) _).comp 0 hγ
      have hchain := tangentMap_comp_at
        (I := 𝓘(ℂ)) (I' := complexModel d) (I'' := complexModel d)
        (f := fun z : ℂ ↦ (U.leaf i).inclusion (γ.val.out z)) (g := f)
        (⟨0,(tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1⟩)
        (f.contMDiff.mdifferentiable (by simp) _) hinc
      change _ = tangentMap (complexModel d) (complexModel d) f
        (tangentMap 𝓘(ℂ) (complexModel d)
          (fun z : ℂ ↦ (U.leaf i).inclusion (γ.val.out z))
          ⟨0,(tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1⟩)
      rw [← hchain]
      apply Bundle.TotalSpace.ext hamb.eq_of_nhds
      rw [hamb.mfderiv_eq]
      rfl
  have hbackTangent (j : NativeLeafwiseJet1 L) :
      tangent (Φ₁.symm j) = tangentMap (complexModel d) (complexModel d) f.symm (tangent j) := by
    have hh := hforwardTangent (Φ₁.symm j)
    rw [Φ₁.apply_symm_apply] at hh
    rw [hh]
    rw [← tangentMap_comp_at (tangent (Φ₁.symm j))
      (f.symm.contMDiff.mdifferentiable (by simp) _)
      (f.contMDiff.mdifferentiable (by simp) _)]
    have he : (f.symm : M → M) ∘ (f : M → M) = id := funext f.symm_apply_apply
    rw [he,tangentMap_id]
    rfl
  have hbackTangentIter (n : ℕ) (j : NativeLeafwiseJet1 L) :
      tangent ((Φ₁.symm : _ → _)^[n] j) =
        tangentMap (complexModel d) (complexModel d)
          ((f.symm : M → M)^[n]) (tangent j) := by
    induction n with
    | zero => simp [tangentMap]; rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', hbackTangent, ih]
      simpa only [Function.iterate_succ'] using (tangentMap_comp_at (tangent j)
        (f.symm.contMDiff.mdifferentiable (by simp) _)
        ((f.symm.contMDiff.iterate n).mdifferentiable (by simp) _)).symm
  let originalNorm (v : TangentBundle (complexModel d) M) : ℝ :=
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ‖complexTangentToReal d v.proj v.snd‖
  have horiginalDecay : ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧
      ∀ n j, originalNorm (tangent ((Φ₁.symm : _ → _)^[n] j)) ≤
        C * q ^ n * originalNorm (tangent j) := by
    let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    obtain ⟨C, q, hC, hq, hq1, _, hUdecay⟩ :=
      fixed_block_uniform_anosov_estimates f a
    refine ⟨C, q, hC, hq, hq1, ?_⟩
    intro n j
    have hmem : complexTangentToReal d (tangent j).proj (tangent j).snd ∈
        a.splitting.unstable.toDistribution (tangent j).proj := by
      rw [← (hRank (tangent j).proj).choose_spec.2]
      exact Submodule.mem_map_of_mem (firstTangent j).val.snd.property
    have hh := hUdecay n (tangent j).proj _ hmem
    rw [mfderiv_complex_to_real
      ((f.symm.contMDiff.iterate n).mdifferentiable (by simp) _)] at hh
    rw [hbackTangentIter]
    exact hh
  let S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x) :=
    fun x ↦ (hRank x).choose
  have hS : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
      a.splitting.unstable.toDistribution x := by
    intro x
    exact (hRank x).choose_spec.2
  obtain ⟨Tbundle, hT⟩ := complex_subbundle_of_realification
    a.splitting.unstable S hS
  have hTS : Tbundle.toDistribution = S := by simpa using hT
  have hRankS : ∀ x, Module.finrank ℂ (S x) = 1 := by
    intro x
    exact (hRank x).choose_spec.1
  let : TopologicalSpace (Bundle.TotalSpace ℂ (fun x : M ↦ ↥(S x))) :=
    TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  obtain ⟨fb, hvb⟩ := exists_native_complex_line_vectorBundle Tbundle S hTS hRankS
  let : FiberBundle ℂ (fun x : M ↦ ↥(S x)) := fb
  let : VectorBundle ℂ ℂ (fun x : M ↦ ↥(S x)) := hvb
  obtain ⟨core, hcore⟩ := exists_native_complex_line_metric Tbundle S hTS hRankS
  let : ∀ x, NormedAddCommGroup (S x) := fun x ↦
    (core x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (S x) := fun x ↦
    InnerProductSpace.ofCore (core x).toCore
  obtain ⟨hNative, hhNative, cNative, CNative, hcNative, hcNativeC,
    hNativeCompare⟩ := exists_native_unstable_line_norm_comparison_compatible
    Tbundle S hTS hRankS core hcore
  have hnorm : Continuous (fun z : Bundle.TotalSpace ℂ (fun x : M ↦ ↥(S x)) ↦ ‖z.snd‖) := hcore
  let ν : NativeLeafwiseJet1 L → ℝ := fun j ↦ ‖(firstTangent j).val.snd‖
  have hνcontinuous : Continuous ν :=
    hnorm.comp (continuous_subtype_val.comp firstTangent.continuous)
  have hνpositive : ∀ j, 0 < ν j := fun j ↦
    norm_pos_iff.mpr (firstTangent j).property
  have hνscale : ∀ (omega : ℂˣ) j,
      ν (nativeLeafwiseJet1Scale L omega j) = ‖(omega : ℂ)‖ * ν j := by
    intro omega j
    have he := hfirstScale omega j
    change ‖(firstTangent (nativeLeafwiseJet1Scale L omega j)).val.snd‖ = _
    rw [he]
    exact norm_smul (omega : ℂ) (firstTangent j).val.snd
  let frames : M → Bundle.Trivialization ℂ
      (Bundle.TotalSpace.proj (F := ℂ) (E := fun x ↦ S x)) :=
    fun x ↦ trivializationAt ℂ (fun y ↦ S y) x
  have hframes : ∀ x, (frames x).IsLinear ℂ := fun x ↦ inferInstance
  have hframesCover : ∀ x : M, ∃ i, x ∈ (frames i).baseSet :=
    fun x ↦ ⟨x, FiberBundle.mem_baseSet_trivializationAt ℂ (fun y ↦ S y) x⟩
  let originalContinuous (b : ∀ x : M, S x →ₗ[ℂ] ℂ) :
      ∀ x : M, S x →L[ℂ] ℂ := fun x ↦ (b x).toContinuousLinearMap
  let αLinear (s t : Sections) (x : M) : S x →ₗ[ℂ] ℂ :=
    (alpha s t x).toLinearMap
  let : ∀ x, TopologicalSpace (S x) := fun x ↦
    (core x).toNormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let β (s t : Sections) (x : M) : S x →L[ℂ] ℂ :=
    (αLinear s t x).toContinuousLinearMap
  have hβcontinuous (s t : Sections) :
      Continuous (fun v : Bundle.TotalSpace ℂ (fun x ↦ S x) ↦
        β s t v.proj v.snd) := halphaContinuous s t
  have hβnorm (s t : Sections) : Continuous (fun x ↦ ‖β s t x‖) :=
    continuous_line_covector_norm hnorm frames hframesCover
      (β s t) (hβcontinuous s t)
  have hβbounded (s t : Sections) : BddAbove (range (fun x ↦ ‖β s t x‖)) :=
    (isCompact_range (hβnorm s t)).bddAbove
  have hDecayOfAmbientComparison
      (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
      (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
      (hcompare : ∀ j,
        c * hermitianBoundsNorm h (tangent j).proj (tangent j).snd ≤ ν j ∧
        ν j ≤ C * hermitianBoundsNorm h (tangent j).proj (tangent j).snd) :
      ∃ C q : ℝ, 0 < C ∧ 0 ≤ q ∧ q < 1 ∧
        ∀ n j, ν ((Φ₁.symm : _ → _)^[n] j) ≤ C * q ^ n * ν j := by
    let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    obtain ⟨C₀, q, hC₀, hq, hq1, hdecay⟩ := horiginalDecay
    obtain ⟨c₁, C₁, hc₁, hc₁C₁, hC₁, hcompareOriginal⟩ :=
      OneFormBundle.original_norm_comparison f a h hh
    have hC : 0 < C := hc.trans_le hcC
    have hC₁pos : 0 < C₁ := zero_lt_one.trans_le hC₁
    have hupper (j : NativeLeafwiseJet1 L) :
        ν j ≤ (C / c₁) * originalNorm (tangent j) := by
      have hbound : hermitianBoundsNorm h (tangent j).proj (tangent j).snd ≤
          originalNorm (tangent j) / c₁ := by
        apply (le_div_iff₀ hc₁).mpr
        simpa only [mul_comm, originalNorm, hermitianBoundsNorm] using
          (hcompareOriginal (tangent j).proj (tangent j).snd).1
      calc
        ν j ≤ C * hermitianBoundsNorm h (tangent j).proj (tangent j).snd := (hcompare j).2
        _ ≤ C * (originalNorm (tangent j) / c₁) :=
          mul_le_mul_of_nonneg_left hbound hC.le
        _ = (C / c₁) * originalNorm (tangent j) := by ring
    have hreverse (j : NativeLeafwiseJet1 L) :
        originalNorm (tangent j) ≤ (C₁ / c) * ν j := by
      have hbound : hermitianBoundsNorm h (tangent j).proj (tangent j).snd ≤ ν j / c := by
        apply (le_div_iff₀ hc).mpr
        simpa only [mul_comm] using (hcompare j).1
      calc
        originalNorm (tangent j) ≤ C₁ *
            hermitianBoundsNorm h (tangent j).proj (tangent j).snd :=
          (hcompareOriginal (tangent j).proj (tangent j).snd).2
        _ ≤ C₁ * (ν j / c) := mul_le_mul_of_nonneg_left hbound hC₁pos.le
        _ = (C₁ / c) * ν j := by ring
    refine ⟨((C / c₁) * C₀ * (C₁ / c)), q,
      (mul_pos (mul_pos (div_pos hC hc₁) hC₀) (div_pos hC₁pos hc)), hq.le, hq1, ?_⟩
    intro n j
    calc
      ν ((Φ₁.symm : _ → _)^[n] j) ≤
          (C / c₁) * originalNorm (tangent ((Φ₁.symm : _ → _)^[n] j)) := hupper _
      _ ≤ (C / c₁) * (C₀ * q ^ n * originalNorm (tangent j)) :=
        mul_le_mul_of_nonneg_left (hdecay n j) (div_pos hC hc₁).le
      _ ≤ (C / c₁) * (C₀ * q ^ n * ((C₁ / c) * ν j)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hreverse j) (mul_nonneg hC₀.le (pow_nonneg hq.le n)))
          (div_pos hC hc₁).le
      _ = ((C / c₁) * C₀ * (C₁ / c)) * q ^ n * ν j := by ring
  obtain ⟨Cdec, qdec, hCdec, hqdec, hqdec1, hNormDecay⟩ :=
    hDecayOfAmbientComparison hNative hhNative cNative CNative hcNative hcNativeC
      (fun j ↦ hNativeCompare (firstTangent j).val.proj (firstTangent j).val.snd)
  obtain ⟨K,hK⟩ := hβbounded s t
  have hpoint (j : NativeLeafwiseJet1 L) : ‖Δ j‖ ≤ K * ν j :=
    ((β s t (firstTangent j).val.proj).le_opNorm (firstTangent j).val.snd).trans
      (mul_le_mul_of_nonneg_right (hK ⟨(firstTangent j).val.proj,rfl⟩) (hνpositive j).le)
  funext j
  have hKnonneg : 0 ≤ K := (norm_nonneg (β s t (firstTangent j).val.proj)).trans
    (hK ⟨(firstTangent j).val.proj,rfl⟩)
  have hbound (n : ℕ) : ‖Δ j‖ ≤ K * (Cdec * qdec^n * ν j) := by
    rw [← hΔiterate n j]
    exact (hpoint _).trans (mul_le_mul_of_nonneg_left (hNormDecay n j) hKnonneg)
  have hlimit : Tendsto (fun n : ℕ ↦ K * (Cdec * qdec^n * ν j)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hqdec hqdec1)).mul
        tendsto_const_nhds)) : Tendsto _ atTop (𝓝 (K * (Cdec * 0 * ν j))))
  have hz : Δ j = 0 := norm_eq_zero.mp (le_antisymm
    (le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit hbound) (norm_nonneg _))
  have hself := halphaShift s s j
  have hst := hshift j
  rw [hz] at hst
  have hzero := congrArg (fun b ↦ b (firstTangent j).val.proj (firstTangent j).val.snd)
    (halphaZero s)
  rw [hzero] at hself
  exact hself.symm.trans hst

end HolomorphicAnosov.Ghys
