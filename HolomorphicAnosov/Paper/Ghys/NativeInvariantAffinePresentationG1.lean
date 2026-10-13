import HolomorphicAnosov.Paper.Ghys.NativeInvariantJetSectionUniquenessG1
import HolomorphicAnosov.Paper.Ghys.NativeAffineHolonomyCoordinatesG1
import HolomorphicAnosov.Paper.Ghys.NativeAffinePresentationAtlasesG1
import HolomorphicAnosov.Paper.Ghys.NativeAffinePresentationActionG1
import HolomorphicAnosov.Paper.Ghys.IntrinsicPresentationHolonomyHolomorphic
import HolomorphicAnosov.Topology.RealCurveContinuityTestG1
import HolomorphicAnosov.Analysis.Complex.NormalizedUnivalentCompactness
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! This file transports invariant affine leaf structures to a supplied intrinsic presentation and
relates holonomy-ratio continuity to continuity of the homogeneous jet section. (Ghys, Prop.
3.1, p. 590; Lemma 3.3, pp. 592–593) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- The affine-ratio condition gives holomorphic disk charts along each one-box stable path with
continuous connection coefficients and the product-box ambient evaluation formula. -/
theorem native_affine_ratio_path_charts_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (Bnative : ∀ i, ComplexAffineStructure (L i))
    (σ : letI : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
      letI : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
      ∀ i, HomogeneousCurveJetSection (L i) (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i))
    (hflat : ∀ i (c : LeafChart (L i)), c.val ∈ (Bnative i).maximalAtlas (L i) →
      ∀ j, curveJet1Base (L i) j ∈ c.val.source → (curveJet2Coeff (L i) c ((σ i).val j)).2 = 0)
    (hcompact : IsCompact {g : C(Complex.UnitDisc,ℂ) | IsNormalizedUnivalent g}) :
    letI := P.realCharts
    ∀ (B : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      B.ContinuousAlongStableHolonomy P.foliations P.complexLeaves →
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ∃ (i : ι) (E : Diffeomorph 𝓘(ℂ) (complexModel 1) (L i)
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
          (∀ z, (E z).val = (U.leaf i).inclusion z) ∧
          ∀ c ∈ (B.structureAt q).maximalAtlas _,
            E.toHomeomorph.toOpenPartialHomeomorph.trans c ∈ (Bnative i).maximalAtlas _) →
      ∀ (k : P.foliations.boxIndex)
        (p : C(unitInterval,FoliationCoordinateDisk (2*d-2))) (w₀ : FoliationCoordinateDisk 2),
      ∃ (δ : OpenPartialHomeomorph (FoliationCoordinateDisk 2) ℂ)
        (label : unitInterval → ι) (c : ∀ r, LeafChart (L (label r))) (Q : unitInterval → ℂ → ℂ),
        w₀ ∈ δ.source ∧ δ w₀ = 0 ∧ Metric.ball (0 : ℂ) 1 ⊆ δ.target ∧
        (∀ r, Metric.ball (0 : ℂ) 1 ⊆ (c r).val.target) ∧
        (∀ r z, z ∈ Metric.ball (0 : ℂ) 1 →
          (U.leaf (label r)).inclusion ((c r).val.symm z) =
            ((P.foliations.box k).chart (p r,δ.symm z)).val) ∧
        (∀ r j, curveJet1Base (L (label r)) j ∈ (c r).val.source →
          (curveJet2Coeff (L (label r)) (c r) ((σ (label r)).val j)).2 =
            Q r (curveJet1Coeff (L (label r)) (c r) j).1 *
              (curveJet1Coeff (L (label r)) (c r) j).2 ^ 2) ∧
        Continuous (fun q : Complex.UnitDisc × unitInterval ↦ Q q.2 q.1.val) := by
  classical
  let := P.realCharts
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  intro B hB hident k p w₀
  let F := P.foliations
  obtain ⟨γ,hγ,e,W,hW,hxW,hWfull,hesource,hecont,heformula⟩ :=
    one_box_stable_curve_continuous_prefixes_g1 F k w₀ p
  let q (r : unitInterval) := Quotient.mk F.unstablePartition (γ r).val
  let (r : unitInterval) := F.unstableTopology (q r)
  let (r : unitInterval) := P.complexLeaves.charts (q r)
  choose label E hE hEmax using fun r : unitInterval ↦ hident (q r)
  obtain ⟨H⟩ := local_holonomy_continuation_exists_g9 F γ
  obtain ⟨h,hgerm,V,hV,hVconn,hxV,hVsource,d,hd,hVd,hratio⟩ := hB _ _ _ γ H
  let x₀ := (E 0).symm (F.uPoint (γ 0).val)
  let V₀ := (E 0) ⁻¹' (V ∩ W)
  have hV₀ : IsOpen V₀ := (hV.inter hW).preimage (E 0).continuous
  have hx₀ : x₀ ∈ V₀ := by
    change (E 0) ((E 0).symm (F.uPoint (γ 0).val)) ∈ V ∩ W
    rw [(E 0).apply_symm_apply]
    exact ⟨hxV,hxW⟩
  obtain ⟨c₀,hxc₀,hc₀zero,hc₀disk,hc₀V⟩ := centered_leaf_chart_in_open_g1
    (L (label 0)) x₀ V₀ hV₀ hx₀
  let en (r : unitInterval) := (E 0).toHomeomorph.toOpenPartialHomeomorph.trans
    ((e r).map.trans (E r).symm.toHomeomorph.toOpenPartialHomeomorph)
  let hn (r : unitInterval) := (E 0).toHomeomorph.toOpenPartialHomeomorph.trans
    ((h r).map.trans (E r).symm.toHomeomorph.toOpenPartialHomeomorph)
  have hen (r : unitInterval) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (en r) (en r).source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (en r).symm (en r).target := by
    have heh := intrinsicPresentation_holonomy_holomorphic f a G.rankOne P _ _ _ γ 0 r (e r)
    exact ⟨((E r).symm.contMDiff.contMDiffOn.comp' heh.1).comp' (E 0).contMDiff.contMDiffOn,
      (E 0).symm.contMDiff.contMDiffOn.comp' (heh.2.comp' (E r).contMDiff.contMDiffOn)⟩
  have hhn (r : unitInterval) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (hn r) (hn r).source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (hn r).symm (hn r).target := by
    have hhh := intrinsicPresentation_holonomy_holomorphic f a G.rankOne P _ _ _ γ 0 r (h r)
    exact ⟨((E r).symm.contMDiff.contMDiffOn.comp' hhh.1).comp' (E 0).contMDiff.contMDiffOn,
      (E 0).symm.contMDiff.contMDiffOn.comp' (hhh.2.comp' (E r).contMDiff.contMDiffOn)⟩
  have hdn (r : unitInterval) :
      (E r).toHomeomorph.toOpenPartialHomeomorph.trans (d r) ∈ (Bnative (label r)).maximalAtlas _ :=
    hEmax r (d r) (hd r)
  let dn (r : unitInterval) : LeafChart (L (label r)) :=
    ⟨(E r).toHomeomorph.toOpenPartialHomeomorph.trans (d r),
      (isHolomorphicScalarChart_iff_mem_scalar_maximalAtlas _ _).mp (hdn r).1⟩
  have hsource (r : unitInterval) (z : ℂ) (hz : z ∈ Metric.ball 0 1) :
      c₀.val.symm z ∈ (en r).source ∧ c₀.val.symm z ∈ (hn r).source ∧
        (hn r) (c₀.val.symm z) ∈ (dn r).val.source := by
    have hv := hc₀V z hz
    change (E 0) (c₀.val.symm z) ∈ V ∩ W at hv
    refine ⟨⟨mem_univ _,?_,mem_univ _⟩,⟨mem_univ _,hVsource r hv.1,mem_univ _⟩,?_⟩
    · change (E 0) (c₀.val.symm z) ∈ (e r).map.source
      exact (hesource r).symm ▸ hv.2
    · refine ⟨mem_univ _,?_⟩
      change (E r) ((E r).symm ((h r).map ((E 0) (c₀.val.symm z)))) ∈ (d r).source
      rw [(E r).apply_symm_apply]
      exact hVd r _ hv.1
  have hzero : c₀.val.symm 0 = x₀ := by rw [← hc₀zero,c₀.val.left_inv hxc₀]
  have hgn (r : unitInterval) : (en r : L (label 0) → L (label r)) =ᶠ[𝓝 (c₀.val.symm 0)] hn r := by
    have heq := same_subpath_plaque_chain_germ F γ (e r).chain (h r).map (h r).chain
    have heq' : (e r).map =ᶠ[𝓝 (F.uPoint (γ 0).val)] (h r).map := Filter.Germ.coe_eq.mp heq
    have ht : Tendsto (E 0) (𝓝 (c₀.val.symm 0)) (𝓝 (F.uPoint (γ 0).val)) := by
      have hc := (E 0).continuous.tendsto (c₀.val.symm 0)
      simpa only [hzero,x₀,(E 0).apply_symm_apply] using hc
    filter_upwards [heq'.comp_tendsto ht] with z hz
    exact congrArg (E r).symm hz
  let b : Complex.UnitDisc := ⟨(1/2 : ℂ),by norm_num [Metric.mem_ball,dist_zero_right]⟩
  have hb : b ≠ 0 := by intro h; have hh := congrArg Subtype.val h; change (1/2 : ℂ) = 0 at hh; norm_num at hh
  have hrat (z : Complex.UnitDisc) (hz : z ≠ 0) (hzb : z ≠ b) :
      Continuous (fun r ↦
        ((dn r).val ((hn r) (c₀.val.symm 0)) - (dn r).val ((hn r) (c₀.val.symm z.val))) /
        ((dn r).val ((hn r) (c₀.val.symm 0)) - (dn r).val ((hn r) (c₀.val.symm b.val)))) := by
    have hz0 : (0 : ℂ) ∈ Metric.ball 0 1 := Metric.mem_ball_self (by norm_num)
    have hinj : Set.InjOn (fun z : ℂ ↦ (E 0) (c₀.val.symm z)) (Metric.ball 0 1) :=
      fun z hz w hw heq ↦ c₀.val.symm.injOn (hc₀disk hz) (hc₀disk hw) ((E 0).injective heq)
    have hrat := hratio ((E 0) (c₀.val.symm 0)) (hc₀V 0 hz0).1
      ((E 0) (c₀.val.symm z.val)) (hc₀V z.val z.property).1
      ((E 0) (c₀.val.symm b.val)) (hc₀V b.val b.property).1
      (fun h ↦ hz (Subtype.ext (hinj z.property hz0 h.symm)))
      (fun h ↦ hb (Subtype.ext (hinj b.property hz0 h.symm)))
      (fun h ↦ hzb (Subtype.ext (hinj z.property b.property h)))
    apply hrat.congr
    intro r
    simp only [transportedAffineRatio,hn,dn,OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply,Diffeomorph.coe_toHomeomorph,
      (E r).apply_symm_apply]
  obtain ⟨c,hc,Q,hQhol,hQquad,hQcont⟩ := curve_jet_coefficients_continuous_of_holonomy_germs_g1
    (L (label 0)) hcompact (fun r ↦ L (label r))
    (fun r ↦ nativeLeafJet1Charts L (label r)) (fun r ↦ nativeLeafJet2Charts L (label r))
    (fun r ↦ native_leaf_coefficient_atlases L f a U (label r)) (fun r ↦ σ (label r))
    en hn hen hhn c₀ dn hc₀disk hsource hgn (fun r ↦ hflat (label r) (dn r) (hdn r)) b hb hrat
  have hγ₀ : (γ 0).val = ((F.box k).chart (p 0,w₀)).val := congrArg Subtype.val (hγ 0)
  have hlabel₀ : F.unstableLabel k (p 0) = q 0 :=
    (F.unstable_label k (p 0) w₀).symm.trans (congrArg (Quotient.mk F.unstablePartition) hγ₀.symm)
  let j₀ : FoliationCoordinateDisk 2 → F.ULeaf (γ 0).val := fun w ↦
    ⟨((F.box k).chart (p 0,w)).val,(F.unstable_label k (p 0) w).trans hlabel₀⟩
  have hj₀ : IsOpenEmbedding j₀ := unstable_plaque_open_at_class_g10 F k (p 0) _ hlabel₀
  let : Nonempty (FoliationCoordinateDisk 2) := ⟨w₀⟩
  let e₀ := hj₀.toOpenPartialHomeomorph j₀
  have hWj : W = e₀.target := by
    rw [hWfull,show e₀.target = Set.range j₀ by simp [e₀]]
    ext z
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨w,Subtype.ext hw⟩
    · rintro ⟨w,rfl⟩
      exact ⟨w,rfl⟩
  have hjw : j₀ w₀ = F.uPoint (γ 0).val := Subtype.ext hγ₀.symm
  let δ := e₀.trans ((E 0).symm.toHomeomorph.toOpenPartialHomeomorph.trans c₀.val)
  have hδsource : w₀ ∈ δ.source := by
    refine ⟨by simp [e₀],mem_univ _,?_⟩
    change (E 0).symm (j₀ w₀) ∈ c₀.val.source
    rw [hjw]
    exact hxc₀
  have hδzero : δ w₀ = 0 := by
    change c₀.val ((E 0).symm (j₀ w₀)) = 0
    rw [hjw]
    exact hc₀zero
  have hδtarget : Metric.ball (0 : ℂ) 1 ⊆ δ.target := by
    intro z hz
    refine ⟨⟨hc₀disk hz,mem_univ _⟩,?_⟩
    change (E 0) (c₀.val.symm z) ∈ e₀.target
    exact hWj ▸ (hc₀V z hz).2
  have hδformula (z : ℂ) (hz : z ∈ Metric.ball 0 1) :
      ((F.box k).chart (p 0,δ.symm z)).val = ((E 0) (c₀.val.symm z)).val := by
    have hh := e₀.right_inv (hWj ▸ (hc₀V z hz).2)
    exact congrArg Subtype.val hh
  refine ⟨δ,label,c,Q,hδsource,hδzero,hδtarget,?_,?_,hQquad,hQcont⟩
  · intro r z hz
    rw [hc r]
    exact ⟨hc₀disk hz,(hsource r z hz).1⟩
  · intro r z hz
    rw [← hE r ((c r).val.symm z),hc r]
    change ((E r) ((E r).symm ((e r).map ((E 0) (c₀.val.symm z))))).val = _
    rw [(E r).apply_symm_apply]
    exact heformula r _ (δ.symm z) (hc₀V z hz).2 (hδformula z hz)

/-- Continuity of affine ratios along stable holonomy implies ambient continuity of the associated
native homogeneous jet section. -/
theorem native_section_continuous_of_affine_ratios_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (Bnative : ∀ i, ComplexAffineStructure (L i))
    (σ : letI : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
      letI : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
      ∀ i, HomogeneousCurveJetSection (L i) (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i))
    (hflat : ∀ i (c : LeafChart (L i)), c.val ∈ (Bnative i).maximalAtlas (L i) →
      ∀ j, curveJet1Base (L i) j ∈ c.val.source → (curveJet2Coeff (L i) c ((σ i).val j)).2 = 0)
    (τ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (hτtrunc : ∀ j, nativeLeafwiseJetTruncation L (τ j) = j)
    (hτσ : ∀ i j, τ (nativeLeafwiseJet1Inclusion L i j) =
      nativeLeafwiseJet2Inclusion L i ((σ i).val j))
    (hcompact : IsCompact {g : C(Complex.UnitDisc,ℂ) | IsNormalizedUnivalent g}) :
    letI := P.realCharts
    ∀ (B : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      B.ContinuousAlongStableHolonomy P.foliations P.complexLeaves →
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ∃ (i : ι) (E : Diffeomorph 𝓘(ℂ) (complexModel 1) (L i)
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
          (∀ z, (E z).val = (U.leaf i).inclusion z) ∧
          ∀ c ∈ (B.structureAt q).maximalAtlas _,
            E.toHomeomorph.toOpenPartialHomeomorph.trans c ∈ (Bnative i).maximalAtlas _) →
      letI := nativeLeafwiseJet1Topology L U G.box
      letI := nativeLeafwiseJet2Topology L U G.box
      Continuous τ := by
  classical
  let := P.realCharts
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  intro B hB hident
  apply native_homogeneous_section_continuous_of_unit_evaluation_g1 L f a U G τ hτtrunc
    (fun i ↦ ⟨σ i,hτσ i⟩)
  intro k q hqb hqc
  let A : M → ℂ := fun x ↦ if hx : x ∈ (G.box k).source then
    (nativeLeafwiseJet2Coeff L U (G.box k) (τ (q ⟨G.box k x,(G.box k).map_source hx⟩))).2 else 0
  have hA (x : M) (hx : x ∈ (G.box k).source) : A x =
      (nativeLeafwiseJet2Coeff L U (G.box k) (τ (q ⟨G.box k x,(G.box k).map_source hx⟩))).2 := by
    simp only [A,dite_eq_left hx]
  have hAc : ContinuousOn A (G.box k).source := by
    intro x hx
    obtain ⟨b,hb⟩ := P.foliations.cover x
    let Ψ := (Homeomorph.prodComm (FoliationCoordinateDisk 2) (FoliationCoordinateDisk (2*d-2))).trans
      (P.foliations.box b).chart
    let φ : FoliationCoordinateDisk 2 × FoliationCoordinateDisk (2*d-2) → M :=
      fun p ↦ (Ψ p).val
    have hφ : IsOpenEmbedding φ := (P.foliations.box b).isOpen_image.isOpenEmbedding_subtypeVal.comp
      Ψ.isOpenEmbedding
    let Ω := φ ⁻¹' (G.box k).source
    have hΩ : IsOpen Ω := (G.box k).open_source.preimage hφ.continuous
    let : TietzeExtension.{0,0} (FoliationCoordinateDisk (2*d-2)) :=
      TietzeExtension.of_homeo (Homeomorph.unitBall (E := Fin (2*d-2) → ℝ)).symm
    have hlocal : ContinuousOn (A ∘ φ) Ω := by
      apply continuousOn_of_local_complex_path_charts_g1 (A ∘ φ) Ω hΩ
      intro a₀ a₁ p w₀
      obtain ⟨δ,label,c,Q,hδw,hδzero,hδdisk,hcdisk,hformula,hQ,hQcont⟩ :=
        native_affine_ratio_path_charts_g1 f a P L U G Bnative σ hflat hcompact B hB hident
          b p.toContinuousMap w₀
      refine ⟨δ,hδw,hδzero,hδdisk,?_⟩
      let Ω₀ : Set (ℂ × unitInterval) := Metric.ball 0 1 ×ˢ univ
      let E (p : ℂ × unitInterval) := (U.leaf (label p.2)).inclusion ((c p.2).val.symm p.1)
      have hEq (r : ℂ × unitInterval) (hr : r ∈ Ω₀) :
          E r = φ (δ.symm r.1,p r.2) := hformula r.2 r.1 hr.1
      have hE : ContinuousOn E Ω₀ := by
        have hc : ContinuousOn (fun r : ℂ × unitInterval ↦ φ (δ.symm r.1,p r.2)) Ω₀ :=
          hφ.continuous.comp_continuousOn
          ((δ.symm.continuousOn.comp continuous_fst.continuousOn (fun r hr ↦ hδdisk hr.1)).prodMk
            (p.continuous.comp continuous_snd).continuousOn)
        exact hc.congr hEq
      have hQc : ContinuousOn (fun r : ℂ × unitInterval ↦ Q r.2 r.1) Ω₀ := by
        apply continuousOn_iff_continuous_domRestrict.mpr
        exact hQcont.comp
          (((continuous_fst.comp continuous_subtype_val).subtype_mk (fun r ↦ r.property.1)).prodMk
            (continuous_snd.comp continuous_subtype_val))
      have hnative := native_unit_coefficient_continuous_in_plaque_charts_g1 L f a U G k label
        τ (fun r ↦ σ (label r)) (fun r ↦ hτσ (label r)) c Q hQ Ω₀
        (Metric.isOpen_ball.prod isOpen_univ) (fun r hr ↦ hcdisk r.2 hr.1) hE hQc
        q hqb (fun r ↦ congrArg Prod.snd (hqc r)) A hA
      have hnative' : ContinuousOn (fun r : ℂ × unitInterval ↦ A (E r))
          (Ω₀ ∩ {r | (δ.symm r.1,p r.2) ∈ Ω}) := hnative.mono (by
        intro r hr
        refine ⟨hr.1,?_⟩
        change E r ∈ (G.box k).source
        rw [hEq r hr.1]
        exact hr.2)
      apply hnative'.congr
      intro r hr
      exact congrArg A (hEq r hr.1).symm
    let y := Ψ.symm ⟨x,hb⟩
    have hy : φ y = x := congrArg Subtype.val (Ψ.apply_symm_apply ⟨x,hb⟩)
    have hyΩ : y ∈ Ω := by change φ y ∈ (G.box k).source; rwa [hy]
    have hat := hφ.continuousAt_iff.mp (hlocal.continuousAt (hΩ.mem_nhds hyΩ))
    rw [hy] at hat
    exact hat.continuousWithinAt
  have hsym : Continuous (fun p : (G.box k).target ↦ (G.box k).symm p.val) :=
    (G.box k).symm.continuousOn.comp_continuous continuous_subtype_val (fun p ↦ p.property)
  have hcont := hAc.comp_continuous hsym (fun p ↦ (G.box k).map_target p.property)
  apply hcont.congr
  intro p
  dsimp only [Function.comp_apply]
  rw [hA _ ((G.box k).map_target p.property)]
  congr 3
  apply congrArg q
  apply Subtype.ext
  exact (G.box k).right_inv p.property

/-- Each native leaf admits a point-preserving biholomorphic identification with a leaf of the
supplied presentation. -/
private theorem native_affine_leaf_identification_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U) :
    letI := P.realCharts
    ∀ i, ∃ q : Quotient P.foliations.unstablePartition,
      letI := P.foliations.unstableTopology q
      letI := P.complexLeaves.charts q
      ∃ T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞,
        ∀ z, (T z).val = (U.leaf i).inclusion z := by
  classical
  let := P.realCharts
  intro i
  let : ConnectedSpace (L i) := (U.leaf i).connected
  let z₀ : L i := Classical.arbitrary (L i)
  let q := Quotient.mk P.foliations.unstablePartition ((U.leaf i).inclusion z₀)
  let := P.foliations.unstableTopology q
  let := P.complexLeaves.charts q
  let x : IntrinsicFoliationLeaf P.foliations.unstablePartition q :=
    ⟨(U.leaf i).inclusion z₀, rfl⟩
  obtain ⟨j, E, hE⟩ := native_affine_presentation_identification_g1 f a P L U G q
  have hji : j = i := by
    apply U.disjoint j i (E.symm x) z₀
    rw [← hE, E.apply_symm_apply]
  subst j
  let T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
      (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞ :=
    { E.toEquiv with
      contMDiff_toFun := E.contMDiff.comp (curveProductToScalar_contMDiff_id (L i))
      contMDiff_invFun := (curveScalarToProduct_contMDiff_id (L i)).comp E.symm.contMDiff }
  exact ⟨q, T, hE⟩


/-- Affine action on intrinsic leaves is preserved by point-preserving identifications. -/
private theorem affine_action_on_identified_leaves_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    ∀ (B : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      B.ActsAffinely P.foliations P.complexLeaves f →
      ∀ (q₀ q₁ : Quotient P.foliations.unstablePartition),
      letI := P.foliations.unstableTopology q₀
      letI := P.foliations.unstableTopology q₁
      letI := P.complexLeaves.charts q₀
      letI := P.complexLeaves.charts q₁
      ∀ {N N' : Type u} [TopologicalSpace N] [TopologicalSpace N']
        (S : N ≃ₜ IntrinsicFoliationLeaf P.foliations.unstablePartition q₀)
        (T : N' ≃ₜ IntrinsicFoliationLeaf P.foliations.unstablePartition q₁)
        (g : N → N') (_hmap : ∀ w, (T (g w)).val = f (S w).val)
        (c : OpenPartialHomeomorph N ℂ) (e : OpenPartialHomeomorph N' ℂ),
        S.symm.toOpenPartialHomeomorph.trans c ∈
          ComplexAffineStructure.maximalAtlas _ (B.structureAt q₀) →
        T.symm.toOpenPartialHomeomorph.trans e ∈
          ComplexAffineStructure.maximalAtlas _ (B.structureAt q₁) →
        ∀ (x : M) (z : N), (S z).val = x → z ∈ c.source → g z ∈ e.source →
          ∃ b : ComplexAffineTransformation,
            ∀ᶠ w in 𝓝 z, e (g w) = b.apply (c w) := by
  let := P.realCharts
  intro B hB q₀ q₁
  let := P.foliations.unstableTopology q₀
  let := P.foliations.unstableTopology q₁
  let := P.complexLeaves.charts q₀
  let := P.complexLeaves.charts q₁
  intro N N' _ _ S T g hmap c e hc he x z hx hzc hze
  have hq₀ : q₀ = Quotient.mk P.foliations.unstablePartition x := by
    rw [← hx]
    exact (S z).property.symm
  have hq₁ : q₁ = Quotient.mk P.foliations.unstablePartition (f x) := by
    rw [← hx, ← hmap]
    exact (T (g z)).property.symm
  subst q₀
  subst q₁
  have hSpoint : S z = P.foliations.uPoint x := Subtype.ext hx
  have hTpoint : T (g z) = P.foliations.uPoint (f x) :=
    Subtype.ext ((hmap z).trans (congrArg f hx))
  have hcpoint : P.foliations.uPoint x ∈ (S.symm.toOpenPartialHomeomorph.trans c).source := by
    rw [← hSpoint]
    simpa using hzc
  have hepoint : P.foliations.uPoint (f x) ∈ (T.symm.toOpenPartialHomeomorph.trans e).source := by
    rw [← hTpoint]
    simpa using hze
  obtain ⟨b, hb⟩ := hB x _ _ hc he hcpoint hepoint
  refine ⟨b, ?_⟩
  rw [← hSpoint] at hb
  have hn := S.continuous.tendsto z hb
  filter_upwards [hn] with w hw
  obtain ⟨_, y, hy, _, heq⟩ := hw
  have hyT : y = T (g w) := Subtype.ext (hy.trans (hmap w).symm)
  rw [hyT] at heq
  simpa only [OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
    Homeomorph.symm_apply_apply] using heq

/-- A supplied intrinsic foliation presentation admits a unique invariant affine family satisfying
holonomy-ratio continuity, and every leaf of this family is complete. (Ghys, Prop. 3.1, p. 590;
Lemma 3.2, p. 591; Lemma 3.3, pp. 592–593) -/
theorem native_invariant_affine_family_on_presentation_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (hcomplete : ∀ i, (G.affineAt f a L U i).Complete (L i)) :
    letI := P.realCharts
    ∃ A : AffineUnstableLeafStructures P.foliations P.complexLeaves,
      A.ActsAffinely P.foliations P.complexLeaves f ∧
      A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves ∧
      (∀ B : AffineUnstableLeafStructures P.foliations P.complexLeaves,
        B.ActsAffinely P.foliations P.complexLeaves f →
        B.ContinuousAlongStableHolonomy P.foliations P.complexLeaves → B = A) ∧
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ComplexAffineStructure.Complete
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) (A.structureAt q)) := by
  classical
  let := P.realCharts
  obtain ⟨A, hA⟩ := native_affine_presentation_atlases_g1 f a P L U G hcomplete
  have hAct : A.ActsAffinely P.foliations P.complexLeaves f := by
    apply native_affine_presentation_action_g1 f a P L U G A
    intro q
    let := P.foliations.unstableTopology q
    let := P.complexLeaves.charts q
    obtain ⟨i, T, B, hT, hB, hAB, hcomp, hflat⟩ := hA q
    exact ⟨i, T, hT, fun e ↦ (hflat e).trans (G.flat_chart_iff i _).symm⟩
  have hComp : ∀ q : Quotient P.foliations.unstablePartition,
      letI := P.foliations.unstableTopology q
      letI := P.complexLeaves.charts q
      ComplexAffineStructure.Complete
        (IntrinsicFoliationLeaf P.foliations.unstablePartition q) (A.structureAt q) := by
    intro q
    let := P.foliations.unstableTopology q
    let := P.complexLeaves.charts q
    obtain ⟨i, T, B, hT, hB, hAB, hcomp, hflat⟩ := hA q
    exact hcomp
  have hCoordinates : A.HasContinuousPrefixCoordinates P.foliations P.complexLeaves := by
    apply native_affine_holonomy_coordinates_g1 f a P L U G A
    intro q
    let := P.foliations.unstableTopology q
    let := P.complexLeaves.charts q
    obtain ⟨i, T, B, hT, hB, hAB, hcomp, hflat⟩ := hA q
    exact ⟨i, T, hT, fun e ↦ (hflat e).trans (G.flat_chart_iff i _).symm⟩
  have hContinuity : A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves :=
    affine_holonomy_ratio_continuous_of_prefix_coordinates_g1 _ _ A hCoordinates
  suffices hUnique : ∀ B : AffineUnstableLeafStructures P.foliations P.complexLeaves,
      B.ActsAffinely P.foliations P.complexLeaves f →
      B.ContinuousAlongStableHolonomy P.foliations P.complexLeaves → B = A by
    exact ⟨A, hAct, hContinuity, hUnique, hComp⟩
  intro B hBAct hBContinuity
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  choose q T hT using native_affine_leaf_identification_g1 f a P L U G
  have hPullback (i : ι) :
      letI := P.foliations.unstableTopology (q i)
      letI := P.complexLeaves.charts (q i)
      ∃ C : ComplexAffineAtlas (L i),
      C.charts = {e | ∃ c ∈ (B.structureAt (q i)).out.charts,
        e = (T i).symm.toHomeomorph.symm.toOpenPartialHomeomorph.trans c} := by
    let := P.foliations.unstableTopology (q i)
    let := P.complexLeaves.charts (q i)
    exact exists_complexAffineAtlas_transport (T i).symm (B.structureAt (q i)).out
  choose C hC using hPullback
  let Bnative : ∀ i, ComplexAffineStructure (L i) := fun i ↦ Quotient.mk _ (C i)
  obtain ⟨τ, hτtrunc, hτhom, hτleaf, hτflat⟩ :=
    native_affine_family_has_section_g1 L Bnative
  have hBchart (i : ι) :
      letI := P.foliations.unstableTopology (q i)
      letI := P.complexLeaves.charts (q i)
      ∀ e : OpenPartialHomeomorph (L i) ℂ,
        e ∈ ComplexAffineStructure.maximalAtlas _ (Bnative i) ↔
          (T i).symm.toHomeomorph.toOpenPartialHomeomorph.trans e ∈
            ComplexAffineStructure.maximalAtlas _ (B.structureAt (q i)) := by
    let := P.foliations.unstableTopology (q i)
    let := P.complexLeaves.charts (q i)
    intro e
    change e ∈ ComplexAffineStructure.maximalAtlas _ (Quotient.mk _ (C i)) ↔ _
    rw [affine_maximalAtlas_transport_iff_g1 (T i).symm _ (C i) (hC i) e]
    have hout : Quotient.mk (complexAffineAtlasSetoid
        (IntrinsicFoliationLeaf P.foliations.unstablePartition (q i)))
        (B.structureAt (q i)).out = B.structureAt (q i) := Quotient.out_eq _
    rw [hout]
  have hNativePull : ∀ i (e : OpenPartialHomeomorph (L (G.permutation i)) ℂ),
      e ∈ ComplexAffineStructure.maximalAtlas _ (Bnative (G.permutation i)) →
        (G.leafMap i).toHomeomorph.toOpenPartialHomeomorph.trans e ∈
          ComplexAffineStructure.maximalAtlas _ (Bnative i) := by
    intro i e he
    let c := (G.leafMap i).toHomeomorph.toOpenPartialHomeomorph.trans e
    change IsHolomorphicScalarChart (L i) c ∧ _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact he.1.1.comp
        (curveScalarToProduct_contMDiff (G.leafMap i).contMDiff).contMDiffOn
        (fun _ hx ↦ hx.2)
    · have ht : c.target = e.target := by simp [c]
      change ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ c.symm c.target
      rw [ht]
      exact (curveScalarToProduct_contMDiff (G.leafMap i).symm.contMDiff).comp_contMDiffOn he.1.2
    · intro d hd z hz
      let := P.foliations.unstableTopology (q i)
      let := P.complexLeaves.charts (q i)
      let := P.foliations.unstableTopology (q (G.permutation i))
      let := P.complexLeaves.charts (q (G.permutation i))
      have hdmax : d ∈ ComplexAffineStructure.maximalAtlas _ (Bnative i) :=
        ⟨(Bnative i).out.holomorphic d hd, fun e he ↦ (Bnative i).out.compatible e he d hd⟩
      have hmap (w : L i) : ((T (G.permutation i)) ((G.leafMap i) w)).val =
          f ((T i) w).val := by
        rw [hT (G.permutation i), hT i, G.leafMap_inclusion]
      obtain ⟨b, hb⟩ := affine_action_on_identified_leaves_g1 f a P B hBAct
        (q i) (q (G.permutation i)) (T i).toHomeomorph
        (T (G.permutation i)).toHomeomorph (G.leafMap i) hmap d e
        ((hBchart i d).mp hdmax) ((hBchart (G.permutation i) e).mp he)
        ((U.leaf i).inclusion z) z (hT i z) hz.1 hz.2.2
      refine ⟨b, ?_⟩
      change ∀ᶠ w in 𝓝 z, e ((G.leafMap i) w) = b.apply (d w)
      exact hb
  have hτinvariant : ∀ i (γ η : CurveParamGerm (L i)),
      τ (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ)) =
        nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) η) →
      τ (nativeLeafwiseJet1Inclusion L (G.permutation i)
        (curveJet1Class (L (G.permutation i)) (curveParamGermPostcompose (G.leafMap i) γ))) =
        nativeLeafwiseJet2Inclusion L (G.permutation i)
          (curveJet2Class (L (G.permutation i)) (curveParamGermPostcompose (G.leafMap i) η)) :=
    native_affine_family_section_graph_preserved_g1 L Bnative τ hτtrunc
      (fun i e he ↦ ((hτflat i e).mp he).2) G.permutation G.leafMap hNativePull
  suffices hτeq : τ = G.jetSection by
    have hNativeMax (i : ι) (e : OpenPartialHomeomorph (L i) ℂ) :
        e ∈ (Bnative i).maximalAtlas (L i) ↔
          e ∈ (G.affineAt f a L U i).maximalAtlas (L i) := by
      exact (hτflat i e).trans (by rw [hτeq]; exact (G.flat_chart_iff i e).symm)
    have hAforward (i : ι) :
        letI := P.foliations.unstableTopology (q i)
        letI := P.complexLeaves.charts (q i)
        ∀ e : OpenPartialHomeomorph (IntrinsicFoliationLeaf P.foliations.unstablePartition (q i)) ℂ,
          e ∈ (A.structureAt (q i)).maximalAtlas _ ↔
            (T i).toHomeomorph.toOpenPartialHomeomorph.trans e ∈
              (G.affineAt f a L U i).maximalAtlas (L i) := by
      let := P.foliations.unstableTopology (q i)
      let := P.complexLeaves.charts (q i)
      obtain ⟨j,S,C',hS,hC',hAC',hcomp,hflat⟩ := hA (q i)
      let : ConnectedSpace (L i) := (U.leaf i).connected
      let z : L i := Classical.arbitrary (L i)
      have hji : j = i := U.disjoint j i (S.symm (T i z)) z (by
        rw [← hS,S.apply_symm_apply,hT])
      subst j
      have hST : S = T i := by
        ext w
        exact (hS w).trans (hT i w).symm
      subst S
      intro e
      exact (hflat e).trans (G.flat_chart_iff i _).symm
    have hAt (i : ι) : B.structureAt (q i) = A.structureAt (q i) := by
      let := P.foliations.unstableTopology (q i)
      let := P.complexLeaves.charts (q i)
      apply affine_structure_eq_of_maximal_charts_g1
      intro e
      let e' := (T i).toHomeomorph.toOpenPartialHomeomorph.trans e
      have heq : (T i).symm.toHomeomorph.toOpenPartialHomeomorph.trans e' = e := by
        change (T i).toHomeomorph.symm.toOpenPartialHomeomorph.trans e' = e
        rw [show e' = (T i).toHomeomorph.toOpenPartialHomeomorph.trans e from rfl,
          ← OpenPartialHomeomorph.trans_assoc, ← Homeomorph.trans_toOpenPartialHomeomorph,
          Homeomorph.symm_trans_self]
        exact OpenPartialHomeomorph.refl_trans e
      have hBe := hBchart i e'
      rw [heq] at hBe
      exact hBe.symm.trans ((hNativeMax i e').trans (hAforward i e).symm)
    have hqsurj : Function.Surjective q := by
      intro Q
      obtain ⟨i,z,hz⟩ := U.cover Q.out
      refine ⟨i,?_⟩
      calc
        q i = Quotient.mk P.foliations.unstablePartition (T i z).val := (T i z).property.symm
        _ = Quotient.mk P.foliations.unstablePartition Q.out := by rw [hT,hz]
        _ = Q := Quotient.out_eq Q
    have hstr : B.structureAt = A.structureAt := by
      funext Q
      obtain ⟨i,rfl⟩ := hqsurj Q
      exact hAt i
    cases B
    cases A
    cases hstr
    rfl
  choose σ hτσ using hτleaf
  have hσflat (i : ι) (c : LeafChart (L i))
      (hc : c.val ∈ (Bnative i).maximalAtlas _) :
      ∀ j, curveJet1Base (L i) j ∈ c.val.source →
        (curveJet2Coeff (L i) c ((σ i).val j)).2 = 0 := by
    apply curve_jet_section_flat_coeff_of_graph (L i) (σ i) c
    intro γ hγ heq
    apply (((hτflat i c.val).mp hc).2 γ hγ).mp
    rw [hτσ,heq]
  have hident : ∀ Q : Quotient P.foliations.unstablePartition,
      letI := P.foliations.unstableTopology Q
      letI := P.complexLeaves.charts Q
      ∃ (i : ι) (E : Diffeomorph 𝓘(ℂ) (complexModel 1) (L i)
        (IntrinsicFoliationLeaf P.foliations.unstablePartition Q) ∞),
        (∀ z, (E z).val = (U.leaf i).inclusion z) ∧
        ∀ c ∈ (B.structureAt Q).maximalAtlas _,
          E.toHomeomorph.toOpenPartialHomeomorph.trans c ∈ (Bnative i).maximalAtlas _ := by
    intro Q
    let := P.foliations.unstableTopology Q
    let := P.complexLeaves.charts Q
    obtain ⟨i,z,hz⟩ := U.cover Q.out
    have hiq : q i = Q := (T i z).property.symm.trans
      ((congrArg (Quotient.mk P.foliations.unstablePartition) ((hT i z).trans hz)).trans
        (Quotient.out_eq Q))
    cases hiq
    let E : Diffeomorph 𝓘(ℂ) (complexModel 1) (L i)
        (IntrinsicFoliationLeaf P.foliations.unstablePartition (q i)) ∞ := {
      (T i).toEquiv with
      contMDiff_toFun := (T i).contMDiff.comp (curveScalarToProduct_contMDiff_id (L i))
      contMDiff_invFun := (curveProductToScalar_contMDiff_id (L i)).comp (T i).symm.contMDiff }
    refine ⟨i,E,hT i,?_⟩
    intro c hc
    apply (hBchart i _).mpr
    change (T i).toHomeomorph.symm.toOpenPartialHomeomorph.trans
      ((T i).toHomeomorph.toOpenPartialHomeomorph.trans c) ∈ _
    rw [← OpenPartialHomeomorph.trans_assoc,← Homeomorph.trans_toOpenPartialHomeomorph,
      Homeomorph.symm_trans_self]
    change (OpenPartialHomeomorph.refl _).trans c ∈ _
    rw [OpenPartialHomeomorph.refl_trans]
    exact hc
  have hτcontinuous :
      letI := nativeLeafwiseJet1Topology L U G.box
      letI := nativeLeafwiseJet2Topology L U G.box
      Continuous τ := native_section_continuous_of_affine_ratios_g1 f a P L U G
        Bnative σ hσflat τ hτtrunc hτσ normalized_univalent_compactness B hBContinuity hident
  
  
  apply native_invariant_jet_section_unique_g1 f a L U G τ
    hτtrunc hτhom hτcontinuous
  intro i γ η he
  exact ⟨curveParamGermPostcompose (G.leafMap i) γ,
    curveParamGermPostcompose (G.leafMap i) η, rfl, rfl, hτinvariant i γ η he⟩

end HolomorphicAnosov.Ghys
