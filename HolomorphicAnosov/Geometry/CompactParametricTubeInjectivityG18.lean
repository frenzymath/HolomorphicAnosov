import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import HolomorphicAnosov.Analysis.ParametricInverseSpatialRegularityG18
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic

noncomputable section
open Set Filter Metric
open scoped _root_.Topology
namespace HolomorphicAnosov

/-- Local injectivity near each point of an embedded compact zero section becomes injectivity on one uniform normal tube, uniformly for nearby parameters. -/
theorem compact_parametric_tube_injectivity_g18
    {P V N E : Type*} [TopologicalSpace P] [TopologicalSpace V]
    [PseudoMetricSpace N] [Zero N] [TopologicalSpace E] [T2Space E]
    (F : P → V × N → E) (p₀ : P) (C : Set V) (hC : IsCompact C)
    (hF : ∀ v ∈ C, ContinuousAt (fun z : P × (V × N) ↦ F z.1 z.2) (p₀,(v,0)))
    (hinj : InjOn (fun v ↦ F p₀ (v,0)) C)
    (hlocal : ∀ v ∈ C, ∃ U ∈ 𝓝 p₀, ∃ S ∈ 𝓝 (v,(0 : N)),
      ∀ p ∈ U, InjOn (F p) S) :
    ∃ U ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ U, InjOn (F p) (C ×ˢ ball (0 : N) ε) := by
  let X := P × (N × N)
  let R : X → V × V → Prop := fun x v ↦
    F x.1 (v.1,x.2.1) = F x.1 (v.2,x.2.2) → (v.1,x.2.1) = (v.2,x.2.2)
  have hall : ∀ᶠ x : X in 𝓝 (p₀,(0,0)), ∀ v ∈ C ×ˢ C, R x v := by
    apply (hC.prod hC).eventually_forall_of_forall_eventually
    rintro ⟨v,w⟩ ⟨hv,hw⟩
    let φ₁ : X × (V × V) → P × (V × N) := fun z ↦ (z.1.1,(z.2.1,z.1.2.1))
    let φ₂ : X × (V × V) → P × (V × N) := fun z ↦ (z.1.1,(z.2.2,z.1.2.2))
    have hc₁ : Continuous φ₁ := by dsimp [φ₁, X]; fun_prop
    have hc₂ : Continuous φ₂ := by dsimp [φ₂, X]; fun_prop
    by_cases heq : v = w
    · subst w
      obtain ⟨U,hU,S,hS,hUS⟩ := hlocal v hv
      have hnearU : ∀ᶠ z : X × (V × V) in 𝓝 ((p₀,(0,0)),(v,v)), z.1.1 ∈ U :=
        (continuous_fst.comp continuous_fst).continuousAt.preimage_mem_nhds hU
      have hnear₁ : ∀ᶠ z : X × (V × V) in 𝓝 ((p₀,(0,0)),(v,v)), (z.2.1,z.1.2.1) ∈ S :=
        (continuous_snd.comp hc₁).continuousAt.preimage_mem_nhds hS
      have hnear₂ : ∀ᶠ z : X × (V × V) in 𝓝 ((p₀,(0,0)),(v,v)), (z.2.2,z.1.2.2) ∈ S :=
        (continuous_snd.comp hc₂).continuousAt.preimage_mem_nhds hS
      filter_upwards [hnearU,hnear₁,hnear₂] with z hp h₁ h₂
      exact hUS z.1.1 hp h₁ h₂
    · have hvw : F p₀ (v,0) ≠ F p₀ (w,0) := fun h ↦ heq (hinj hv hw h)
      have hcF₁ := (hF v hv).comp (x := ((p₀,(0,0)),(v,w))) hc₁.continuousAt
      have hcF₂ := (hF w hw).comp (x := ((p₀,(0,0)),(v,w))) hc₂.continuousAt
      have hn := (hcF₁.ne_iff_eventually_ne hcF₂).mp hvw
      filter_upwards [hn] with z hz
      exact fun h ↦ (hz h).elim
  obtain ⟨U,hU,S,hS,hUS⟩ := mem_nhds_prod_iff.mp hall
  obtain ⟨ε,hε,hεS⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨U,hU,ε,hε,?_⟩
  intro p hp z hz w hw heq
  have hnormal : (z.2,w.2) ∈ S := hεS (by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Prod.fst_zero, Prod.snd_zero]
      using And.intro hz.2 hw.2)
  exact hUS (show (p,(z.2,w.2)) ∈ U ×ˢ S from ⟨hp,hnormal⟩)
    (z.1,w.1) ⟨hz.1,hw.1⟩ heq


/-- A jointly open family of actual inverse-chart domains gives a common parameter neighborhood of local injectivity at every retained source point. -/
theorem parametric_chart_local_injectivity_g18
    {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    (F : P → X → Y) (p₀ : P) (x₀ : X)
    (Q : TopologicalSpace.Opens P) (hp₀ : p₀ ∈ Q)
    (e : Q → OpenPartialHomeomorph X Y) (he : ∀ p : Q, (e p : X → Y) = F p.val)
    (hopen : IsOpen {z : Q × X | z.2 ∈ (e z.1).source})
    (hcenter : x₀ ∈ (e ⟨p₀,hp₀⟩).source) :
    ∃ U ∈ 𝓝 p₀, ∃ S ∈ 𝓝 x₀, ∀ p ∈ U, InjOn (F p) S := by
  obtain ⟨U,hU,S,hS,hUS⟩ := mem_nhds_prod_iff.mp (hopen.mem_nhds hcenter)
  have hU' : Subtype.val '' U ∈ 𝓝 p₀ := by
    have h := mem_nhds_subtype_iff_nhdsWithin.mp hU
    rwa [nhdsWithin_eq_nhds.mpr (Q.isOpen.mem_nhds hp₀)] at h
  refine ⟨Subtype.val '' U,hU',S,hS,?_⟩
  rintro p ⟨p',hp',rfl⟩ z hz w hw heq
  apply (e p').injOn (hUS (show (p',z) ∈ U ×ˢ S from ⟨hp',hz⟩))
    (hUS (show (p',w) ∈ U ×ˢ S from ⟨hp',hw⟩))
  simpa only [he p'] using heq

/-- Apply uniform compact tube injectivity to actual local inverse charts with jointly open domains. -/
theorem compact_parametric_tube_injectivity_of_charts_g18
    {P V N E : Type*} [TopologicalSpace P] [TopologicalSpace V]
    [PseudoMetricSpace N] [Zero N] [TopologicalSpace E] [T2Space E]
    (F : P → V × N → E) (p₀ : P) (C : Set V) (hC : IsCompact C)
    (hF : ∀ v ∈ C, ContinuousAt (fun z : P × (V × N) ↦ F z.1 z.2) (p₀,(v,0)))
    (hinj : InjOn (fun v ↦ F p₀ (v,0)) C)
    (hcharts : ∀ v ∈ C, ∃ Q : TopologicalSpace.Opens P, ∃ hp : p₀ ∈ Q,
      ∃ e : Q → OpenPartialHomeomorph (V × N) E,
        (∀ p : Q, (e p : V × N → E) = F p.val) ∧
        IsOpen {z : Q × (V × N) | z.2 ∈ (e z.1).source} ∧
        (v,0) ∈ (e ⟨p₀,hp⟩).source) :
    ∃ U ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ U, InjOn (F p) (C ×ˢ ball (0 : N) ε) := by
  apply compact_parametric_tube_injectivity_g18 F p₀ C hC hF hinj
  intro v hv
  obtain ⟨Q,hp,e,he,hopen,hcenter⟩ := hcharts v hv
  exact parametric_chart_local_injectivity_g18 F p₀ (v,0) Q hp e he hopen hcenter


/-- A continuous spatial C¹ family with invertible derivative has a common neighborhood of local injectivity at an arbitrary source point. -/
theorem parametric_c1_local_injectivity_g18
    {P X Y : Type*} [TopologicalSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : P → X → Y) (D : P × X → X →L[ℝ] Y)
    (S : Set (P × X)) (hS : IsOpen S) (p₀ : P) (x₀ : X) (hp₀ : (p₀,x₀) ∈ S)
    (hf : ContinuousOn (fun z : P × X ↦ f z.1 z.2) S) (hD : ContinuousOn D S)
    (hd : ∀ z ∈ S, HasFDerivAt (f z.1) (D z) z.2)
    (A : X ≃L[ℝ] Y) (hA : D (p₀,x₀) = A.toContinuousLinearMap) :
    ∃ U ∈ 𝓝 p₀, ∃ T ∈ 𝓝 x₀, ∀ p ∈ U, InjOn (f p) T := by
  let j : P × X → P × X := fun z ↦ (z.1,x₀+z.2)
  have hj : Continuous j := continuous_fst.prodMk (continuous_const.add continuous_snd)
  let f₀ : P → X → Y := fun p z ↦ f p (x₀+z)
  let D₀ : P × X → X →L[ℝ] Y := D ∘ j
  let S₀ := j ⁻¹' S
  have hpS₀ : (p₀,0) ∈ S₀ := by simpa only [S₀,j,mem_preimage,add_zero] using hp₀
  have hd₀ : ∀ z ∈ S₀, HasFDerivAt (f₀ z.1) (D₀ z) z.2 := by
    intro z hz
    have h := (hd (j z) hz).comp z.2 ((hasFDerivAt_id z.2).const_add x₀)
    change HasFDerivAt (f₀ z.1) ((D₀ z).comp (ContinuousLinearMap.id ℝ X)) z.2 at h
    simpa only [ContinuousLinearMap.comp_id] using h
  have hA₀ : D₀ (p₀,0) = A.toContinuousLinearMap := by simpa [D₀,j] using hA
  obtain ⟨Q,hpQ,W,hW,hfW,e,he,hg,hgD,hcenter,hopen⟩ :=
    Analysis.parametric_c1_inverse_at_equiv_g18 f₀ D₀ S₀ (hS.preimage hj) p₀ hpS₀
      (hf.comp hj.continuousOn (fun _ hz ↦ hz))
      (hD.comp hj.continuousOn (fun _ hz ↦ hz)) hd₀ A hA₀
  obtain ⟨U,hU,T,hT,hinj⟩ := parametric_chart_local_injectivity_g18 f₀ p₀ 0 Q hpQ e
    (fun p ↦ (he p).1) hopen hcenter
  have hT' : (fun z : X ↦ z-x₀) ⁻¹' T ∈ 𝓝 x₀ := by
    have hc : ContinuousAt (fun z : X ↦ z-x₀) x₀ :=
      (continuous_id.sub continuous_const).continuousAt
    exact hc.preimage_mem_nhds (by simpa only [sub_self] using hT)
  refine ⟨U,hU,(fun z : X ↦ z-x₀) ⁻¹' T,hT',?_⟩
  intro p hp z hz w hw hzw
  have heq := hinj p hp hz hw (show f₀ p (z-x₀) = f₀ p (w-x₀) by
    simpa [f₀,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hzw)
  have h := congrArg (fun v : X ↦ x₀+v) heq
  simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using h

/-- A jointly continuous C¹ family that is locally nonsingular along an embedded compact zero section is injective on one common normal tube for nearby parameters. -/
theorem compact_parametric_c1_tube_injectivity_g18
    {P V N E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : P → V × N → E) (D : P × (V × N) → (V × N) →L[ℝ] E)
    (S : Set (P × (V × N))) (hS : IsOpen S) (p₀ : P) (C : Set V) (hC : IsCompact C)
    (hmem : ∀ v ∈ C, (p₀,(v,0)) ∈ S)
    (hF : ContinuousOn (fun z : P × (V × N) ↦ F z.1 z.2) S)
    (hD : ContinuousOn D S) (hd : ∀ z ∈ S, HasFDerivAt (F z.1) (D z) z.2)
    (hinj : InjOn (fun v ↦ F p₀ (v,0)) C)
    (hinvert : ∀ v ∈ C, (D (p₀,(v,0))).IsInvertible) :
    ∃ U ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ U, InjOn (F p) (C ×ˢ ball (0 : N) ε) := by
  apply compact_parametric_tube_injectivity_g18 F p₀ C hC
    (fun v hv ↦ hF.continuousAt (hS.mem_nhds (hmem v hv))) hinj
  intro v hv
  obtain ⟨A,hA⟩ := hinvert v hv
  exact parametric_c1_local_injectivity_g18 F D S hS p₀ (v,0) (hmem v hv) hF hD hd A hA.symm


/-- An open joint domain containing a compact zero section contains a uniform normal tube over that same compact core for nearby parameters. -/
theorem compact_zero_section_tube_subset_g18
    {P V N : Type*} [TopologicalSpace P] [TopologicalSpace V]
    [PseudoMetricSpace N] [Zero N]
    (S : Set (P × (V × N))) (hS : IsOpen S) (p₀ : P) (C : Set V) (hC : IsCompact C)
    (hmem : ∀ v ∈ C, (p₀,(v,0)) ∈ S) :
    ∃ U ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ U, ∀ z ∈ C ×ˢ ball (0 : N) ε, (p,z) ∈ S := by
  have hall : ∀ᶠ z : P × N in 𝓝 (p₀,0), ∀ v ∈ C, (z.1,(v,z.2)) ∈ S := by
    apply hC.eventually_forall_of_forall_eventually
    intro v hv
    have hc : Continuous (fun z : (P × N) × V ↦ (z.1.1,(z.2,z.1.2))) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (hS.mem_nhds (hmem v hv))
  obtain ⟨U,hU,T,hT,hUT⟩ := mem_nhds_prod_iff.mp hall
  obtain ⟨ε,hε,hεT⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨U,hU,ε,hε,?_⟩
  intro p hp z hz
  exact hUT (show (p,z.2) ∈ U ×ˢ T from ⟨hp,hεT hz.2⟩) z.1 hz.1

/-- The compact C¹ tube can be chosen inside the given joint domain. -/
theorem compact_parametric_c1_tube_injectivity_with_domain_g18
    {P V N E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : P → V × N → E) (D : P × (V × N) → (V × N) →L[ℝ] E)
    (S : Set (P × (V × N))) (hS : IsOpen S) (p₀ : P) (C : Set V) (hC : IsCompact C)
    (hmem : ∀ v ∈ C, (p₀,(v,0)) ∈ S)
    (hF : ContinuousOn (fun z : P × (V × N) ↦ F z.1 z.2) S)
    (hD : ContinuousOn D S) (hd : ∀ z ∈ S, HasFDerivAt (F z.1) (D z) z.2)
    (hinj : InjOn (fun v ↦ F p₀ (v,0)) C)
    (hinvert : ∀ v ∈ C, (D (p₀,(v,0))).IsInvertible) :
    ∃ U ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ U,
      InjOn (F p) (C ×ˢ ball (0 : N) ε) ∧
      ∀ z ∈ C ×ˢ ball (0 : N) ε, (p,z) ∈ S := by
  obtain ⟨U,hU,ε,hε,hi⟩ :=
    compact_parametric_c1_tube_injectivity_g18 F D S hS p₀ C hC hmem hF hD hd hinj hinvert
  obtain ⟨W,hW,δ,hδ,hsub⟩ := compact_zero_section_tube_subset_g18 S hS p₀ C hC hmem
  refine ⟨U ∩ W,inter_mem hU hW,min ε δ,lt_min hε hδ,?_⟩
  intro p hp
  refine ⟨(hi p hp.1).mono (prod_mono (Subset.refl C) (ball_subset_ball (min_le_left ε δ))),?_⟩
  intro z hz
  exact hsub p hp.2 z ⟨hz.1,ball_subset_ball (min_le_right ε δ) hz.2⟩

/-- Shrink the uniform tube into the open locus where its actual full spatial derivative is invertible. -/
theorem compact_parametric_c1_tube_regular_g18
    {P V N E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : P → V × N → E) (D : P × (V × N) → (V × N) →L[ℝ] E)
    (S : Set (P × (V × N))) (hS : IsOpen S) (p₀ : P) (C : Set V) (hC : IsCompact C)
    (hmem : ∀ v ∈ C, (p₀,(v,0)) ∈ S)
    (hF : ContinuousOn (fun z : P × (V × N) ↦ F z.1 z.2) S)
    (hD : ContinuousOn D S) (hd : ∀ z ∈ S, HasFDerivAt (F z.1) (D z) z.2)
    (hinj : InjOn (fun v ↦ F p₀ (v,0)) C)
    (hinvert : ∀ v ∈ C, (D (p₀,(v,0))).IsInvertible) :
    ∃ U ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ U,
      InjOn (F p) (C ×ˢ ball (0 : N) ε) ∧
      ∀ z ∈ C ×ˢ ball (0 : N) ε, (p,z) ∈ S ∧ (D (p,z)).IsInvertible := by
  let S' := S ∩ D ⁻¹' {A | A.IsInvertible}
  have hS' : IsOpen S' :=
    hD.isOpen_inter_preimage hS ContinuousLinearMap.isOpen_setOfPred_isInvertible
  exact compact_parametric_c1_tube_injectivity_with_domain_g18 F D S' hS' p₀ C hC
    (fun v hv ↦ ⟨hmem v hv,hinvert v hv⟩) (hF.mono inter_subset_left)
    (hD.mono inter_subset_left) (fun z hz ↦ hd z hz.1) hinj hinvert

/-- An injective C¹ map with invertible derivatives on an open domain gives one actual C¹ partial homeomorphism onto its own open image. -/
theorem injOn_c1_openPartialHomeomorph_g18
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hinj : InjOn f U) (hreg : ∀ z ∈ U, (fderiv ℝ f z).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ e.source = U ∧
      e.target = f '' U ∧ ContDiffOn ℝ 1 e e.source ∧
      ContDiffOn ℝ 1 e.symm e.target := by
  classical
  let pe : PartialEquiv E F := hinj.toPartialEquiv f U
  have hopen : IsOpenMap (U.domRestrict f) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    have hs := hf.contDiffAt (hU.mem_nhds z.property)
    obtain ⟨A,hA⟩ := hreg z.val z.property
    have hd : HasFDerivAt f A.toContinuousLinearMap z.val := by
      rw [hA]
      exact (hs.differentiableAt (by simp)).hasFDerivAt
    have hmap := (hs.hasStrictFDerivAt' hd (by simp)).map_nhds_eq_of_equiv
    change 𝓝 (f z.val) ≤ Filter.map (f ∘ Subtype.val) (𝓝 z)
    rw [← Filter.map_map,map_nhds_subtype_val,
      nhdsWithin_eq_nhds.mpr (hU.mem_nhds z.property),hmap]
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe hf.continuousOn hopen hU
  refine ⟨e,rfl,rfl,rfl,hf,?_⟩
  intro w hw
  have hp : e.symm w ∈ U := e.map_target hw
  have hs := hf.contDiffAt (hU.mem_nhds hp)
  obtain ⟨A,hA⟩ := hreg _ hp
  have hd : HasFDerivAt e A.toContinuousLinearMap (e.symm w) := by
    change HasFDerivAt f A.toContinuousLinearMap (e.symm w)
    rw [hA]
    exact (hs.differentiableAt (by simp)).hasFDerivAt
  exact (e.contDiffAt_symm hw hd hs).contDiffWithinAt

/-- The regular compact tube has an actual C¹ inverse on its own open image for every nearby parameter, with the literal forward map and original domain retained. -/
theorem compact_parametric_c1_tube_charts_g18
    {P V N E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : P → V × N → E) (D : P × (V × N) → (V × N) →L[ℝ] E)
    (S : Set (P × (V × N))) (hS : IsOpen S) (p₀ : P) (C : Set V) (hC : IsCompact C)
    (hmem : ∀ v ∈ C, (p₀,(v,0)) ∈ S)
    (hF : ContinuousOn (fun z : P × (V × N) ↦ F z.1 z.2) S)
    (hD : ContinuousOn D S) (hd : ∀ z ∈ S, HasFDerivAt (F z.1) (D z) z.2)
    (hinj : InjOn (fun v ↦ F p₀ (v,0)) C)
    (hinvert : ∀ v ∈ C, (D (p₀,(v,0))).IsInvertible) :
    ∃ U ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ U,
      ∃ e : OpenPartialHomeomorph (V × N) E,
        (e : V × N → E) = F p ∧ e.source = interior C ×ˢ ball (0 : N) ε ∧
        e.target = F p '' (interior C ×ˢ ball (0 : N) ε) ∧
        ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
        ∀ z ∈ e.source, (p,z) ∈ S := by
  obtain ⟨U,hU,ε,hε,hall⟩ := compact_parametric_c1_tube_regular_g18
    F D S hS p₀ C hC hmem hF hD hd hinj hinvert
  refine ⟨U,hU,ε,hε,?_⟩
  intro p hp
  let B := interior C ×ˢ ball (0 : N) ε
  have hB : IsOpen B := isOpen_interior.prod isOpen_ball
  have hsub : B ⊆ C ×ˢ ball (0 : N) ε := prod_mono interior_subset (Subset.refl _)
  have hguard z (hz : z ∈ B) := ((hall p hp).2 z (hsub hz)).1
  have hdc : ContinuousOn (fun z : V × N ↦ fderiv ℝ (F p) z) B := by
    apply (hD.comp (continuous_const.prodMk continuous_id).continuousOn hguard).congr
    intro z hz
    exact (hd (p,z) (hguard z hz)).fderiv
  have hsm : ContDiffOn ℝ 1 (F p) B := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp,contDiffOn_succ_iff_fderiv_of_isOpen hB]
    refine ⟨fun z hz ↦ (hd (p,z) (hguard z hz)).differentiableAt.differentiableWithinAt,?_,?_⟩
    · simp
    · exact contDiffOn_zero.mpr hdc
  obtain ⟨e,hef,hes,het,hec,heic⟩ := injOn_c1_openPartialHomeomorph_g18
    (F p) B hB hsm ((hall p hp).1.mono hsub) (fun z hz ↦ by
      rw [(hd (p,z) (hguard z hz)).fderiv]
      exact ((hall p hp).2 z (hsub hz)).2)
  refine ⟨e,hef,hes,het,hec,heic,?_⟩
  intro z hz
  exact hguard z (hes ▸ hz)

end HolomorphicAnosov





