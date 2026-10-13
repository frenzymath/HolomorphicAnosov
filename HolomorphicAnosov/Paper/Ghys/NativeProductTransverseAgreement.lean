import HolomorphicAnosov.Paper.Ghys.ProjectivePlaqueCoordinatesG19

namespace HolomorphicAnosov.Ghys
universe u
open Set Filter TopologicalSpace _root_.Topology
open scoped ContDiff Manifold _root_.Topology

/-- Every point of the projective line has a holomorphic scalar chart, including infinity. -/
theorem projective_scalar_chart_at (p : ComplexProjectiveLine) :
    ∃ k : OpenPartialHomeomorph ComplexProjectiveLine ℂ,
      p ∈ k.source ∧
      ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k k.source ∧
      ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k.symm k.target := by
  let b := chartAt (ComplexModel 1) p
  let k := b.trans canonicalPlaneCoordinate
  have hk : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k k.source :=
    canonicalPlaneCoordinate_properties.2.1.1.comp
      ((contMDiffOn_chart (I := complexModel 1) (x := p)).mono Set.inter_subset_left)
      (fun z hz ↦ hz.2)
  have hki : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k.symm k.target :=
    (contMDiffOn_chart_symm (I := complexModel 1) (x := p)).comp
      (canonicalPlaneCoordinate_properties.2.1.2.mono Set.inter_subset_left)
      (fun z hz ↦ hz.2)
  exact ⟨k,⟨mem_chart_source _ p,canonicalPlaneCoordinate_properties.1 (b p)⟩,hk,hki⟩

/-- The projective chart on a native unstable plaque agrees exactly with the ambient transverse coordinate. -/
theorem transverseProjectiveChart_plaque_values
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F)
    (c : TransverseProjectiveChart F C)
    (z : FoliationCoordinateDisk s) (hz : z ∈ c.stableDomain) :
    letI := F.unstableTopology (F.unstableLabel c.box z)
    letI := C.charts (F.unstableLabel c.box z)
    ∃ e : OpenPartialHomeomorph
        (IntrinsicFoliationLeaf F.unstablePartition (F.unstableLabel c.box z))
        ComplexProjectiveLine,
      e.source = {p | ∃ w : FoliationCoordinateDisk 2, w ∈ c.coordinate.source ∧
        p.val = ((F.box c.box).chart (z,w)).val} ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target ∧
      ∀ p ∈ e.source, e p = c.transverseCoordinate F C p.val := by
  let := F.unstableTopology (F.unstableLabel c.box z)
  let := C.charts (F.unstableLabel c.box z)
  obtain ⟨e,hs,ht,hval,he,hei⟩ := c.holomorphic_on_plaque z hz
  refine ⟨e,hs,he,hei,?_⟩
  intro p hp
  rw [hs] at hp
  obtain ⟨w,hw,hp⟩ := hp
  have heq : p = ⟨((F.box c.box).chart (z,w)).val,F.unstable_label c.box z w⟩ :=
    Subtype.ext hp
  rw [heq,hval w hw,transverseCoordinate_on_box]

/-- A native product with constant stable labels admits a neighborhood where a transverse projective coordinate is independent of the stable factor. (HPS, §7; Ghys, §4) -/
theorem nativeProduct_transverse_constant_on_rectangle
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F)
    (hsep : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
    {P T : Type*} [TopologicalSpace P] [TopologicalSpace T] [LocallyConnectedSpace T]
    (O : Opens M) (Ψ : (P × T) ≃ₜ O)
    (c : TransverseProjectiveChart F C) (u₀ : P) (s₀ : T)
    (hx : (Ψ (u₀,s₀)).val ∈ c.domain F C)
    (hleaf : ∀ u t, Quotient.mk F.stablePartition (Ψ (u,t)).val =
      Quotient.mk F.stablePartition (Ψ (u,s₀)).val) :
    ∃ (V : Opens P) (W : Opens T), u₀ ∈ V ∧ s₀ ∈ W ∧
      (∀ u ∈ V, ∀ t ∈ W, (Ψ (u,t)).val ∈ c.domain F C) ∧
      ∀ u ∈ V, ∀ t ∈ W,
        c.transverseCoordinate F C (Ψ (u,t)).val =
          c.transverseCoordinate F C (Ψ (u,s₀)).val := by
  classical
  have hΨ : Continuous (fun p : P × T ↦ (Ψ p).val) :=
    continuous_subtype_val.comp Ψ.continuous
  have hn := ((c.isOpen_domain F C).preimage hΨ).mem_nhds hx
  obtain ⟨V₀,hV₀,W₀,hW₀,hprod⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨V,hVV,hVo,hu⟩ := mem_nhds_iff.mp hV₀
  obtain ⟨W,hWW,hWo,ht,hWc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance s₀ W₀ hW₀
  have hi : ∀ u ∈ V, ∀ t ∈ W, (Ψ (u,t)).val ∈ c.domain F C :=
    fun u hu t ht ↦ hprod ⟨hVV hu,hWW ht⟩
  refine ⟨⟨V,hVo⟩,⟨W,hWo⟩,hu,ht,hi,?_⟩
  intro u hu t ht'
  have hin : ∀ t : W, (Ψ (u,t.val)).val ∈ (F.box c.box).image :=
    fun t ↦ (hi u hu t.val t.property).choose
  let coords : W → FoliationCoordinateDisk s × FoliationCoordinateDisk 2 :=
    fun t ↦ (F.box c.box).chart.symm ⟨(Ψ (u,t.val)).val,hin t⟩
  have hc : Continuous coords := (F.box c.box).chart.symm.continuous.comp
    ((hΨ.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _)
  let q := Quotient.mk F.stablePartition (Ψ (u,s₀)).val
  have hl (t : W) : F.stableLabel c.box (coords t).2 = q := by
    have he : ((F.box c.box).chart (coords t)).val = (Ψ (u,t.val)).val :=
      congrArg Subtype.val ((F.box c.box).chart.apply_symm_apply _)
    rw [← F.stable_label c.box (coords t).1 (coords t).2,he]
    exact hleaf u t.val
  have hr : range (fun t : W ↦ (coords t).2) ⊆
      {w | F.stableLabel c.box w = q} := by
    rintro _ ⟨t,rfl⟩
    exact hl t
  let : PreconnectedSpace W := isPreconnected_iff_preconnectedSpace.mp hWc.isPreconnected
  have he := (stable_plaque_label_fiber_countable_g9 F c.box q (hsep q)).isTotallyDisconnected
    _ hr (isPreconnected_range hc.snd) (mem_range_self (⟨t,ht'⟩ : W))
      (mem_range_self (⟨s₀,ht⟩ : W))
  simp only [TransverseProjectiveChart.transverseCoordinate,
    dite_eq_left (hin ⟨t,ht'⟩),dite_eq_left (hin ⟨s₀,ht⟩)]
  exact congrArg c.coordinate he

/-- Agreement of a slice-constant coordinate with a transverse coordinate on the central curve extends to an ambient neighborhood. (Ghys, §4) -/
theorem nativeProduct_transverse_agreement_neighborhood
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F)
    (hsep : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
    {P T : Type*} [TopologicalSpace P] [TopologicalSpace T] [LocallyConnectedSpace T]
    (O : Opens M) (Ψ : (P × T) ≃ₜ O)
    (c : TransverseProjectiveChart F C) (u₀ : P) (s₀ : T)
    (hx : (Ψ (u₀,s₀)).val ∈ c.domain F C)
    (hleaf : ∀ u t, Quotient.mk F.stablePartition (Ψ (u,t)).val =
      Quotient.mk F.stablePartition (Ψ (u,s₀)).val)
    (g : M → ComplexProjectiveLine)
    (hg : ∀ u t, g (Ψ (u,t)).val = g (Ψ (u,s₀)).val)
    (hcentral : ∀ᶠ u in 𝓝 u₀,
      g (Ψ (u,s₀)).val = c.transverseCoordinate F C (Ψ (u,s₀)).val) :
    ∃ N : Opens M, (Ψ (u₀,s₀)).val ∈ N ∧ N ≤ O ∧
      (N : Set M) ⊆ c.domain F C ∧
      ∀ y ∈ N, g y = c.transverseCoordinate F C y := by
  obtain ⟨V,W,hu,ht,hi,he⟩ :=
    nativeProduct_transverse_constant_on_rectangle F C hsep O Ψ c u₀ s₀ hx hleaf
  have hbox : IsOpenEmbedding (fun p : P × T ↦ (Ψ p).val) :=
    O.isOpen.isOpenEmbedding_subtypeVal.comp Ψ.isOpenEmbedding
  have hagree : ∀ᶠ y in 𝓝 (Ψ (u₀,s₀)).val,
      y ∈ O ∧ y ∈ c.domain F C ∧ g y = c.transverseCoordinate F C y := by
    rw [← hbox.map_nhds_eq (u₀,s₀)]
    change ∀ᶠ p : P × T in 𝓝 (u₀,s₀),
      (Ψ p).val ∈ O ∧ (Ψ p).val ∈ c.domain F C ∧
        g (Ψ p).val = c.transverseCoordinate F C (Ψ p).val
    have hV : ∀ᶠ p : P × T in 𝓝 (u₀,s₀), p.1 ∈ V :=
      continuousAt_fst.eventually (V.isOpen.mem_nhds hu)
    have hW : ∀ᶠ p : P × T in 𝓝 (u₀,s₀), p.2 ∈ W :=
      continuousAt_snd.eventually (W.isOpen.mem_nhds ht)
    have hG : ∀ᶠ p : P × T in 𝓝 (u₀,s₀),
        g (Ψ (p.1,s₀)).val = c.transverseCoordinate F C (Ψ (p.1,s₀)).val :=
      (show ContinuousAt Prod.fst (u₀,s₀) from continuousAt_fst).eventually hcentral
    filter_upwards [hV,hW,hG] with p hpV hpW hpG
    exact ⟨(Ψ p).property,hi p.1 hpV p.2 hpW,
      (hg p.1 p.2).trans (hpG.trans (he p.1 hpV p.2 hpW).symm)⟩
  obtain ⟨N,hN,hNo,hxN⟩ := mem_nhds_iff.mp hagree
  exact ⟨⟨N,hNo⟩,hxN,(fun y hy ↦ (hN hy).1),
    (fun y hy ↦ (hN hy).2.1),(fun y hy ↦ (hN hy).2.2)⟩

/-- The scalar first integral in its projective target chart agrees with the supplied transverse atlas on an ambient neighborhood. -/
theorem nativeProduct_scalar_transverse_agreement
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F)
    (hsep : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
    {P T : Type*} [TopologicalSpace P] [TopologicalSpace T] [LocallyConnectedSpace T]
    (O : Opens M) (Ψ : (P × T) ≃ₜ O)
    (c : TransverseProjectiveChart F C) (u₀ : P) (s₀ : T)
    (hx : (Ψ (u₀,s₀)).val ∈ c.domain F C)
    (hleaf : ∀ u t, Quotient.mk F.stablePartition (Ψ (u,t)).val =
      Quotient.mk F.stablePartition (Ψ (u,s₀)).val)
    (q : M → ℂ) (a : OpenPartialHomeomorph P ℂ)
    (k : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
    (ha : u₀ ∈ a.source)
    (hq : ∀ u t, q (Ψ (u,t)).val = a u)
    (hcentral : ∀ u ∈ a.source,
      k.symm (a u) = c.transverseCoordinate F C (Ψ (u,s₀)).val)
    (W : Opens M) (hxW : (Ψ (u₀,s₀)).val ∈ W) :
    ∃ N : Opens M, (Ψ (u₀,s₀)).val ∈ N ∧ N ≤ W ∧ N ≤ O ∧
      (N : Set M) ⊆ c.domain F C ∧
      ∀ y ∈ N, k.symm (q y) = c.transverseCoordinate F C y := by
  have hg : ∀ u t, k.symm (q (Ψ (u,t)).val) = k.symm (q (Ψ (u,s₀)).val) := by
    intro u t
    rw [hq,hq]
  have he : ∀ᶠ u in 𝓝 u₀,
      k.symm (q (Ψ (u,s₀)).val) = c.transverseCoordinate F C (Ψ (u,s₀)).val := by
    filter_upwards [a.open_source.mem_nhds ha] with u hu
    rw [hq]
    exact hcentral u hu
  obtain ⟨N,hxN,hNO,hNc,hNval⟩ :=
    nativeProduct_transverse_agreement_neighborhood F C hsep O Ψ c u₀ s₀ hx hleaf
      (fun y ↦ k.symm (q y)) hg he
  exact ⟨N ⊓ W,⟨hxN,hxW⟩,inf_le_right,inf_le_left.trans hNO,
    (fun y hy ↦ hNc hy.1),(fun y hy ↦ hNval y hy.1)⟩

end HolomorphicAnosov.Ghys




