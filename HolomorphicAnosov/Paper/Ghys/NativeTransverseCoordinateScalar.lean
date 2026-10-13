import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Geometry.NativeFlowboxAffineCarrierComparison
import HolomorphicAnosov.Paper.Ghys.SurfaceAffineScalarFromProduct
import HolomorphicAnosov.Paper.Ghys.NativeProductTransverseAgreement

/-! This file scalarizes a specified native transverse projective coordinate. -/

namespace HolomorphicAnosov.Ghys
universe u
open scoped Manifold ContDiff _root_.Topology
attribute [local instance] complex_isManifold_real
set_option backward.isDefEq.respectTransparency false in
/-- A native transverse projective coordinate admits a scalar representative agreeing on an ambient neighborhood and having the original stable kernel. (Ghys, Proposition 2.2) -/
theorem native_transverse_coordinate_scalar_kernel
    {d s : ℕ} {M : Type u} [mOriginal : MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (hd : 2 ≤ d) (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (B : NativeTransverseAsymptoticIdentification.{u,u} f.toHomeomorph
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution s 2)
    (C : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F)
    (hC : letI := B.realAmbientCharts
      ∀ q : Quotient B.F.unstablePartition,
        letI := B.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) ∧
        ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) z) :
    letI := B.realAmbientCharts
    ∀ (c : TransverseProjectiveChart B.F C) (x : M), x ∈ c.domain B.F C →
    ∃ (k : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
      (q : M → ℂ) (N : TopologicalSpace.Opens M),
      x ∈ N ∧ (N : Set M) ⊆ c.domain B.F C ∧
      ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k k.source ∧
      ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k.symm k.target ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q N ∧
      (∀ y ∈ N, q y ∈ k.target ∧ k.symm (q y) = c.transverseCoordinate B.F C y) ∧
      ∀ y ∈ N, mfderiv (complexModel d) 𝓘(ℂ) q y ≠ 0 ∧
        ((LinearMap.ker (mfderiv (complexModel d) 𝓘(ℂ) q y).toLinearMap).restrictScalars ℝ).map
          (complexTangentToReal d y).toLinearEquiv.toLinearMap =
            a.splitting.stable.toDistribution y := by
  intro c x hx
  classical
  let := B.realAmbientCharts
  obtain ⟨ιs,ιu,Ls,Lu,topS,topU,hboxes⟩ :=
    ActualInvariantSectionFlowboxCoverG5.actual_invariant_section_flowbox_cover f a hRank
  let := topS
  let := topU
  obtain ⟨chartS,chartU,hboxes⟩ := hboxes
  let := chartS
  let := chartU
  obtain ⟨smoothS,smoothU,hboxes⟩ := hboxes
  let := smoothS
  let := smoothU
  obtain ⟨S,U,complexChart,hcomplex,hinclusion,hasymptotic,
    hinvariantS,hinvariantU,hlamination,hatlas,hproducts⟩ := hboxes
  obtain ⟨qu,qs,hprod⟩ := hproducts x
  let := complexChart qu
  let := hcomplex qu
  obtain ⟨Pu,Ps,hconnectedU,hconnectedS,u₀,s₀,O,Ψ,
    hu₀,hs₀,hcenter,hsliceU,hsliceS,πu,πs,hprojections,
    hprojection_inverse,hintersection,hreceivingU,hreceivingS,hdimOne⟩ := hprod
  obtain ⟨mG,hmetric,hrS,hrU⟩ := hasymptotic
  let : MetricSpace M := mOriginal
  have hrange : Set.range (U.leaf qu).inclusion =
      {y | ForwardAsymptotic f.toHomeomorph.symm x y} := by
    ext y
    rw [Set.mem_range,hrU qu u₀.val y,hu₀]
    exact native_flowbox_asymptotic_metric_iff mG hmetric f.symm x y
  have HE := native_flowbox_curve_fixed_carrier_biholomorph B C hC
    (U.leaf qu).inclusion (hinclusion qu).1 (U.leaf qu).injective
    (hinclusion qu).2 x hrange
  have hx0 := hx
  obtain ⟨hxbox,hxz,hxw⟩ := hx
  let zw := (B.F.box c.box).chart.symm ⟨x,hxbox⟩
  have hpoint : ((B.F.box c.box).chart zw).val = x :=
    congrArg Subtype.val ((B.F.box c.box).chart.apply_symm_apply _)
  have hlabel : Quotient.mk B.F.unstablePartition x = B.F.unstableLabel c.box zw.1 := by
    rw [← hpoint]
    exact B.F.unstable_label c.box zw.1 zw.2
  let := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
  let := C.charts (Quotient.mk B.F.unstablePartition x)
  obtain ⟨E,hE⟩ := HE
  have Hplaque := transverseProjectiveChart_plaque_values B.F C c zw.1 hxz
  rw [← hlabel] at Hplaque
  obtain ⟨e,hesource,he,hei,heval⟩ := Hplaque
  have hep : E u₀.val ∈ e.source := by
    rw [hesource]
    exact ⟨zw.2,hxw,(hE u₀.val).trans (hu₀.trans hpoint.symm)⟩
  obtain ⟨k,hpk,hk,hki⟩ := projective_scalar_chart_at (e (E u₀.val))
  obtain ⟨cc,hccp,hcc,hccd,hccval⟩ :=
    restricted_projective_scalar_chart Pu u₀ E e he hei k hk hki hep hpk
  obtain ⟨W,q,hWO,hWslice,hqslice,hq,hker⟩ :=
    pairedProduct_specified_scalar_kernel hd f a hRank S U complexChart hcomplex
      hinclusion qu qs Pu Ps O Ψ cc hcc hccd hreceivingU hreceivingS
  have hxW : (Ψ (u₀,s₀)).val ∈ W := (hWslice u₀ s₀).mpr hccp
  have hcentral : ∀ u ∈ cc.source,
      k.symm (cc u) = c.transverseCoordinate B.F C (Ψ (u,s₀)).val := by
    intro u hu
    rw [(hccval u hu).2.1,heval _ (hccval u hu).1,hE,hsliceU]
  have hleaf : ∀ u t, Quotient.mk B.F.stablePartition (Ψ (u,t)).val =
      Quotient.mk B.F.stablePartition (Ψ (u,s₀)).val := by
    intro u t
    obtain ⟨qi,V,b,hb⟩ := hreceivingS u
    have ha : ForwardAsymptotic f.toHomeomorph (Ψ (u,t)).val (Ψ (u,s₀)).val := by
      rw [← hb t,← hb s₀]
      apply (native_flowbox_asymptotic_metric_iff mG hmetric f _ _).mp
      exact (hrS qi (b t).val _).mp ⟨(b s₀).val,rfl⟩
    exact Quotient.sound
      ((native_identification_stable_partition_iff_asymptotic B _ _).mpr ha)
  have hsep : ∀ r : Quotient B.F.stablePartition,
      letI := B.F.stableTopology r
      TopologicalSpace.SeparableSpace (IntrinsicFoliationLeaf B.F.stablePartition r) := by
    intro r
    obtain ⟨y,rfl⟩ := Quotient.exists_rep r
    let := B.stableTopology y
    let := (B.nativeS y).secondCountable
    let := (B.stableClassHomeomorph y).secondCountableTopology
    infer_instance
  let : LocallyConnectedSpace Ps := ChartedSpace.locallyConnectedSpace (Fin (2*d-2) → ℝ) Ps
  obtain ⟨N,hxN,hNW,hNO,hNc,hNval⟩ :=
    nativeProduct_scalar_transverse_agreement B.F C hsep O Ψ c u₀ s₀
      (hcenter.symm ▸ hx0) hleaf q cc k hccp hqslice hcentral W hxW
  have htarget : ∀ y ∈ W, q y ∈ k.target := by
    intro y hy
    let yo : O := ⟨y,hWO hy⟩
    let uv := Ψ.symm yo
    have hey : (Ψ uv).val = y := congrArg Subtype.val (Ψ.apply_symm_apply yo)
    have huv : uv.1 ∈ cc.source := (hWslice uv.1 uv.2).mp (hey.symm ▸ hy)
    rw [← hey,hqslice]
    exact (hccval uv.1 huv).2.2
  refine ⟨k,q,N,hcenter ▸ hxN,hNc,hk,hki,hq.mono hNW,?_,?_⟩
  · intro y hy
    exact ⟨htarget y (hNW hy),hNval y hy⟩
  · intro y hy
    exact hker y (hNW hy)


end HolomorphicAnosov.Ghys

