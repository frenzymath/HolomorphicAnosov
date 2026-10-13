import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Paper.Ghys.PairedProductScalarAmbientDifferentiability
import HolomorphicAnosov.Geometry.Manifold.ComplexScalarSmoothOfDifferentiable
import HolomorphicAnosov.Paper.Ghys.PairedProductLocalScalarFirstIntegral
import HolomorphicAnosov.Dynamics.Anosov.NativeLeafScalarAnnihilation
import HolomorphicAnosov.Algebra.ComplexLineComplementKernel
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.OriginalRealKernelIdentification

namespace HolomorphicAnosov.Ghys
universe u
open scoped Manifold ContDiff _root_.Topology
attribute [local instance] complex_isManifold_real

/-- A specified scalar coordinate pulls back through a receiving biholomorphism to a holomorphic
coordinate on the receiving plaque (Ghys, §3). -/
theorem receiving_specified_scalar_chart
    {P L : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
    [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (V : TopologicalSpace.Opens L) (p : P)
    (b : Diffeomorph 𝓘(ℂ) (complexModel 1) P V ∞)
    (d : OpenPartialHomeomorph L ℂ)
    (hd : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ d d.source)
    (hdi : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ d.symm d.target) :
    ∃ c : OpenPartialHomeomorph P ℂ,
      (∀ u, c u = d (b u).val) ∧
      (∀ u, u ∈ c.source ↔ (b u).val ∈ d.source) ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source ∧
      c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  let e := V.openPartialHomeomorphSubtypeCoe ⟨b p⟩
  let c := b.toHomeomorph.toOpenPartialHomeomorph.trans (e.trans d)
  have hei : ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target := by
    intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff V e.symm e.target z).mp
    exact contMDiffWithinAt_id.congr_of_mem (fun w hw ↦ e.right_inv hw) hz
  have hc : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source := by
    exact hd.comp (contMDiff_subtype_val.comp b.contMDiff).contMDiffOn
      (fun u hu ↦ hu.2.2)
  have hci : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c.symm c.target := by
    apply b.symm.contMDiff.comp_contMDiffOn
    exact hei.comp (hdi.mono (fun z hz ↦ hz.1.1)) (fun z hz ↦ hz.1.2)
  refine ⟨c, (fun _ ↦ rfl), ?_, hc, hc.mdifferentiableOn (by simp),
    hci.mdifferentiableOn (by simp)⟩
  intro u
  simp [c, e]

/-- A leaf biholomorphism followed by a specified scalar chart restricts to a holomorphic coordinate
on the open curve factor of a product. -/
theorem restricted_receiving_scalar_chart
    {L N : Type*} [TopologicalSpace L] [ChartedSpace ℂ L]
    [TopologicalSpace N] [ChartedSpace (ComplexModel 1) N]
    (P : TopologicalSpace.Opens L) (p : P)
    (E : Diffeomorph 𝓘(ℂ) (complexModel 1) L N ∞)
    (d : OpenPartialHomeomorph N ℂ)
    (hd : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ d d.source)
    (hdi : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ d.symm d.target) :
    ∃ c : OpenPartialHomeomorph P ℂ,
      (∀ u, c u = d (E u.val)) ∧
      (∀ u, u ∈ c.source ↔ E u.val ∈ d.source) ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source ∧
      c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  let i := P.openPartialHomeomorphSubtypeCoe ⟨p⟩
  let c := i.trans (E.toHomeomorph.toOpenPartialHomeomorph.trans d)
  have hii : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ i.symm i.target := by
    intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff P i.symm i.target z).mp
    exact contMDiffWithinAt_id.congr_of_mem (fun w hw ↦ i.right_inv hw) hz
  have hc : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source := by
    exact hd.comp (E.contMDiff.comp contMDiff_subtype_val).contMDiffOn
      (fun u hu ↦ hu.2.2)
  have hci : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c.symm c.target := by
    exact hii.comp (E.symm.contMDiff.comp_contMDiffOn
      (hdi.mono (fun z hz ↦ hz.1.1))) (fun z hz ↦ hz.2)
  refine ⟨c,(fun _ ↦ rfl),?_,hc,hc.mdifferentiableOn (by simp),
    hci.mdifferentiableOn (by simp)⟩
  intro u
  simp [c,i]

/-- A specified projective coordinate on the receiving leaf gives a scalar chart whose inverse
reconstructs that projective coordinate on its source. -/
theorem restricted_projective_scalar_chart
    {L N : Type*} [TopologicalSpace L] [ChartedSpace ℂ L]
    [TopologicalSpace N] [ChartedSpace (ComplexModel 1) N]
    (P : TopologicalSpace.Opens L) (p : P)
    (E : Diffeomorph 𝓘(ℂ) (complexModel 1) L N ∞)
    (e : OpenPartialHomeomorph N ComplexProjectiveLine)
    (he : ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source)
    (hei : ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target)
    (k : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
    (hk : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k k.source)
    (hki : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k.symm k.target)
    (hp : E p.val ∈ e.source) (hpk : e (E p.val) ∈ k.source) :
    ∃ c : OpenPartialHomeomorph P ℂ,
      p ∈ c.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source ∧
      c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ∧
      ∀ u ∈ c.source, E u.val ∈ e.source ∧
        k.symm (c u) = e (E u.val) ∧ c u ∈ k.target := by
  let d := e.trans k
  have hd : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ d d.source :=
    hk.comp (he.mono Set.inter_subset_left) (fun _ h ↦ h.2)
  have hdi : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ d.symm d.target :=
    hei.comp (hki.mono Set.inter_subset_left) (fun _ h ↦ h.2)
  obtain ⟨c,hcval,hcsource,hc,hcd⟩ := restricted_receiving_scalar_chart P p E d hd hdi
  refine ⟨c,(hcsource p).mpr ⟨hp,hpk⟩,hc,hcd,?_⟩
  intro u hu
  have hu' : E u.val ∈ e.source ∧ e (E u.val) ∈ k.source := (hcsource u).mp hu
  exact ⟨hu'.1,(by rw [hcval]; exact k.left_inv hu'.2),
    (by rw [hcval]; exact k.map_source hu'.2)⟩

set_option backward.isDefEq.respectTransparency false in
/-- A specified holomorphic coordinate on the curve factor of a product extends to an ambient
holomorphic scalar whose real differential has kernel equal to the stable distribution (Ghys,
Prop. 2.2). -/
theorem pairedProduct_specified_scalar_kernel
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X] (hd : 2 ≤ d)
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin (2 * d - 2) → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (2 * d - 2) → ℝ) ∞ (Ls i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i)]
    (S : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls (fun _ ↦ 2 * d - 2))
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu (fun _ ↦ 2))
    (complexChart : ∀ i, ChartedSpace ℂ (Lu i))
    (hcomplex : ∀ i, letI := complexChart i; IsManifold 𝓘(ℂ) ∞ (Lu i))
    (hinclusion : ∀ i, letI := complexChart i;
      ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z))
    (qu : ιu) (qs : ιs) :
    letI := complexChart qu
    ∀ (Pu : TopologicalSpace.Opens (Lu qu)) (Ps : TopologicalSpace.Opens (Ls qs))
      (O : TopologicalSpace.Opens X) (Ψ : (Pu × Ps) ≃ₜ O)
      (c : OpenPartialHomeomorph Pu ℂ),
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source →
      c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) →
      (∀ s : Ps, ∃ qi : ιu, letI := complexChart qi
        ∃ (V : TopologicalSpace.Opens (Lu qi))
          (b : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Pu V ∞),
          ∀ u : Pu, (U.leaf qi).inclusion (b u).val = (Ψ (u, s)).val) →
      (∀ u : Pu, ∃ (qi : ιs) (V : TopologicalSpace.Opens (Ls qi)) (b : Ps ≃ₜ V),
        ∀ s : Ps, (S.leaf qi).inclusion (b s).val = (Ψ (u, s)).val) →
      ∃ (W : TopologicalSpace.Opens X) (q : X → ℂ), W ≤ O ∧
        (∀ u s, (Ψ (u, s)).val ∈ W ↔ u ∈ c.source) ∧
        (∀ u s, q (Ψ (u, s)).val = c u) ∧
        ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q W ∧
        ∀ y ∈ W, mfderiv (complexModel d) 𝓘(ℂ) q y ≠ 0 ∧
          ((LinearMap.ker (mfderiv (complexModel d) 𝓘(ℂ) q y).toLinearMap).restrictScalars ℝ).map
            (complexTangentToReal d y).toLinearEquiv.toLinearMap =
              a.splitting.stable.toDistribution y := by
  intro Pu Ps O Ψ c hc hcd hreceivingU hreceivingS
  classical
  let := hcomplex qu
  obtain ⟨W, q, hWO, hWslice, hqcont, hqslice, hqfiber, hqreceiving⟩ :=
    pairedProduct_local_scalar_firstIntegral.{u,u,u,u} O Ψ c hc
  have hunstableScalar (u : Pu) :
      ∃ (qi : ιs) (V : TopologicalSpace.Opens (Ls qi)) (b : Ps ≃ₜ V),
        (∀ s : Ps, (S.leaf qi).inclusion (b s).val = (Ψ (u, s)).val) ∧
        ∀ v : V, q ((S.leaf qi).inclusion v.val) = c u := by
    obtain ⟨qi, V, b, hb⟩ := hreceivingS u
    refine ⟨qi, V, b, hb, ?_⟩
    intro v
    rw [← b.apply_symm_apply v, hb, hqslice]
  have hnonzero_of_holomorphic
      (hq : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q W) :
      ∀ y ∈ W, mfderiv (complexModel d) 𝓘(ℂ) q y ≠ 0 := by
    intro y hy
    let yO : O := ⟨y, hWO hy⟩
    let u := (Ψ.symm yO).1
    let s := (Ψ.symm yO).2
    have hys : (Ψ (u, s)).val = y :=
      congrArg Subtype.val (Ψ.apply_symm_apply yO)
    have huc : u ∈ c.source := (hWslice u s).mp (hys.symm ▸ hy)
    obtain ⟨qi, hreceiving⟩ := hreceivingU s
    let := complexChart qi
    let := hcomplex qi
    obtain ⟨V, b, hb⟩ := hreceiving
    let j : Pu → X := fun v ↦ (U.leaf qi).inclusion (b v).val
    have hjy : j u = y := (hb u).trans hys
    have hqj : q ∘ j = c := by
      funext v
      change q ((U.leaf qi).inclusion (b v).val) = c v
      rw [hb, hqslice]
    have hj : ContMDiff 𝓘(ℂ) (complexModel d) ∞ j :=
      (hinclusion qi).1.comp (contMDiff_subtype_val.comp b.contMDiff)
    have hqd : MDifferentiableAt (complexModel d) 𝓘(ℂ) q (j u) := by
      rw [hjy]
      exact (hq.contMDiffAt (W.isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
    have hchain := mfderiv_comp u hqd (hj.mdifferentiable (by simp) u)
    intro hz
    have hzj : mfderiv (complexModel d) 𝓘(ℂ) q (j u) = 0 := hjy.symm ▸ hz
    rw [hqj, hzj] at hchain
    have hzero : mfderiv 𝓘(ℂ) 𝓘(ℂ) c u = 0 := by
      simpa only [ContinuousLinearMap.zero_comp] using hchain
    have hinj := hcd.mfderiv_injective huc
    have hbad : (1 : ℂ) = 0 := hinj (by rw [hzero]; rfl)
    exact one_ne_zero hbad
  have hkill_of_holomorphic
      (hq : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q W) :
      ∀ y ∈ W, ∀ v ∈ a.splitting.stable.toDistribution y,
        mfderiv (complexModel d) 𝓘(ℂ) q y
          ((complexTangentToReal d y).symm v) = 0 := by
    intro y hy
    let yO : O := ⟨y, hWO hy⟩
    let u := (Ψ.symm yO).1
    let s := (Ψ.symm yO).2
    have hys : (Ψ (u, s)).val = y :=
      congrArg Subtype.val (Ψ.apply_symm_apply yO)
    obtain ⟨qi, V, b, hb, hconst⟩ := hunstableScalar u
    have hi : (S.leaf qi).inclusion (b s).val = y := (hb s).trans hys
    have hlocal : (q ∘ (S.leaf qi).inclusion) =ᶠ[𝓝 (b s).val]
        fun _ ↦ q ((S.leaf qi).inclusion (b s).val) := by
      filter_upwards [V.isOpen.mem_nhds (b s).property] with z hz
      exact (hconst ⟨z, hz⟩).trans (hconst (b s)).symm
    have hd : MDifferentiableAt (complexModel d) 𝓘(ℂ) q
        ((S.leaf qi).inclusion (b s).val) := by
      rw [hi]
      exact (hq.contMDiffAt (W.isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
    have hk := (S.leaf qi).scalar_annihilates_of_eventually_constant q (b s).val hd hlocal
    change ∀ v ∈ a.splitting.stable.toDistribution ((S.leaf qi).inclusion (b s).val),
      mfderiv (complexModel d) 𝓘(ℂ) q ((S.leaf qi).inclusion (b s).val)
        ((complexTangentToReal d ((S.leaf qi).inclusion (b s).val)).symm v) = 0 at hk
    exact hi ▸ hk
  have hq : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q W :=
    complex_scalar_contMDiffOn_of_mdifferentiableOn W.isOpen
      (pairedProduct_scalar_ambient_mdifferentiableOn hd f a hRank S U
        complexChart hcomplex hinclusion qu qs Pu Ps O Ψ c hc
        hreceivingU hreceivingS W q hWO hWslice hqcont hqslice)
  refine ⟨W, q, hWO, hWslice, hqslice, hq, ?_⟩
  intro y hy
  have hne := hnonzero_of_holomorphic hq y hy
  have hkill := hkill_of_holomorphic hq y hy
  refine ⟨hne, ?_⟩
  obtain ⟨K, hKdim, hK⟩ := hRank y
  have hcompl : IsCompl
      ((K.restrictScalars ℝ).map (complexTangentToReal d y).toLinearEquiv.toLinearMap)
      (a.splitting.stable.toDistribution y) := by
    rw [hK]
    exact (a.splitting.isCompl y).symm
  have hne' : (mfderiv (complexModel d) 𝓘(ℂ) q y).toLinearMap ≠ 0 := by
    intro h
    apply hne
    ext v
    exact DFunLike.congr_fun h v
  have hu := complexLineComplement_scalar_injective
    (complexTangentToReal d y).toLinearEquiv K
    (a.splitting.stable.toDistribution y) hKdim hcompl
    (mfderiv (complexModel d) 𝓘(ℂ) q y).toLinearMap hne' hkill
  rw [hK] at hu
  exact originalRealKernelIdentification y _ _ (a.splitting.isCompl y).symm _ hkill hu

end HolomorphicAnosov.Ghys



