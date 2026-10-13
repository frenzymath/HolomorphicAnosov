import HolomorphicAnosov.Paper.Ghys.PairedProductScalarAmbientDifferentiability
import HolomorphicAnosov.Geometry.Manifold.ComplexScalarSmoothOfDifferentiable
import HolomorphicAnosov.Paper.Ghys.PairedProductLocalScalarFirstIntegral
import HolomorphicAnosov.Dynamics.Anosov.NativeLeafScalarAnnihilation
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseAnosovDatum
import HolomorphicAnosov.Algebra.ComplexLineComplementKernel
import HolomorphicAnosov.Geometry.NativePlaqueProjectionControl
import HolomorphicAnosov.Linear.RankOneKernelFrame
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicDirectionalDerivative
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicKernelFrameOn
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ExistsNativeHolomorphicFrame
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.LocalHolomorphicSubmersionKernel
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicSubbundleOfLocalSubmersions
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.OriginalRealKernelIdentification
import HolomorphicAnosov.Paper.Zhang.OriginalUnstableHolomorphicOfLocalSubmersions
import HolomorphicAnosov.Analysis.Complex.ComplexLinearDifferentialOfSplitting
import HolomorphicAnosov.Analysis.Complex.ComplexDerivativeOfRealSplitting
import HolomorphicAnosov.Analysis.Complex.HolomorphicSubmersionOfRealSplitting
import HolomorphicAnosov.Analysis.BoundedContinuousInvariantSections
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularity
import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle

/-!
This file establishes holomorphicity of the unstable tangent subbundle when the
stable bundle has complex rank one. (Zhang, pp.3–4; Ghys, Prop. 2.2, pp.589–590
and surface remark, p.590)
-/

namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff _root_.Topology

attribute [local instance] complex_isManifold_real

set_option backward.isDefEq.respectTransparency false in
/-- For a compact holomorphic Anosov manifold of complex dimension `d ≥ 2`, a
rank-one stable bundle implies that the unstable distribution is the realification of a
rank-`d - 1` holomorphic tangent subbundle. (Zhang, pp.3–4; Ghys, Prop. 2.2, pp.589–590
and surface remark, p.590) -/
theorem rank_one_stable_holomorphic_unstable {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (hd : 2 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution) :
    ∃ P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x),
      IsHolomorphicTangentSubbundle (d - 1) P ∧
        ∀ x : X, ((P x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap =
            a.splitting.unstable.toDistribution x := by
  classical
  cases d with
  | zero => omega
  | succ n =>
    let ainv : AnosovDatum f.symm := TheoremAProof.inverseAnosovDatum f a
    have hRankInv : HasComplexRankOne ainv.splitting.unstable.toDistribution := hstable
    have hboxes := Ghys.ActualInvariantSectionFlowboxCoverG5.actual_invariant_section_flowbox_cover
      f.symm ainv hRankInv
    apply originalUnstableHolomorphicOfLocalSubmersions f a
    intro x
    obtain ⟨ιs, ιu, Ls, Lu, topS, topU, hboxes⟩ := hboxes
    let := topS
    let := topU
    obtain ⟨chartS, chartU, hboxes⟩ := hboxes
    let := chartS
    let := chartU
    obtain ⟨smoothS, smoothU, hboxes⟩ := hboxes
    let := smoothS
    let := smoothU
    obtain ⟨S, U, complexChart, hcomplex, hinclusion, hasymptotic,
      hinvariantS, hinvariantU, hlamination, hatlas, hpaired⟩ := hboxes
    obtain ⟨qu, qs, hpaired⟩ := hpaired x
    let := complexChart qu
    let := hcomplex qu
    obtain ⟨Pu, Ps, hconnectedU, hconnectedS, u₀, s₀, O, Ψ,
      hu₀, hs₀, hcenter, hsliceU, hsliceS, πu, πs, hprojections,
      hprojection_inverse, hintersection, hreceivingU, hreceivingS, hdimOne⟩ := hpaired
    have hxO : x ∈ O := hcenter ▸ (Ψ (u₀, s₀)).property
    let c := chartAt ℂ u₀
    obtain ⟨W, q, hWO, hWslice, hqcont, hqslice, hqfiber, hqreceiving⟩ :=
      Ghys.pairedProduct_local_scalar_firstIntegral O Ψ c
        (contMDiffOn_chart (I := 𝓘(ℂ)) (x := u₀))
    have hxW : x ∈ W := by
      rw [← hcenter, hWslice]
      exact mem_chart_source ℂ u₀
    have hstableScalar (s : Ps) :
        ∃ qi : ιu, letI := complexChart qi
        ∃ (V : TopologicalSpace.Opens (Lu qi))
          (b : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Pu V ∞),
          (∀ u : Pu, (U.leaf qi).inclusion (b u).val = (Ψ (u, s)).val) ∧
          ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞
            (fun v : V ↦ q ((U.leaf qi).inclusion v.val)) (b.symm ⁻¹' c.source) ∧
          Set.InjOn (fun v : V ↦ q ((U.leaf qi).inclusion v.val))
            (b.symm ⁻¹' c.source) := by
      obtain ⟨qi, hreceiving⟩ := hreceivingU s
      let := complexChart qi
      obtain ⟨V, b, hb⟩ := hreceiving
      exact ⟨qi, V, b, hb, hqreceiving (fun v : V ↦ (U.leaf qi).inclusion v.val) s b hb⟩
    have hunstableScalar (u : Pu) :
        ∃ (qi : ιs) (V : TopologicalSpace.Opens (Ls qi)) (b : Ps ≃ₜ V),
          (∀ s : Ps, (S.leaf qi).inclusion (b s).val = (Ψ (u, s)).val) ∧
          ∀ v : V, q ((S.leaf qi).inclusion v.val) = c u := by
      obtain ⟨qi, V, b, hb⟩ := hreceivingS u
      refine ⟨qi, V, b, hb, ?_⟩
      intro v
      rw [← b.apply_symm_apply v, hb, hqslice]
    have hnonzero_of_holomorphic
        (hq : ContMDiffOn (complexModel (n + 1)) 𝓘(ℂ) ∞ q W) :
        ∀ y ∈ W, mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y ≠ 0 := by
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
      have hj : ContMDiff 𝓘(ℂ) (complexModel (n + 1)) ∞ j :=
        (hinclusion qi).1.comp (contMDiff_subtype_val.comp b.contMDiff)
      have hqd : MDifferentiableAt (complexModel (n + 1)) 𝓘(ℂ) q (j u) := by
        rw [hjy]
        exact (hq.contMDiffAt (W.isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
      have hchain := mfderiv_comp u hqd (hj.mdifferentiable (by simp) u)
      intro hz
      have hzj : mfderiv (complexModel (n + 1)) 𝓘(ℂ) q (j u) = 0 := hjy.symm ▸ hz
      rw [hqj, hzj] at hchain
      have hzero : mfderiv 𝓘(ℂ) 𝓘(ℂ) c u = 0 := by
        simpa only [ContinuousLinearMap.zero_comp] using hchain
      have hinj := (mdifferentiable_chart (I := 𝓘(ℂ)) u₀).mfderiv_injective huc
      have hbad : (1 : ℂ) = 0 := hinj (by rw [hzero]; rfl)
      exact one_ne_zero hbad
    have hkill_of_holomorphic
        (hq : ContMDiffOn (complexModel (n + 1)) 𝓘(ℂ) ∞ q W) :
        ∀ y ∈ W, ∀ v ∈ a.splitting.unstable.toDistribution y,
          mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y
            ((complexTangentToReal (n + 1) y).symm v) = 0 := by
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
      have hd : MDifferentiableAt (complexModel (n + 1)) 𝓘(ℂ) q
          ((S.leaf qi).inclusion (b s).val) := by
        rw [hi]
        exact (hq.contMDiffAt (W.isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
      have hk := (S.leaf qi).scalar_annihilates_of_eventually_constant q (b s).val hd hlocal
      change ∀ v ∈ a.splitting.unstable.toDistribution ((S.leaf qi).inclusion (b s).val),
        mfderiv (complexModel (n + 1)) 𝓘(ℂ) q ((S.leaf qi).inclusion (b s).val)
          ((complexTangentToReal (n + 1) ((S.leaf qi).inclusion (b s).val)).symm v) = 0 at hk
      exact hi ▸ hk
    suffices hq : ContMDiffOn (complexModel (n + 1)) 𝓘(ℂ) ∞ q W by
      refine ⟨W, q, W.isOpen, hxW, hq, hnonzero_of_holomorphic hq x hxW, ?_⟩
      intro y hy
      have hkill := hkill_of_holomorphic hq y hy
      refine ⟨hkill, ?_⟩
      obtain ⟨K, hKdim, hK⟩ := hstable y
      have hcompl : IsCompl
          ((K.restrictScalars ℝ).map (complexTangentToReal (n + 1) y).toLinearEquiv.toLinearMap)
          (a.splitting.unstable.toDistribution y) := by
        rw [hK]
        exact a.splitting.isCompl y
      have hne : (mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y).toLinearMap ≠ 0 := by
        intro h
        apply hnonzero_of_holomorphic hq y hy
        ext v
        exact DFunLike.congr_fun h v
      have hs := complexLineComplement_scalar_injective
        (complexTangentToReal (n + 1) y).toLinearEquiv K
        (a.splitting.unstable.toDistribution y) hKdim hcompl
        (mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y).toLinearMap hne hkill
      rw [hK] at hs
      exact hs
    apply complex_scalar_contMDiffOn_of_mdifferentiableOn W.isOpen
    exact Ghys.pairedProduct_scalar_ambient_mdifferentiableOn hd f.symm ainv hRankInv
      S U complexChart hcomplex hinclusion qu qs Pu Ps O Ψ c
      (contMDiffOn_chart (I := 𝓘(ℂ)) (x := u₀)) hreceivingU hreceivingS
      W q hWO hWslice hqcont hqslice

end HolomorphicAnosov

