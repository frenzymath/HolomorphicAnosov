import HolomorphicAnosov.Geometry.IntrinsicPiecewiseC1PathReversal
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import HolomorphicAnosov.Geometry.HolomorphicCoordinateOrientationG18
import HolomorphicAnosov.Geometry.NativeUnstableIntrinsicContractionG18
import HolomorphicAnosov.Geometry.NativePlaqueTubeDerivativeG18
import HolomorphicAnosov.Analysis.UniqueSmallSelectionG18
import HolomorphicAnosov.Paper.Ghys.NativeUnstableIterateHolomorphic
import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18
import HolomorphicAnosov.Paper.Ghys.Blocks.TubePhysicalNormalBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.TubeReconstructionBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.TubeImageCenterBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.TubeAtZeroBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.SmallTubeBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.TubeOriginalNormalSizeBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.NativeNormalUniquenessBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.TubePhysicalReconstructionBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.SmallPhysicalTubeBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.NativeMetricBoundsBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.NativeMetricLowerBoundsBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.NativeLiftBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.NativeChartBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.NativeConfinementBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.GlobalNormalUniquenessBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.NativeRadialBoundBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.UniformPathBlock

import HolomorphicAnosov.Paper.Ghys.Blocks.NativeControlBlock
import HolomorphicAnosov.Paper.Ghys.Blocks.ExpandedControlBlock

open Manifold MeasureTheory TopologicalSpace
open scoped Manifold

namespace HolomorphicAnosov.Ghys
noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff
open scoped Bundle
universe u
section OriginalStatement

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]

attribute [local instance] complex_isManifold_real

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- A holomorphic diffeomorphism on a nonempty compact manifold with a complex-rank-one
unstable distribution and Hermitian Anosov estimates has intrinsic leaves satisfying the
expanding plaque comparison property. (Ghys, Prop. 2.2, pp.588–590) -/
theorem rank_one_expanding_plaque_comparisons
    (f : Biholomorph d d M M) (hmetric : HermitianTangentMetricCore d M)
    (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric)
    (S : InvariantRealTangentSplitting f.toReal)
    (hAnosov : HermitianAllTimeAnosov f hmetric S)
    (hRank : HasComplexRankOne S.unstable.toDistribution) :
    letI : MetricSpace M := rankComparisonMetric (d := d)
    Nonempty M → ∃ L : RankOneNativeLeaves f S, L.ComparisonProperty hmetric := by
  classical
  let : MetricSpace M := rankComparisonMetric (d := d)
  intro hM
  let realManifold : IsManifold (realModel d) ∞ M := complex_isManifold_real d M
  let originalAmbientMetric : MetricSpace M := inferInstance
  let g := StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth
  have hb := hermitian_tensor_bounds_g18 f hmetric hmetric_smooth S hAnosov
  obtain ⟨a,ha,hag⟩ := anosovDatum_of_tensorBounds_g18 f S g hb
  subst S
  obtain ⟨hS,hU⟩ := HPS.anosov_global_lamination_tensor_metric f.toReal a.splitting g hb
  obtain ⟨ιs,Ls,rs,ts,cs,ss,Fs,boxesS,invS,familiesS,coherentS,extraS⟩ := hS
  obtain ⟨ιu,Lu,ru,tu,cu,su,Fu,boxesU,invU,familiesU,coherentU,extraU⟩ := hU
  let nativeNorm (p : M) : NormedAddCommGroup (Fin (coherentU.dimension 2 p) → ℝ) :=
    inferInstance
  let nativeSpace (p : M) : NormedSpace ℝ (Fin (coherentU.dimension 2 p) → ℝ) :=
    inferInstance
  let nativeFinite (p : M) : FiniteDimensional ℝ (Fin (coherentU.dimension 2 p) → ℝ) :=
    inferInstance
  obtain ⟨L⟩ := exists_rank_one_native_leaves_g18 f hmetric hmetric_smooth
    a.splitting hAnosov hRank hM
  let nativeTopology (p : M) : TopologicalSpace
      (UnstableAsymptoticLeaf f.toHomeomorph p) :=
    L.identification.unstableTopology p
  let nativeCharts (p : M) : ChartedSpace (Fin (L.unstable p).rank → ℝ)
      (UnstableAsymptoticLeaf f.toHomeomorph p) :=
    L.identification.unstableCharts p
  let nativeIterate (k : ℕ) (x : M) :
      let := nativeTopology x
      let := nativeCharts x
      let := nativeTopology ((f^[k]) x)
      let := nativeCharts ((f^[k]) x)
      Diffeomorph (L.uModel x) (L.uModel ((f^[k]) x))
        (L.U x) (L.U ((f^[k]) x)) ∞ := L.iterateUnstable k x
  obtain ⟨labelU,discU,mapU,stagesU,⟨AU,hAUlabel⟩,hfamilyU,hcoherentU⟩ := extraU
  have hNativeUnstableAsymptotic (p : M) (q : (coherentU.family 2 p).family.centerDomain)
      (v : Fin (coherentU.dimension 2 p) → ℝ)
      (hv : v ∈ Metric.ball 0 (coherentU.family 2 p).family.radius) :
      ForwardAsymptotic (f.symm : M → M) q.val
        (((coherentU.family 2 p).family.plaque q).param v) := by
    let Φ := coherentU.family 2 p
    let v₀ : Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ) Φ.family.radius :=
      ⟨0,Metric.mem_ball_self Φ.family.radius_pos⟩
    have hrange := AU.range_eq_forwardAsymptotic (Φ.label q) (Φ.chart q v₀).val
    have hcenter : (Fu.leaf (Φ.label q)).inclusion (Φ.chart q v₀).val = q.val :=
      (Φ.factorization q v₀).symm.trans (Φ.family.plaque q).centered
    rw [hcenter] at hrange
    have hmem : (Φ.family.plaque q).param v ∈ Set.range (Fu.leaf (Φ.label q)).inclusion :=
      ⟨(Φ.chart q ⟨v,hv⟩).val,(Φ.factorization q ⟨v,hv⟩).symm⟩
    rw [hrange] at hmem
    exact hmem
  have hNativeTubes (p : M) := (coherentU.coherence 2 p).original_exponential_normal_tube_g18
    (by omega) g ⟨p,(coherentU.family 2 p).family.center_mem⟩
  choose tubeDomain hTubeDomain hTubeDomainCenter hTubeGuard
    tubeLabels hTubeLabel tubeImage hTubeImage hTubeImagePoint
    tubeInverse hTubeInverse hTubeInverseContinuous hTubeDerivativeContinuous
    hTubeZeroSource hTubeOpenSource using hNativeTubes
  have hNativeCoefficientData (p : M) :=
    (coherentU.coherence 2 p).original_normal_coefficients_locally_bounded_g18 g
      ⟨p,(coherentU.family 2 p).family.center_mem⟩
  choose coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius
    coefficientBound hCoefficientBound hCoefficient using hNativeCoefficientData
  have hNativeUniformTubes (p : M) :=
    (coherentU.coherence 2 p).original_exponential_normal_uniform_tube_g18
      (by omega) g ⟨p,(coherentU.family 2 p).family.center_mem⟩
  choose fixedTubeDomain hFixedTubeDomain hFixedTubeCenter hFixedTubeGuard
    fixedTubeRadius hFixedTubeRadius fixedTubeLabels hFixedTubeLabels
    fixedNormalRadius hFixedNormalRadius hFixedTube using hNativeUniformTubes
  let tubeChart (p : M) := extChartAt (realModel d) (coherentU.family 2 p).family.receivingAnchor
  let tubeTr (p : M) := trivializationAt (ComplexModel d) (TangentSpace (realModel d))
    (coherentU.family 2 p).family.receivingAnchor
  let tubeTangentChart (p : M) := extChartAt (realModel d).tangent
    (⟨(coherentU.family 2 p).family.receivingAnchor,0⟩ : TangentBundle (realModel d) M)
  let tubeTensor (p : M) (q : (coherentU.family 2 p).family.centerDomain)
      (v : Fin (coherentU.dimension 2 p) → ℝ) :=
    originalMetricChartTensor_g18 g (coherentU.family 2 p).family.receivingAnchor
      ((coherentU.coherence 2 p).coordinate q v)
  let tubeDerivative (p : M) (q : (coherentU.family 2 p).family.centerDomain)
      (v : Fin (coherentU.dimension 2 p) → ℝ) :=
    fderiv ℝ ((coherentU.coherence 2 p).coordinate q) v
  let tubeNormalSpace (p : M) := plaqueNormalSpace
    (tubeTensor p ⟨p,(coherentU.family 2 p).family.center_mem⟩ 0)
    (tubeDerivative p ⟨p,(coherentU.family 2 p).family.center_mem⟩ 0)
  let tubeNormal (p : M) (q : (coherentU.family 2 p).family.centerDomain)
      (v : Fin (coherentU.dimension 2 p) → ℝ) :=
    plaqueNormalFrame (tubeTensor p q v) (tubeDerivative p q v) (tubeNormalSpace p).subtypeL
  have hTubeZeroProjectionDerivative (p : M) (q : tubeLabels p)
      (hq : q.val ∈ coefficientLabels p)
      (u : Fin (coherentU.dimension 2 p) → ℝ) (hu : ‖u‖ < coefficientRadius p)
      (hs : (u,0) ∈ (tubeInverse p q).source) :
      HasFDerivAt (fun w ↦ (coherentU.coherence 2 p).coordinate q.val
        ((tubeInverse p q).symm w).1)
        (plaqueMetricProjection (tubeTensor p q.val u) (tubeDerivative p q.val u))
        ((coherentU.coherence 2 p).coordinate q.val u) := by
    have hd := hCoefficient p q.val hq u (by simpa only [Metric.mem_ball,dist_zero_right] using hu)
    exact HPS.native_inverse_projection_derivative_g18 (coherentU.coherence 2 p) g
      ⟨p,(coherentU.family 2 p).family.center_mem⟩ q.val u hd.1
      (tubeInverse p q) (hTubeInverse p q).1 hs hd.2.1
  have hFixedTubeEqual (p : M) (q : (coherentU.family 2 p).family.centerDomain)
      (hq : q ∈ fixedTubeLabels p)
      (z w : (Fin (coherentU.dimension 2 p) → ℝ) × tubeNormalSpace p)
      (hz : z ∈ Metric.closedBall 0 (fixedTubeRadius p) ×ˢ Metric.ball 0 (fixedNormalRadius p))
      (hw : w ∈ Metric.closedBall 0 (fixedTubeRadius p) ×ˢ Metric.ball 0 (fixedNormalRadius p))
      (he : riemannianExponential g ((tubeTangentChart p).symm
          ((coherentU.coherence 2 p).coordinate q z.1,tubeNormal p q z.1 z.2)) =
        riemannianExponential g ((tubeTangentChart p).symm
          ((coherentU.coherence 2 p).coordinate q w.1,tubeNormal p q w.1 w.2))) : z = w := by
    exact (hFixedTube p q hq).1 hz hw (congrArg (tubeChart p) he)
  let tubePhysicalNormal (p : M) (q : (coherentU.family 2 p).family.centerDomain)
      (u : Fin (coherentU.dimension 2 p) → ℝ)
      (hu : u ∈ Metric.ball 0 (coherentU.family 2 p).family.radius)
      (k : tubeNormalSpace p) :
      TangentSpace (realModel d) (((coherentU.family 2 p).family.plaque q).param u) :=
      let P := (coherentU.family 2 p).family.plaque q
      let tr := tubeTr p
      let hx : P.param u ∈ tr.baseSet := by
        simpa only [tr,tubeTr,tubeChart,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
          (coherentU.family 2 p).family.receiving_domain q u hu
      let J := tr.continuousLinearEquivAt ℝ (P.param u) hx
      J.symm (tubeNormal p q u k)
  have hTubePhysicalNormal : ∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain) (u : Fin (coherentU.dimension 2 p) → ℝ) (hu : u ∈ Metric.ball 0 (coherentU.family 2 p).family.radius) (k : tubeNormalSpace p),
      ∀ v ∈ (mfderiv 𝓘(ℝ,Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
        ((coherentU.family 2 p).family.plaque q).param u).range,
        g.inner (((coherentU.family 2 p).family.plaque q).param u)
          (tubePhysicalNormal p q u hu k) v = 0 :=
    TubePhysicalNormalBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels
  have hTubeNormalSizeContinuous (p : M) :=
    (coherentU.coherence 2 p).original_normal_size_continuous_g18 g
      ⟨p,(coherentU.family 2 p).family.center_mem⟩
  have hTubeReconstruction : ∀ (p : M) (q : tubeLabels p) (x : M) (hx : x ∈ (tubeChart p).source) (ht : tubeChart p x ∈ (tubeInverse p q).target),
      let z := (tubeInverse p q).symm (tubeChart p x)
      let ξ := (tubeTangentChart p).symm
        ((coherentU.coherence 2 p).coordinate q.val z.1,tubeNormal p q.val z.1 z.2)
      ξ ∈ riemannianExponentialDomain g ∧
        ξ.proj = ((coherentU.family 2 p).family.plaque q.val).param z.1 ∧
        riemannianExponential g ξ = x :=
    TubeReconstructionBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeDomain hTubeGuard tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous
  have hTubeChartSource (p : M) : p ∈ (tubeChart p).source := by
    let Φ := coherentU.family 2 p
    let p₀ : Φ.family.centerDomain := ⟨p,Φ.family.center_mem⟩
    have hz : (0 : Fin (coherentU.dimension 2 p) → ℝ) ∈ Metric.ball 0 Φ.family.radius :=
      Metric.mem_ball_self Φ.family.radius_pos
    simpa only [(Φ.family.plaque p₀).centered] using Φ.family.receiving_domain p₀ 0 hz
  have hTubeImageCenter : ∀ (p : M),
      tubeChart p p ∈ tubeImage p :=
    TubeImageCenterBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage hTubeImagePoint tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeChartSource
  let tubeGoodLabels (p : M) : Set (tubeLabels p) :=
    {q | 0 ∈ (tubeInverse p q).source}
  have hTubeGoodLabelsOpen (p : M) : IsOpen (tubeGoodLabels p) :=
    (hTubeOpenSource p).preimage (continuous_id.prodMk continuous_const)
  let tubeLabelCover (p : M) : Set M :=
    (fun q : tubeLabels p ↦ q.val.val) '' tubeGoodLabels p
  have hTubeLabelCoverOpen (p : M) : IsOpen (tubeLabelCover p) := by
    have ho := (coherentU.family 2 p).family.centerDomain_open.isOpenEmbedding_subtypeVal.comp
      (tubeLabels p).isOpen.isOpenEmbedding_subtypeVal
    exact ho.isOpenMap _ (hTubeGoodLabelsOpen p)
  have hTubeLabelCoverCenter (p : M) : p ∈ tubeLabelCover p :=
    ⟨⟨⟨p,(coherentU.family 2 p).family.center_mem⟩,hTubeLabel p⟩,hTubeZeroSource p,rfl⟩
  have hTubeAtZero : ∀ (p : M) (q : tubeLabels p),
      tubeInverse p q 0 = tubeChart p q.val.val :=
    TubeAtZeroBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeDomain tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter
  have hTubeInverseAtZero (p : M) (q : tubeLabels p) (hq : q ∈ tubeGoodLabels p) :
      (tubeInverse p q).symm (tubeChart p q.val.val) = 0 := by
    rw [← hTubeAtZero p q]
    exact (tubeInverse p q).left_inv hq
  let tubeProjectedCoordinate (p : M) (q : tubeLabels p) :
      ComplexModel d → ComplexModel d :=
    fun w ↦ (coherentU.coherence 2 p).coordinate q.val ((tubeInverse p q).symm w).1
  let tubeProjectionPair (p : M) (q : tubeLabels p) : M → M × ComplexModel d :=
    fun x ↦ (((coherentU.family 2 p).family.plaque q.val).param
      (((tubeInverse p q).symm (tubeChart p x)).1),
      tubeProjectedCoordinate p q (tubeChart p x))
  obtain ⟨complexDist,complexBundle,hComplexBundle,hComplexRank,hComplexReal⟩ :=
    exists_continuous_complex_rank_one_subbundle a.splitting.unstable hRank
  have hComplexFrame (p : M) := complex_rank_one_frame_g18 complexBundle
    (fun x ↦ by rw [hComplexBundle]; exact hComplexRank x) p
  choose complexFrame hComplexFrameCenter hComplexFrameLinear using hComplexFrame
  have hNativeControl (p : M) (ε : ℝ) (hε : 0 < ε) :
      letI : TopologicalSpace (Bundle.TotalSpace (ComplexModel 1)
          (fun x : M ↦ ↥(complexBundle.toDistribution x))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
      let := hComplexFrameLinear p
      let frame := complexFrame p
      let tr := tubeTr p
      let τ : tubeLabels p → M → M := fun q x ↦
        ((coherentU.family 2 p).family.plaque q.val).param
          (((tubeInverse p q).symm (tubeChart p x)).1)
      let V : tubeLabels p → M → (ComplexModel d) →L[ℝ] (ComplexModel d) := fun q x ↦
        fderiv ℝ (fun w ↦ (coherentU.coherence 2 p).coordinate q.val
          (((tubeInverse p q).symm w).1)) (tubeChart p x)
      ∃ A : Set M, IsOpen A ∧ p ∈ A ∧
        A ⊆ (tubeChart p).source ∩ (tubeChart p) ⁻¹' tubeImage p ∧
        ∀ q : tubeLabels p, q.val.val ∈ A → ∀ x ∈ A,
          ∃ (hxf : x ∈ frame.baseSet) (hyf : τ q x ∈ frame.baseSet)
            (hx : x ∈ tr.baseSet) (hy : τ q x ∈ tr.baseSet)
            (C : ComplexModel 1 →L[ℝ] ComplexModel 1),
            0 < C.det ∧ (∀ v,
              complexTangentToReal d (τ q x)
                (((frame.linearEquivAt ℂ (τ q x) hyf).symm (C v)).val) =
              (tr.continuousLinearEquivAt ℝ (τ q x) hy).symm
                (V q x ((tr.continuousLinearEquivAt ℝ x hx)
                  (complexTangentToReal d x
                    (((frame.linearEquivAt ℂ x hxf).symm v).val))))) ∧
            ∀ v : a.splitting.unstable.toDistribution x,
              let av := (tr.continuousLinearEquivAt ℝ (τ q x) hy).symm
                (V q x ((tr.continuousLinearEquivAt ℝ x hx) v.val))
              (1-ε)*Real.sqrt (g.inner x v.val v.val) ≤
                  Real.sqrt (g.inner (τ q x) av av) ∧
                Real.sqrt (g.inner (τ q x) av av) ≤
                  (1+ε)*Real.sqrt (g.inner x v.val v.val) := by
    exact NativeControlBlock f hmetric hmetric_smooth hM a hb ιs Ls rs ts cs ss Fs invS ιu Lu ru tu cu su Fu invU coherentU L tubeDomain tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverse hTubeInverseContinuous hTubeDerivativeContinuous hTubeZeroSource coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius hTubeZeroProjectionDerivative hTubeChartSource hTubeImageCenter hTubeInverseAtZero complexDist complexBundle hComplexBundle hComplexReal complexFrame hComplexFrameCenter hComplexFrameLinear p ε hε
  let tubeCover (p : M) : Set M :=
    ((tubeChart p).source ∩ (tubeChart p) ⁻¹' tubeImage p) ∩ tubeLabelCover p
  have hTubeCoverOpen (p : M) : IsOpen (tubeCover p) :=
    ((continuousOn_extChartAt (I := realModel d)
      (coherentU.family 2 p).family.receivingAnchor).isOpen_inter_preimage
        (isOpen_extChartAt_source _) (hTubeImage p)).inter (hTubeLabelCoverOpen p)
  have hTubeCoverCenter (p : M) : p ∈ tubeCover p :=
    ⟨⟨hTubeChartSource p,hTubeImageCenter p⟩,hTubeLabelCoverCenter p⟩
  let tubeNormalSize (p : M) (z : ((coherentU.family 2 p).family.centerDomain ×
      (Fin (coherentU.dimension 2 p) → ℝ)) × tubeNormalSpace p) :=
    Real.sqrt (tubeTensor p z.1.1 z.1.2 (tubeNormal p z.1.1 z.1.2 z.2)
      (tubeNormal p z.1.1 z.1.2 z.2))
  have hSmallTube : ∀ (p : M) (η : ℝ) (hη : 0 < η),
      ∃ A : Set M, IsOpen A ∧ p ∈ A ∧ A ⊆ tubeCover p ∧
        ∀ q : tubeLabels p, q.val.val ∈ A → ∀ x ∈ A,
          ‖(tubeInverse p q).symm (tubeChart p x)‖ < η :=
    SmallTubeBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous hTubeZeroSource coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeChartSource hTubeImageCenter hTubeLabelCoverOpen hTubeLabelCoverCenter hTubeInverseAtZero hTubeCoverOpen hTubeCoverCenter
  have hTubeOriginalNormalSize : ∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain) (u : Fin (coherentU.dimension 2 p) → ℝ) (hu : u ∈ Metric.ball 0 (coherentU.family 2 p).family.radius) (k : tubeNormalSpace p),
      tubeNormalSize p ((q,u),k) =
        Real.sqrt (g.inner (((coherentU.family 2 p).family.plaque q).param u)
          (tubePhysicalNormal p q u hu k) (tubePhysicalNormal p q u hu k)) :=
    TubeOriginalNormalSizeBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter
  have hNativeNormalUniqueness : ∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain) (hq : q ∈ fixedTubeLabels p ∩ coefficientLabels p) (u v : Fin (coherentU.dimension 2 p) → ℝ) (hu : ‖u‖ < min (fixedTubeRadius p) (coefficientRadius p)) (hv : ‖v‖ < min (fixedTubeRadius p) (coefficientRadius p)) (ν : TangentSpace (realModel d) (((coherentU.family 2 p).family.plaque q).param u)) (μ : TangentSpace (realModel d) (((coherentU.family 2 p).family.plaque q).param v)) (hν : ∀ w ∈ a.splitting.unstable.toDistribution (((coherentU.family 2 p).family.plaque q).param u), g.inner (((coherentU.family 2 p).family.plaque q).param u) ν w = 0) (hμ : ∀ w ∈ a.splitting.unstable.toDistribution (((coherentU.family 2 p).family.plaque q).param v), g.inner (((coherentU.family 2 p).family.plaque q).param v) μ w = 0) (hνsmall : Real.sqrt (g.inner (((coherentU.family 2 p).family.plaque q).param u) ν ν) < fixedNormalRadius p / coefficientBound p) (hμsmall : Real.sqrt (g.inner (((coherentU.family 2 p).family.plaque q).param v) μ μ) < fixedNormalRadius p / coefficientBound p) (he : riemannianExponential g (⟨((coherentU.family 2 p).family.plaque q).param u,ν⟩ : TangentBundle (realModel d) M) = riemannianExponential g (⟨((coherentU.family 2 p).family.plaque q).param v,μ⟩ : TangentBundle (realModel d) M)),
      u = v :=
    NativeNormalUniquenessBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels coefficientRadius coefficientBound hCoefficientBound hCoefficient fixedTubeRadius fixedTubeLabels hFixedTubeLabels fixedNormalRadius hFixedTubeEqual hTubeNormalSizeContinuous hTubeImageCenter
  have hTubePhysicalReconstruction : ∀ (p : M) (q : tubeLabels p) (x : M) (hx : x ∈ (tubeChart p).source) (ht : tubeChart p x ∈ (tubeInverse p q).target),
      let z := (tubeInverse p q).symm (tubeChart p x)
      ∃ ξ : TangentBundle (realModel d) M,
        ξ ∈ riemannianExponentialDomain g ∧
        ξ.proj = ((coherentU.family 2 p).family.plaque q.val).param z.1 ∧
        riemannianExponential g ξ = x ∧
        Real.sqrt (g.inner ξ.proj ξ.2 ξ.2) = tubeNormalSize p ((q.val,z.1),z.2) ∧
        ∀ v ∈ a.splitting.unstable.toDistribution ξ.proj, g.inner ξ.proj ξ.2 v = 0 :=
    TubePhysicalReconstructionBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeDomain tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubePhysicalNormal hTubeNormalSizeContinuous hTubeReconstruction hTubeImageCenter hTubeOriginalNormalSize
  have hSmallTubeAndPhysical (p : M) (η : ℝ) (hη : 0 < η) (θ : ℝ) (hθ : 0 < θ) :
      ∃ A : Set M, IsOpen A ∧ p ∈ A ∧ A ⊆ tubeCover p ∧
        ∀ q : tubeLabels p, q.val.val ∈ A → ∀ x ∈ A,
          ‖(tubeInverse p q).symm (tubeChart p x)‖ < η ∧
          let z := (tubeInverse p q).symm (tubeChart p x)
          tubeNormalSize p ((q.val,z.1),z.2) < θ := by
    let q₀ : tubeLabels p :=
      ⟨⟨p,(coherentU.family 2 p).family.center_mem⟩,hTubeLabel p⟩
    have hcont := (hTubeInverseContinuous p).continuousAt
      ((isOpen_univ.prod (hTubeImage p)).mem_nhds
        (show (q₀,tubeChart p p) ∈ univ ×ˢ tubeImage p from
          ⟨mem_univ _,hTubeImageCenter p⟩))
    have hzero : (tubeInverse p q₀).symm (tubeChart p p) = 0 :=
      hTubeInverseAtZero p q₀ (hTubeZeroSource p)
    have hsize : ContinuousAt (tubeNormalSize p) ((q₀.val,0),0) :=
      (hTubeNormalSizeContinuous p).1
    have hsize0 : tubeNormalSize p ((q₀.val,0),0) = 0 :=
      (hTubeNormalSizeContinuous p).2
    have hsize' : ContinuousAt (tubeNormalSize p)
        ((q₀.val,((tubeInverse p q₀).symm (tubeChart p p)).1),
          ((tubeInverse p q₀).symm (tubeChart p p)).2) := by
      simpa only [hzero,Prod.fst_zero,Prod.snd_zero] using hsize
    have hjoined : ContinuousAt (fun z : tubeLabels p × ComplexModel d ↦
        ((z.1.val,((tubeInverse p z.1).symm z.2).1),
          ((tubeInverse p z.1).symm z.2).2)) (q₀,tubeChart p p) :=
      ((continuousAt_subtype_val.comp continuousAt_fst).prodMk hcont.fst).prodMk hcont.snd
    have hcomposed : ContinuousAt (fun z : tubeLabels p × ComplexModel d ↦
        tubeNormalSize p ((z.1.val,((tubeInverse p z.1).symm z.2).1),
          ((tubeInverse p z.1).symm z.2).2)) (q₀,tubeChart p p) :=
      ContinuousAt.comp (g := tubeNormalSize p) (x := (q₀,tubeChart p p)) (f := fun z : tubeLabels p × ComplexModel d ↦
        ((z.1.val,((tubeInverse p z.1).symm z.2).1),
          ((tubeInverse p z.1).symm z.2).2)) hsize' hjoined
    have hphysicalSmall := hcomposed.eventually_lt_const
      (show tubeNormalSize p ((q₀.val,((tubeInverse p q₀).symm (tubeChart p p)).1),
        ((tubeInverse p q₀).symm (tubeChart p p)).2) < θ by
          simpa only [hzero,Prod.fst_zero,Prod.snd_zero,hsize0] using hθ)
    have hnormSmall := hcont.norm.eventually_lt_const
      (show ‖(tubeInverse p q₀).symm (tubeChart p p)‖ < η by
        simpa only [hzero,norm_zero] using hη)
    have hsmall := hnormSmall.and hphysicalSmall
    have hcoord : ContinuousAt (fun z : tubeLabels p × M ↦ (z.1,tubeChart p z.2)) (q₀,p) :=
      continuousAt_fst.prodMk
        ((continuousAt_extChartAt' (hTubeChartSource p)).comp continuousAt_snd)
    exact open_label_relation_localization_g18 (fun q : tubeLabels p ↦ q.val.val)
      ((coherentU.family 2 p).family.centerDomain_open.isOpenEmbedding_subtypeVal.comp
        (tubeLabels p).isOpen.isOpenEmbedding_subtypeVal) q₀
      (fun q x ↦ ‖(tubeInverse p q).symm (tubeChart p x)‖ < η ∧
        tubeNormalSize p ((q.val,((tubeInverse p q).symm (tubeChart p x)).1),
          ((tubeInverse p q).symm (tubeChart p x)).2) < θ)
      (hcoord.eventually hsmall) (tubeCover p) (hTubeCoverOpen p) (hTubeCoverCenter p)
  have hSmallPhysicalTube : ∀ (p : M) (η : ℝ) (hη : 0 < η),
      ∃ A : Set M, IsOpen A ∧ p ∈ A ∧ A ⊆ tubeCover p ∧
        ∀ q : tubeLabels p, q.val.val ∈ A → ∀ x ∈ A,
          let z := (tubeInverse p q).symm (tubeChart p x)
          tubeNormalSize p ((q.val,z.1),z.2) < η :=
    SmallPhysicalTubeBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous hTubeZeroSource coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeChartSource hTubeImageCenter hTubeLabelCoverOpen hTubeLabelCoverCenter hTubeInverseAtZero hTubeCoverOpen hTubeCoverCenter
  have hNativeMetricBounds : ∀ (p : M),
      ∃ K : Set (coherentU.family 2 p).family.centerDomain,
        IsCompact K ∧ K ∈ 𝓝 ⟨p,(coherentU.family 2 p).family.center_mem⟩ ∧
        ∃ B : ℝ, 0 < B ∧ ∀ q ∈ K,
          ∀ u ∈ Metric.closedBall (0 : Fin (coherentU.dimension 2 p) → ℝ)
            ((coherentU.family 2 p).family.radius / 2),
          ∀ v : Fin (coherentU.dimension 2 p) → ℝ,
            Real.sqrt (g.inner (((coherentU.family 2 p).family.plaque q).param u)
              (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
                ((coherentU.family 2 p).family.plaque q).param u v)
              (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
                ((coherentU.family 2 p).family.plaque q).param u v)) ≤ B * ‖v‖ :=
    NativeMetricBoundsBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter
  choose speedCore hSpeedCore hSpeedCoreCenter speedBound hSpeedBound hSpeed
    using hNativeMetricBounds
  have hNativeMetricLowerBounds : ∀ (p : M),
      ∃ c : ℝ, 0 < c ∧ ∀ q ∈ speedCore p,
        ∀ u ∈ Metric.closedBall (0 : Fin (coherentU.dimension 2 p) → ℝ)
          ((coherentU.family 2 p).family.radius / 2),
        ∀ v : Fin (coherentU.dimension 2 p) → ℝ,
          c * ‖v‖ ≤ Real.sqrt (g.inner (((coherentU.family 2 p).family.plaque q).param u)
            (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
              ((coherentU.family 2 p).family.plaque q).param u v)
            (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
              ((coherentU.family 2 p).family.plaque q).param u v)) :=
    NativeMetricLowerBoundsBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter speedCore hSpeedCore hSpeedCoreCenter
  let speedCover (p : M) : Set M := Subtype.val '' interior
    (speedCore p ∩ (fixedTubeLabels p ∩ coefficientLabels p))
  have hSpeedCoverOpen (p : M) : IsOpen (speedCover p) :=
    (coherentU.family 2 p).family.centerDomain_open.isOpenEmbedding_subtypeVal.isOpenMap _
      isOpen_interior
  have hSpeedCoverCenter (p : M) : p ∈ speedCover p :=
    ⟨⟨p,(coherentU.family 2 p).family.center_mem⟩,
      mem_interior_iff_mem_nhds.mpr
        (inter_mem (hSpeedCoreCenter p) (inter_mem (hFixedTubeLabels p) (hCoefficientLabels p))),rfl⟩
  refine ⟨L, ?_⟩
  let := L.realAmbientCharts
  have hNativeDistanceContinuous (x : M) :
      letI := nativeTopology x
      letI := nativeCharts x
      Continuous (fun z : L.U x × L.U x ↦ intrinsicHermitianLeafEDist
        (r := (L.unstable x).rank) (Subtype.val : L.U x → M) hmetric z.1 z.2) := by
    let := nativeTopology x
    let := nativeCharts x
    let : T2Space (L.U x) := (L.unstable x).hausdorff
    let : IsManifold (L.uModel x) ∞ (L.U x) := (L.unstable x).smoothAtlas
    exact intrinsicHermitianLeafEDist_continuous_g18 (L := L.U x)
      (r := (L.unstable x).rank) hmetric hmetric_smooth
      (Subtype.val : L.U x → M) (L.unstable x).inclusion_smooth
      (fun z ↦ ((L.unstable x).inclusion_immersion z).mfderiv_injective (by simp))
  have hNativeLift : ∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain) (x : M) (hclass : ForwardAsymptotic (f.symm : M → M) x q.val),
      letI := L.identification.unstableTopology x
      letI := L.identification.unstableCharts x
      let B : Opens (Fin (coherentU.dimension 2 p) → ℝ) :=
        ⟨Metric.ball 0 (coherentU.family 2 p).family.radius, Metric.isOpen_ball⟩
      ∃ l : B → L.U x,
        (∀ v, (l v).val = ((coherentU.family 2 p).family.plaque q).param v.val) ∧
        IsLocalDiffeomorph 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ)
          (L.uModel x) ∞ l ∧ IsOpenEmbedding l :=
    NativeLiftBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU hNativeUnstableAsymptotic tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter speedCore hSpeedCoreCenter hSpeedCoverOpen hSpeedCoverCenter
  have hNativeLocalProjection (p : M) (q : tubeLabels p)
      (x : M) (hclass : ForwardAsymptotic (f.symm : M → M) x q.val.val) :
      letI := nativeTopology x
      letI := nativeCharts x
      ∃ hO : IsOpen ((tubeChart p).source ∩ (tubeChart p) ⁻¹' (tubeInverse p q).target),
      let O : Opens M := ⟨(tubeChart p).source ∩ (tubeChart p) ⁻¹' (tubeInverse p q).target,hO⟩
      ∃ ψ : O → L.U x, ContMDiff (realModel d) (L.uModel x) 1 ψ ∧
        ∀ z : O, (ψ z).val = ((coherentU.family 2 p).family.plaque q.val).param
          (((tubeInverse p q).symm (tubeChart p z.val)).1) := by
    let := nativeTopology x
    let := nativeCharts x
    obtain ⟨l,hl,hlocal,hopen⟩ := hNativeLift p q.val x hclass
    let B : Opens (Fin (coherentU.dimension 2 p) → ℝ) :=
      ⟨Metric.ball 0 (coherentU.family 2 p).family.radius,Metric.isOpen_ball⟩
    obtain ⟨hO,ψ,hψ,hvalue⟩ := native_local_smooth_projection_g18 (L.uModel x)
      (coherentU.family 2 p).family.receivingAnchor B l (hlocal.contMDiff.of_le (by simp))
      (tubeInverse p q) (hTubeInverse p q).2.2.2.1
      (fun z hz ↦ ((hTubeInverse p q).2.2.2.2 z hz).1.2)
    exact ⟨hO,ψ,hψ,fun z ↦ (congrArg Subtype.val (hvalue z)).trans (hl _)⟩
  have hNativeChart : ∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain) (x : M) (hclass : ForwardAsymptotic (f.symm : M → M) x q.val),
      letI := L.identification.unstableTopology x
      letI := L.identification.unstableCharts x
      ∃ J : (Fin (L.unstable x).rank → ℝ) ≃ₗᵢ[ℝ] (Fin (coherentU.dimension 2 p) → ℝ),
        ∃ c : OpenPartialHomeomorph (L.U x) (Fin (L.unstable x).rank → ℝ),
          c ∈ IsManifold.maximalAtlas (L.uModel x) ∞ (L.U x) ∧
          c.target = J ⁻¹' Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
            (coherentU.family 2 p).family.radius ∧
          (∀ v, J v ∈ Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
            (coherentU.family 2 p).family.radius →
              (c.symm v).val = ((coherentU.family 2 p).family.plaque q).param (J v)) ∧
          ∃ center : L.U x, center.val = q.val ∧ center ∈ c.source ∧ c center = 0 :=
    NativeChartBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius fixedTubeRadius hFixedTubeRadius fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter speedCore hSpeedCoreCenter hNativeMetricLowerBounds hSpeedCoverOpen hSpeedCoverCenter hNativeLift
  choose lowerBound hLowerBound hLower using hNativeMetricLowerBounds
  have hNativeConfinement : ∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain) (hqK : q ∈ speedCore p) (x : M) (hclass : ForwardAsymptotic (f.symm : M → M) x q.val) (R : ℝ) (hR : 0 < R) (hRδ : R < (coherentU.family 2 p).family.radius / 2),
      letI := L.identification.unstableTopology x
      letI := L.identification.unstableCharts x
      ∃ J : (Fin (L.unstable x).rank → ℝ) ≃ₗᵢ[ℝ] (Fin (coherentU.dimension 2 p) → ℝ),
        ∃ c : OpenPartialHomeomorph (L.U x) (Fin (L.unstable x).rank → ℝ),
          c ∈ IsManifold.maximalAtlas (L.uModel x) ∞ (L.U x) ∧
          ∃ center : L.U x, center.val = q.val ∧ center ∈ c.source ∧ c center = 0 ∧
            ∀ y : L.U x,
              intrinsicHermitianLeafEDist (r := (L.unstable x).rank)
                (Subtype.val : L.U x → M) hmetric center y <
                ENNReal.ofReal (lowerBound p * R) →
              y ∈ c.source ∧ ‖J (c y)‖ < R ∧
                ((coherentU.family 2 p).family.plaque q).param (J (c y)) = y.val :=
    NativeConfinementBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius fixedTubeRadius hFixedTubeRadius fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter speedCore hSpeedCoreCenter hSpeedCoverOpen hSpeedCoverCenter hNativeChart lowerBound hLowerBound hLower
  have hGlobalNormalUniqueness : ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧ ∀ x : M,
      letI := L.identification.unstableTopology x
      letI := L.identification.unstableCharts x
      ∀ anchor w₁ w₂ : L.U x,
        intrinsicHermitianLeafEDist (r := (L.unstable x).rank)
          (Subtype.val : L.U x → M) hmetric anchor w₁ < ENNReal.ofReal δ →
        intrinsicHermitianLeafEDist (r := (L.unstable x).rank)
          (Subtype.val : L.U x → M) hmetric anchor w₂ < ENNReal.ofReal δ →
        ∀ ξ ζ : TangentBundle (realModel d) M,
          ξ.proj = w₁.val → ζ.proj = w₂.val →
          Real.sqrt (g.inner ξ.proj ξ.2 ξ.2) < η →
          Real.sqrt (g.inner ζ.proj ζ.2 ζ.2) < η →
          (∀ v ∈ a.splitting.unstable.toDistribution ξ.proj, g.inner ξ.proj ξ.2 v = 0) →
          (∀ v ∈ a.splitting.unstable.toDistribution ζ.proj, g.inner ζ.proj ζ.2 v = 0) →
          riemannianExponential g ξ = riemannianExponential g ζ → w₁ = w₂ :=
    GlobalNormalUniquenessBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius coefficientBound hCoefficientBound fixedTubeRadius hFixedTubeRadius fixedTubeLabels hFixedTubeLabels fixedNormalRadius hFixedNormalRadius hTubeNormalSizeContinuous hTubeImageCenter hNativeNormalUniqueness speedCore hSpeedCoreCenter hSpeedCoverOpen hSpeedCoverCenter lowerBound hLowerBound hNativeConfinement
  obtain ⟨normalBaseRadius,normalSizeRadius,hNormalBaseRadius,hNormalSizeRadius,
    hNormalUnique⟩ := hGlobalNormalUniqueness
  have hNativeRadialBound : ∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain) (x : M),
      letI := L.identification.unstableTopology x
      letI := L.identification.unstableCharts x
      let D : Opens (Fin (coherentU.dimension 2 p) → ℝ) :=
        ⟨Metric.ball 0 (coherentU.family 2 p).family.radius, Metric.isOpen_ball⟩
      ∀ (l : D → L.U x)
        (hl : ∀ v, (l v).val = ((coherentU.family 2 p).family.plaque q).param v.val)
        (hlocal : IsLocalDiffeomorph 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ)
          (L.uModel x) ∞ l)
        (C : ℝ)
        (hbound : ∀ u ∈ Metric.closedBall (0 : Fin (coherentU.dimension 2 p) → ℝ)
          ((coherentU.family 2 p).family.radius / 2), ∀ w : Fin (coherentU.dimension 2 p) → ℝ,
          Real.sqrt (g.inner (((coherentU.family 2 p).family.plaque q).param u)
            (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
              ((coherentU.family 2 p).family.plaque q).param u w)
            (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
              ((coherentU.family 2 p).family.plaque q).param u w)) ≤ C * ‖w‖)
        (v : Fin (coherentU.dimension 2 p) → ℝ)
        (hv : v ∈ Metric.closedBall 0 ((coherentU.family 2 p).family.radius / 2)),
        intrinsicHermitianLeafEDist (r := (L.unstable x).rank)
          (Subtype.val : L.U x → M) hmetric
          (l ⟨0,Metric.mem_ball_self (coherentU.family 2 p).family.radius_pos⟩)
          (l ⟨v,Metric.closedBall_subset_ball (half_lt_self
            (coherentU.family 2 p).family.radius_pos) hv⟩) ≤ ENNReal.ofReal (C * ‖v‖) :=
    NativeRadialBoundBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter speedCore hSpeedCoreCenter hSpeedCoverOpen hSpeedCoverCenter
  choose b hboxPoint using L.foliation.cover
  let c (p : M) := (L.foliation.box (b p)).chart.symm ⟨p,hboxPoint p⟩
  have hc (p : M) : ((L.foliation.box (b p)).chart (c p)).val = p :=
    congrArg Subtype.val ((L.foliation.box (b p)).chart.apply_symm_apply ⟨p,hboxPoint p⟩)
  choose R hR hRF T ht hcenter hproductBox hproductOpen hproductCoord using fun p : M ↦
    native_identification_anosov_stable_family_local_product_g18 f a L.identification
      (familiesS.family p).family (b p) (c p).1 (c p).2 (hc p)
  let U (p : M) : TopologicalSpace.Opens (Fin (familiesS.dimension p) → ℝ) :=
    ⟨Metric.ball 0 (R p),Metric.isOpen_ball⟩
  let J (p : M) : U p × T p → M := fun z ↦
    ((familiesS.family p).family.plaque
      ⟨((L.foliation.box (b p)).chart ((c p).1,z.2.val)).val,hcenter p z.2⟩).param z.1.val
  have hJ (p : M) : IsOpenEmbedding (J p) := hproductOpen p
  have hpJ (p : M) : p ∈ Set.range (J p) := by
    refine ⟨(⟨0,Metric.mem_ball_self (hR p)⟩,⟨(c p).2,ht p⟩),?_⟩
    exact ((familiesS.family p).family.plaque _).centered.trans (hc p)
  dsimp only [RankOneNativeLeaves.ComparisonProperty]
  intro q x y γ e h hsource hpoint hgerm
  let := L.foliation.stableTopology q
  let := nativeTopology (γ 0).val
  let := nativeTopology (γ 1).val
  let receivingChart : OpenPartialHomeomorph (L.U (γ 1).val) (ComplexModel 1) := by
    let := nativeCharts (γ 1).val
    let : ChartedSpace (Fin (L.unstable (γ 1).val).rank → ℝ) (L.U (γ 1).val) :=
      nativeCharts (γ 1).val
    let : ChartedSpace (ComplexModel 1) (L.U (γ 1).val) :=
      (L.complexUnstable (γ 1).val).charts
    exact chartAt (ComplexModel 1) (L.uPoint (γ 1).val)
  have hReceivingCenter : L.uPoint (γ 1).val ∈ receivingChart.source := by
    let := nativeCharts (γ 1).val
    let : ChartedSpace (Fin (L.unstable (γ 1).val).rank → ℝ) (L.U (γ 1).val) :=
      nativeCharts (γ 1).val
    let : ChartedSpace (ComplexModel 1) (L.U (γ 1).val) :=
      (L.complexUnstable (γ 1).val).charts
    exact mem_chart_source (ComplexModel 1) _
  have hReceivingNear : ∀ᶠ z in 𝓝 (L.uPoint (γ 0).val), h z ∈ receivingChart.source :=
    (h.continuousAt hsource).preimage_mem_nhds
      (receivingChart.open_source.mem_nhds (by rw [hpoint]; exact hReceivingCenter))
  obtain ⟨hprefix, W₀, hW₀, hxW₀, hprefixSource, hprefixContinuous⟩ :=
    path_continuous_prefix_family_g1 L.foliation γ
  have hzero : (hprefix 0).map =ᶠ[𝓝 (L.foliation.uPoint (γ 0).val)] id := by
    obtain ⟨i,hi⟩ := L.foliation.cover (γ 0).val
    let zw := (L.foliation.box i).chart.symm ⟨(γ 0).val,hi⟩
    have hv : ((L.foliation.box i).chart zw).val = (γ 0).val :=
      congrArg Subtype.val ((L.foliation.box i).chart.apply_symm_apply ⟨(γ 0).val,hi⟩)
    obtain ⟨e₀,hebox,hef,hes,het,_⟩ := local_plaque_transport_of_box L.foliation i
      zw.1 zw.1 zw.2 (γ 0).val (γ 0).val hv hv
    have hs : ∀ v : unitInterval, 0 ≤ v → v ≤ 0 →
        ∃ z : FoliationCoordinateDisk L.stableDimension,
          ((L.foliation.box e₀.box).chart (z,e₀.transverse)).val = (γ v).val := by
      intro v hav hvb
      have hv0 : v = 0 := le_antisymm hvb bot_le
      subst v
      refine ⟨zw.1,?_⟩
      have hh := congrArg (fun j ↦ ((L.foliation.box j).chart (zw.1,zw.2)).val) hebox
      simpa only [het] using hh.trans hv
    exact Filter.Germ.coe_eq.mp
      ((plaque_chain_germ_in_one_plaque L.foliation γ (hprefix 0).chain e₀ hs).trans
        (same_center_plaque_identity_germ L.foliation e₀))
  obtain ⟨Vzero,hVzero,hVzeroOpen,hxVzero⟩ := mem_nhds_iff.mp hzero
  let H₀ : unitInterval × W₀ → M := fun p ↦ ((hprefix p.1).map p.2.val).val
  have hH₀ : Continuous H₀ := hprefixContinuous.comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    (fun p ↦ ⟨mem_univ _,p.2.property⟩)
  obtain ⟨n,hn,t,ht0,ht1,ht,assigned,Nfam,hNfam,hbaseNfam,hsegments⟩ :=
    parametric_openCover_pathSubdivision_g18 H₀ hH₀
      (⟨L.foliation.uPoint (γ 0).val,hxW₀⟩ : W₀)
      (fun p ↦ Set.range (J p))
      (fun p ↦ (hJ p).isOpen_range)
      (fun r ↦ ⟨_,hpJ _⟩)
  let N₀ := (Subtype.val '' Nfam) ∩ Vzero
  have hN₀open : IsOpen N₀ :=
    (hW₀.isOpenMap_subtype_val Nfam hNfam).inter hVzeroOpen
  have hN₀sub : N₀ ⊆ W₀ := by
    rintro z ⟨⟨p,_,rfl⟩,_⟩
    exact p.property
  have hxN₀ : L.foliation.uPoint (γ 0).val ∈ N₀ :=
    ⟨⟨⟨_,hxW₀⟩,hbaseNfam,rfl⟩,hxVzero⟩
  have hePrefix : e.map =ᶠ[𝓝 (L.foliation.uPoint (γ 0).val)] (hprefix 1).map :=
    Filter.Germ.coe_eq.mp (same_subpath_plaque_chain_germ L.foliation γ e.chain
      (hprefix 1).map (hprefix 1).chain)
  have htransport := (L.unstableClass (γ 0).val).symm.continuous.tendsto
    (L.uPoint (γ 0).val)
  have htransportPoint : (L.unstableClass (γ 0).val).symm (L.uPoint (γ 0).val) =
      L.foliation.uPoint (γ 0).val := by
    exact (L.unstableClass (γ 0).val).symm_apply_apply _
  rw [htransportPoint] at htransport
  have hfinal : ∀ᶠ z in 𝓝 (L.uPoint (γ 0).val),
      h z = L.holonomyRepresentative γ (hprefix 1) z := by
    filter_upwards [hgerm, htransport.eventually hePrefix] with z hz hz'
    rw [hz]
    exact congrArg (L.unstableClass (γ 1).val) hz'
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (hfinal.and hReceivingNear)
  let N := ((L.unstableClass (γ 0).val).symm ⁻¹' N₀ ∩ h.source) ∩ V
  have hNopen : IsOpen N :=
    ((hN₀open.preimage (L.unstableClass (γ 0).val).symm.continuous).inter h.open_source).inter hVo
  refine ⟨N, hNopen, ?_, fun z hz ↦ hz.1.2, ?_⟩
  · refine ⟨⟨?_, hsource⟩, hxV⟩
    simpa only [Set.mem_preimage, RankOneNativeLeaves.uPoint, Homeomorph.symm_apply_apply] using hxN₀
  · intro Wtarget hWtarget hWtargetN hxWtarget
    have hWtargetCompact : IsCompact Wtarget := by
      obtain ⟨c, hc, a, r, hr, hball, hWc⟩ := hWtarget
      rw [hWc]
      exact (isCompact_closedBall a r).image_of_continuousOn
        (c.symm.continuousOn.mono hball)
    let := nativeCharts (γ 0).val
    let : T2Space (L.U (γ 0).val) := (L.unstable (γ 0).val).hausdorff
    let : LocallyCompactSpace (L.U (γ 0).val) :=
      ChartedSpace.locallyCompactSpace (Fin (L.unstable (γ 0).val).rank → ℝ) (L.U (γ 0).val)
    obtain ⟨sourceOpen,hSourceOpen,hTargetSource,hSourceN,hWcompact⟩ :=
      exists_open_between_and_isCompact_closure hWtargetCompact hNopen hWtargetN
    let W := closure sourceOpen
    have hWN : W ⊆ N := hSourceN
    have hTargetInterior : Wtarget ⊆ interior W :=
      hTargetSource.trans (hSourceOpen.subset_interior_iff.mpr subset_closure)
    obtain ⟨sourceChart,hSourceChart,sourceCenter,sourceRadius,hSourceRadius,
      hSourceBall,hWtargetEq⟩ := hWtarget
    let coordinateBuffer := sourceChart.target ∩ sourceChart.symm ⁻¹' interior W
    have hCoordinateBufferOpen : IsOpen coordinateBuffer :=
      sourceChart.symm.continuousOn.isOpen_inter_preimage sourceChart.open_target isOpen_interior
    have hSourceBuffer : Metric.closedBall sourceCenter sourceRadius ⊆ coordinateBuffer := by
      intro z hz
      refine ⟨hSourceBall hz,hTargetInterior ?_⟩
      rw [hWtargetEq]
      exact mem_image_of_mem sourceChart.symm hz
    obtain ⟨bufferWidth,hBufferWidth,hBufferThickening⟩ :=
      (isCompact_closedBall sourceCenter sourceRadius).exists_thickening_subset_open
        hCoordinateBufferOpen hSourceBuffer
    let degreeRadius := sourceRadius + bufferWidth / 3
    let regularRadius := sourceRadius + 2 * bufferWidth / 3
    have hSourceDegree : sourceRadius < degreeRadius := by
      dsimp only [degreeRadius]
      linarith only [hBufferWidth]
    have hDegreeRegular : degreeRadius < regularRadius := by
      dsimp only [degreeRadius,regularRadius]
      linarith only [hBufferWidth]
    have hRegularBuffer : Metric.closedBall sourceCenter regularRadius ⊆ coordinateBuffer := by
      apply Subset.trans (Metric.closedBall_subset_ball (show regularRadius < bufferWidth+sourceRadius by
        dsimp only [regularRadius]
        linarith only [hBufferWidth]))
      rw [← thickening_closedBall hBufferWidth hSourceRadius.le sourceCenter]
      exact hBufferThickening
    have hReceivingOn : ∀ z ∈ W, h z ∈ receivingChart.source :=
      fun z hz ↦ (hV (hWN hz).2).2
    have hFinalOn : ∀ z ∈ W, h z = L.holonomyRepresentative γ (hprefix 1) z :=
      fun z hz ↦ (hV (hWN hz).2).1
    have hCommonSource : ∀ r, ∀ z ∈ W,
        (L.unstableClass (γ 0).val).symm z ∈ (hprefix r).map.source :=
      fun r z hz ↦ hprefixSource r (hN₀sub (hWN hz).1.1)
    let H : unitInterval × L.U (γ 0).val → M := fun p ↦
      ((hprefix p.1).map ((L.unstableClass (γ 0).val).symm p.2)).val
    have hH : ContinuousOn H (univ ×ˢ W) := by
      apply hprefixContinuous.comp
        (continuous_fst.prodMk ((L.unstableClass (γ 0).val).symm.continuous.comp
          continuous_snd)).continuousOn
      exact fun p hp ↦ ⟨mem_univ _, hN₀sub (hWN hp.2).1.1⟩
    have hSubpaths : ∀ j : Fin n, ∀ z ∈ W,
        ∀ r ∈ Icc (t j.castSucc) (t j.succ),
          H (r,z) ∈ Set.range (J (assigned j)) := by
      intro j z hz r hr
      obtain ⟨p,hp,heq⟩ := (hWN hz).1.1.1
      simpa only [H₀,H,heq] using hsegments j p hp r hr
    have hHzero (z : W) : H (0,z.val) = z.val.val := by
      change ((hprefix 0).map ((L.unstableClass (γ 0).val).symm z.val)).val = z.val.val
      rw [hVzero (hWN z.property).1.1.2]
      have hh := L.identification.unstable_points (γ 0).val
        ((L.unstableClass (γ 0).val).symm z.val)
      change (L.unstableClass (γ 0).val ((L.unstableClass (γ 0).val).symm z.val)).val = _ at hh
      exact hh.symm.trans (congrArg Subtype.val
        ((L.unstableClass (γ 0).val).apply_symm_apply z.val))
    have hStable : ∀ r, ∀ z ∈ W,
        L.foliation.stablePartition
          ((L.unstableClass (γ 0).val).symm z).val (H (r,z)) := by
      intro r z hz
      exact path_holonomy_stable_related L.foliation γ (hprefix r).chain
        ((L.unstableClass (γ 0).val).symm z) (hCommonSource r z hz)
    let I (j : Fin n) : Set unitInterval := Icc (t j.castSucc) (t j.succ)
    let Hseg (j : Fin n) : I j × W → M := fun z ↦ H (z.1.val,z.2.val)
    have hHseg (j : Fin n) : Continuous (Hseg j) := hH.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z ↦ ⟨mem_univ _,z.2.property⟩)
    let eprod (p : M) := (hJ p).isEmbedding.toHomeomorph
    let Q (j : Fin n) : I j × W → U (assigned j) × T (assigned j) := fun z ↦
      (eprod (assigned j)).symm
        ⟨Hseg j z,hSubpaths j z.2.val z.2.property z.1.val z.1.property⟩
    have hQ (j : Fin n) : Continuous (Q j) :=
      (eprod (assigned j)).symm.continuous.comp ((hHseg j).subtype_mk _)
    have hQval (j : Fin n) (z : I j × W) : J (assigned j) (Q j z) = Hseg j z :=
      congrArg Subtype.val ((eprod (assigned j)).apply_symm_apply
        ⟨Hseg j z,hSubpaths j z.2.val z.2.property z.1.val z.1.property⟩)
    let Cseg (j : Fin n) : I j × W → (familiesS.family (assigned j)).family.centerDomain :=
      fun z ↦ ⟨((L.foliation.box (b (assigned j))).chart
        ((c (assigned j)).1,(Q j z).2.val)).val,hcenter (assigned j) (Q j z).2⟩
    have hCseg (j : Fin n) : Continuous (Cseg j) :=
      (continuous_subtype_val.comp ((L.foliation.box (b (assigned j))).chart.continuous.comp
        (continuous_const.prodMk (continuous_subtype_val.comp (hQ j).snd)))).subtype_mk _
    let Kseg (j : Fin n) := Set.range (Cseg j)
    have hKseg (j : Fin n) : IsCompact (Kseg j) := by
      let : CompactSpace W := isCompact_iff_compactSpace.mp hWcompact
      let : CompactSpace (I j) := isCompact_iff_compactSpace.mp isCompact_Icc
      exact isCompact_range (hCseg j)
    have hboxseg (j : Fin n) (z : I j × W) :
        Hseg j z ∈ (L.foliation.box (b (assigned j))).image := by
      rw [← hQval]
      exact hproductBox (assigned j) (Q j z)
    have hQcoord (j : Fin n) (z : I j × W) :
        ((L.foliation.box (b (assigned j))).chart.symm ⟨Hseg j z,hboxseg j z⟩).2 =
          (Q j z).2.val := by
      have hh := hproductCoord (assigned j) (Q j z)
      change ((L.foliation.box (b (assigned j))).chart.symm
        ⟨J (assigned j) (Q j z),_⟩).2 = (Q j z).2.val at hh
      simpa only [hQval] using hh
    have hCseg_const (j : Fin n) (z : W) (r r' : I j) :
        Cseg j (r,z) = Cseg j (r',z) := by
      let : PreconnectedSpace (I j) := Subtype.preconnectedSpace isPreconnected_Icc
      let xz := ((L.unstableClass (γ 0).val).symm z.val).val
      let qz := Quotient.mk L.foliation.stablePartition xz
      let := L.foliation.stableTopology qz
      let := L.identification.stableTopology xz
      let := (L.identification.nativeS xz).secondCountable
      let : SecondCountableTopology (IntrinsicFoliationLeaf L.foliation.stablePartition qz) :=
        (L.identification.stableClassHomeomorph xz).secondCountableTopology
      have he := stable_connected_range_in_box L.foliation (b (assigned j)) qz
        (fun r : I j ↦ Hseg j (r,z))
        ((hHseg j).comp (continuous_id.prodMk continuous_const))
        (fun r ↦ hboxseg j (r,z))
        (fun r ↦ Quotient.sound (L.foliation.stablePartition.symm
          (hStable r.val z.val z.property))) inferInstance r r'
      rw [hQcoord,hQcoord] at he
      apply Subtype.ext
      exact congrArg (fun v ↦ ((L.foliation.box (b (assigned j))).chart
        ((c (assigned j)).1,v)).val) he
    obtain ⟨m,hmTop,hm⟩ := anosov_exists_full_length_metric f a
    let : MetricSpace M := originalAmbientMetric
    have hshrink (j : Fin n) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop,
        ∀ z : I j × W, m.dist ((f^[k]) (Hseg j z)) ((f^[k]) (Cseg j z).val) < ε := by
      filter_upwards [anosov_native_stable_plaque_uniform_shrinking f a m hm
        (familiesS.family (assigned j)).family (Kseg j) (hKseg j)
        (hR (assigned j)) (hRF (assigned j)) ε hε] with k hk
      intro z
      have hh := hk (Cseg j z) (Set.mem_range_self z) (Q j z).1.val
        (Metric.ball_subset_closedBall (Q j z).1.property)
      change m.dist ((f^[k]) (J (assigned j) (Q j z)))
        ((f^[k]) (Cseg j z).val) < ε at hh
      rwa [hQval] at hh
    have hdiam (j : Fin n) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop,
        ∀ z : W, ∀ r r' : I j,
          m.dist ((f^[k]) (Hseg j (r,z))) ((f^[k]) (Hseg j (r',z))) < ε := by
      filter_upwards [hshrink j (ε/2) (half_pos hε)] with k hk
      intro z r r'
      have h₁ := hk (r,z)
      have h₂ := hk (r',z)
      rw [← hCseg_const j z r r'] at h₂
      have hh := m.dist_triangle ((f^[k]) (Hseg j (r,z)))
        ((f^[k]) (Cseg j (r,z)).val) ((f^[k]) (Hseg j (r',z)))
      rw [m.dist_comm ((f^[k]) (Cseg j (r,z)).val)] at hh
      linarith only [h₁,h₂,hh]
    have hcoverTime (r : unitInterval) : ∃ j : Fin n, r ∈ I j := by
      by_contra hnone
      have hall (i : Fin (n+1)) : t i ≤ r ∧ (i ≠ 0 → t i < r) := by
        induction i using Fin.induction with
        | zero =>
          refine ⟨?_,fun hi ↦ False.elim (hi rfl)⟩
          rw [ht0]
          exact r.property.1
        | succ j ih =>
          have hj : t j.succ < r := lt_of_not_ge (fun hr ↦ hnone ⟨j,ih.1,hr⟩)
          exact ⟨hj.le,fun _ ↦ hj⟩
      have hlast : Fin.last n ≠ 0 := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_last,Fin.val_zero] at hv
        omega
      have hh := (hall (Fin.last n)).2 hlast
      rw [ht1] at hh
      exact not_lt_of_ge r.property.2 hh
    have hUniformPath : ∀ (ε : ℝ) (hε : 0 < ε),
        ∀ᶠ k : ℕ in atTop,
        ∀ z : W, ∀ r : unitInterval,
          m.dist ((f^[k]) (H (0,z.val))) ((f^[k]) (H (r,z.val))) < ε :=
      UniformPathBlock f hmetric hmetric_smooth hM a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels hTubeNormalSizeContinuous hTubeImageCenter speedCore hSpeedCoreCenter hSpeedCoverOpen hSpeedCoverCenter b hboxPoint hc R hR hRF T hcenter hproductBox hproductOpen hproductCoord hJ hpJ q x y γ e h hprefix W₀ hxW₀ hprefixSource hprefixContinuous hzero Vzero hH₀ n t ht0 ht1 ht assigned Nfam hsegments hN₀sub W hCommonSource hWcompact hH hSubpaths hStable hHseg hQ hQval hCseg hKseg hboxseg hQcoord hCseg_const m hm hshrink hdiam hcoverTime
    have hUniformOriginalPath (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop,
        ∀ z : W, ∀ r : unitInterval,
          m.dist ((f^[k]) z.val.val) ((f^[k]) (H (r,z.val))) < ε := by
      filter_upwards [hUniformPath ε hε] with k hk
      intro z r
      simpa only [hHzero] using hk z r
    have hHone (z : W) : H (1,z.val) = (h z.val).val := by
      have hh := L.identification.unstable_points (γ 1).val
        ((hprefix 1).map ((L.unstableClass (γ 0).val).symm z.val))
      change (L.holonomyRepresentative γ (hprefix 1) z.val).val = H (1,z.val) at hh
      exact hh.symm.trans (congrArg Subtype.val (hFinalOn z.val z.property).symm)
    have hCoverTail (C : M → Set M) (hCo : ∀ p, IsOpen (C p))
        (hCp : ∀ p, p ∈ C p) : ∀ᶠ k : ℕ in atTop,
        ∀ z : W, ∃ p : M, ∀ r : unitInterval, (f^[k]) (H (r,z.val)) ∈ C p := by
      have hcm : @IsCompact M m.toUniformSpace.toTopologicalSpace univ := by
        rw [hmTop]
        exact isCompact_univ
      have hCo' : ∀ p, @IsOpen M m.toUniformSpace.toTopologicalSpace (C p) := by
        intro p
        rw [hmTop]
        exact hCo p
      obtain ⟨ε,hε,hballs⟩ := @lebesgue_number_lemma_of_metric M m.toPseudoMetricSpace
        univ M C hcm hCo' (by intro p _; exact mem_iUnion.mpr ⟨p,hCp p⟩)
      filter_upwards [hUniformOriginalPath ε hε] with k hk
      intro z
      obtain ⟨p,hp⟩ := hballs ((f^[k]) z.val.val) (mem_univ _)
      refine ⟨p,fun r ↦ hp ?_⟩
      change m.dist ((f^[k]) (H (r,z.val))) ((f^[k]) z.val.val) < ε
      rw [m.dist_comm]
      exact hk z r
    have hSmallTubeAndPhysicalEndpointData (C : M → Set M) (hCo : ∀ p, IsOpen (C p))
        (hCp : ∀ p, p ∈ C p) (η : M → ℝ) (hη : ∀ p, 0 < η p)
        (θ : M → ℝ) (hθ : ∀ p, 0 < θ p) :
        ∀ᶠ k : ℕ in atTop, ∀ z : W,
        ∃ p : M, ∃ q : tubeLabels p,
          q.val.val = (f^[k]) (h z.val).val ∧ q ∈ tubeGoodLabels p ∧ q.val ∈ speedCore p ∩
            (fixedTubeLabels p ∩ coefficientLabels p) ∧
          (∀ r : unitInterval, (f^[k]) (H (r,z.val)) ∈ (tubeChart p).source ∧
            tubeChart p ((f^[k]) (H (r,z.val))) ∈ (tubeInverse p q).target) ∧
          (∀ r : unitInterval, ‖(tubeInverse p q).symm
            (tubeChart p ((f^[k]) (H (r,z.val))))‖ < η p) ∧
          (∀ r : unitInterval,
            let v := (tubeInverse p q).symm (tubeChart p ((f^[k]) (H (r,z.val))))
            tubeNormalSize p ((q.val,v.1),v.2) < θ p) ∧
          (∀ r : unitInterval, (f^[k]) (H (r,z.val)) ∈ C p) ∧
          (tubeInverse p q).symm (tubeChart p ((f^[k]) (h z.val).val)) = 0 := by
      choose A hAo hpA hAsub hAsmall using fun p ↦ hSmallTubeAndPhysical p (η p) (hη p) (θ p) (hθ p)
      filter_upwards [hCoverTail (fun p ↦ (A p ∩ speedCover p) ∩ C p)
        (fun p ↦ ((hAo p).inter (hSpeedCoverOpen p)).inter (hCo p))
        (fun p ↦ ⟨⟨hpA p,hSpeedCoverCenter p⟩,hCp p⟩)] with k hk
      intro z
      obtain ⟨p,hpall⟩ := hk z
      have hp := fun r ↦ (hpall r).1
      obtain ⟨q,hq,heq⟩ := (hAsub p (hp 1).1).2
      have hqval : q.val.val = (f^[k]) (h z.val).val := by
        simpa only [hHone] using heq
      have hqA : q.val.val ∈ A p :=
        Eq.mpr (congrArg (fun x : M ↦ x ∈ A p) heq) (hp 1).1
      have hqK : q.val ∈ speedCore p ∩ (fixedTubeLabels p ∩ coefficientLabels p) := by
        obtain ⟨q',hq',heq'⟩ := (hp 1).2
        have he : q' = q.val := Subtype.ext (heq'.trans heq.symm)
        exact he ▸ interior_subset hq'
      refine ⟨p,q,hqval,hq,hqK,?_,?_,?_,fun r ↦ (hpall r).2,?_⟩
      · intro r
        refine ⟨(hAsub p (hp r).1).1.1,?_⟩
        rw [(hTubeInverse p q).2.1]
        exact (hAsub p (hp r).1).1.2
      · exact fun r ↦ (hAsmall p q hqA _ (hp r).1).1
      · exact fun r ↦ (hAsmall p q hqA _ (hp r).1).2
      · rw [← hqval]
        exact hTubeInverseAtZero p q hq
    let endpoint (k : ℕ) (z : W) (w : L.U ((f^[k]) (γ 1).val)) (ε : ℝ) : Prop :=
      let := nativeTopology ((f^[k]) (γ 1).val)
      let := nativeCharts ((f^[k]) (γ 1).val)
      intrinsicHermitianLeafEDist (r := (L.unstable ((f^[k]) (γ 1).val)).rank)
        (Subtype.val : L.U ((f^[k]) (γ 1).val) → M) hmetric
        (nativeIterate k (γ 1).val (h z.val)) w < ENNReal.ofReal ε ∧
      ∃ ξ : TangentBundle (realModel d) M,
        ξ ∈ riemannianExponentialDomain g ∧ ξ.proj = w.val ∧
        riemannianExponential g ξ = (f^[k]) z.val.val ∧
        Real.sqrt (g.inner ξ.proj ξ.2 ξ.2) < ε ∧
        ∀ v ∈ a.splitting.unstable.toDistribution ξ.proj, g.inner ξ.proj ξ.2 v = 0
    let localEndpoint (C : M → Set M) (k : ℕ) (z : W) (w : L.U ((f^[k]) (γ 1).val)) (ε : ℝ) : Prop :=
      ∃ p : M, ∃ q : tubeLabels p,
        q.val.val = (f^[k]) (h z.val).val ∧
        (f^[k]) z.val.val ∈ (tubeChart p).source ∧
        tubeChart p ((f^[k]) z.val.val) ∈ (tubeInverse p q).target ∧
        w.val = ((coherentU.family 2 p).family.plaque q.val).param
          (((tubeInverse p q).symm (tubeChart p ((f^[k]) z.val.val))).1) ∧
        tubeNormalSize p ((q.val,((tubeInverse p q).symm
          (tubeChart p ((f^[k]) z.val.val))).1),((tubeInverse p q).symm
          (tubeChart p ((f^[k]) z.val.val))).2) < ε ∧
        q.val.val ∈ C p ∧ (f^[k]) z.val.val ∈ C p
    have hLocalEndpointExists (C : M → Set M) (hCo : ∀ p, IsOpen (C p))
        (hCp : ∀ p, p ∈ C p) (ε : ℝ) (hε : 0 < ε) :
        ∀ᶠ k : ℕ in atTop, ∀ z : W, ∃ w, localEndpoint C k z w ε ∧ endpoint k z w ε := by
      let η (p : M) := min ((coherentU.family 2 p).family.radius / 2)
        (min (ε / speedBound p) (min (fixedTubeRadius p) (coefficientRadius p)))
      have hη (p : M) : 0 < η p := lt_min (half_pos (coherentU.family 2 p).family.radius_pos)
        (lt_min (div_pos hε (hSpeedBound p)) (lt_min (hFixedTubeRadius p) (hCoefficientRadius p)))
      filter_upwards [hSmallTubeAndPhysicalEndpointData C hCo hCp η hη
        (fun p ↦ min ε (fixedNormalRadius p / coefficientBound p))
        (fun p ↦ lt_min hε (div_pos (hFixedNormalRadius p) (hCoefficientBound p)))] with k hk
      intro z
      let yk := (f^[k]) (γ 1).val
      let := nativeTopology yk
      let := nativeCharts yk
      obtain ⟨p,q,hqval,hqgood,hqK,hqt,hqsmall,hqphysical,hqC,hqzero⟩ := hk z
      let v := ((tubeInverse p q).symm (tubeChart p ((f^[k]) z.val.val))).1
      have hvsmall : ‖v‖ < η p := by
        have hh := hqsmall 0
        rw [hHzero] at hh
        exact (norm_fst_le _).trans_lt hh
      have hv : v ∈ Metric.closedBall 0 ((coherentU.family 2 p).family.radius / 2) := by
        rw [Metric.mem_closedBall,dist_zero_right]
        exact (hvsmall.trans_le (min_le_left _ _)).le
      have hclass : @ForwardAsymptotic M originalAmbientMetric
          (f.symm : M → M) yk q.val.val := by
        rw [hqval]
        have hh := (nativeIterate k (γ 1).val (h z.val)).property
        change @ForwardAsymptotic M originalAmbientMetric (f.symm : M → M) yk
          (nativeIterate k (γ 1).val (h z.val)).val at hh
        have hval := L.iterateUnstable_points k (γ 1).val (h z.val)
        exact hval ▸ hh
      obtain ⟨l,hl,hlocal,hopen⟩ := hNativeLift p q.val yk hclass
      let w := l ⟨v,Metric.closedBall_subset_ball
        (half_lt_self (coherentU.family 2 p).family.radius_pos) hv⟩
      have hwval : w.val = ((coherentU.family 2 p).family.plaque q.val).param v :=
        hl ⟨v,Metric.closedBall_subset_ball
          (half_lt_self (coherentU.family 2 p).family.radius_pos) hv⟩
      have hzero : l ⟨0,Metric.mem_ball_self (coherentU.family 2 p).family.radius_pos⟩ =
          nativeIterate k (γ 1).val (h z.val) := by
        apply Subtype.ext
        exact (hl _).trans (((coherentU.family 2 p).family.plaque q.val).centered.trans
          (hqval.trans (L.iterateUnstable_points k (γ 1).val (h z.val)).symm))
      have hvOpen : v ∈ Metric.ball 0 ((coherentU.family 2 p).family.radius / 2) := by
        rw [Metric.mem_ball,dist_zero_right]
        exact hvsmall.trans_le (min_le_left _ _)
      have hb := hNativeRadialBound p q.val yk l hl hlocal (speedBound p)
        (hSpeed p q.val hqK.1) v hv
      rw [hzero] at hb
      have hxt : (f^[k]) z.val.val ∈ (tubeChart p).source ∧
          tubeChart p ((f^[k]) z.val.val) ∈ (tubeInverse p q).target := by
        simpa only [hHzero] using hqt 0
      have hphysical : tubeNormalSize p ((q.val,v),
          ((tubeInverse p q).symm (tubeChart p ((f^[k]) z.val.val))).2) < ε :=
        (show tubeNormalSize p ((q.val,v),
          ((tubeInverse p q).symm (tubeChart p ((f^[k]) z.val.val))).2) <
          min ε (fixedNormalRadius p / coefficientBound p) by
            simpa only [hHzero] using hqphysical 0).trans_le (min_le_left _ _)
      have hqC' : q.val.val ∈ C p := by
        rw [hqval]
        simpa only [hHone] using hqC 1
      have hxC : (f^[k]) z.val.val ∈ C p := by
        simpa only [hHzero] using hqC 0
      refine ⟨w,⟨p,q,hqval,hxt.1,hxt.2,hwval,hphysical,hqC',hxC⟩,hb.trans_lt ?_,?_⟩
      · apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
        simpa only [mul_comm] using (lt_div_iff₀ (hSpeedBound p)).mp
          (hvsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      · obtain ⟨ξ,hdom,hbase,hexp,hsize,hnormal⟩ :=
          hTubePhysicalReconstruction p q ((f^[k]) z.val.val) hxt.1 hxt.2
        refine ⟨ξ,hdom,hbase.trans hwval.symm,hexp,?_,hnormal⟩
        rw [hsize]
        exact hphysical
    have hEndpointExists (ε : ℝ) (hε : 0 < ε) :
        ∀ᶠ k : ℕ in atTop, ∀ z : W, ∃ w, endpoint k z w ε :=
      (hLocalEndpointExists (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ mem_univ _) ε hε).mono (fun k hk z ↦
        ⟨(hk z).choose,(hk z).choose_spec.2⟩)
    have hEndpointMono {k : ℕ} {z : W} {w : L.U ((f^[k]) (γ 1).val)}
        {ε ε' : ℝ} (he : endpoint k z w ε) (hle : ε ≤ ε') : endpoint k z w ε' := by
      obtain ⟨hd,ξ,hdom,hbase,hexp,hsize,hnormal⟩ := he
      exact ⟨hd.trans_le (ENNReal.ofReal_le_ofReal hle),ξ,hdom,hbase,hexp,
        hsize.trans_le hle,hnormal⟩
    let endpointRadius := min normalBaseRadius normalSizeRadius / 2
    have hEndpointRadius : 0 < endpointRadius :=
      half_pos (lt_min hNormalBaseRadius hNormalSizeRadius)
    have hEndpointBase : endpointRadius < normalBaseRadius :=
      (half_lt_self (lt_min hNormalBaseRadius hNormalSizeRadius)).trans_le (min_le_left _ _)
    have hEndpointSize : endpointRadius < normalSizeRadius :=
      (half_lt_self (lt_min hNormalBaseRadius hNormalSizeRadius)).trans_le (min_le_right _ _)
    have hEndpointUnique {k : ℕ} {z : W} {w w' : L.U ((f^[k]) (γ 1).val)}
        (hw : endpoint k z w endpointRadius) (hw' : endpoint k z w' endpointRadius) : w = w' := by
      obtain ⟨hd,ξ,hdom,hbase,hexp,hsize,hnormal⟩ := hw
      obtain ⟨hd',ζ,hdom',hbase',hexp',hsize',hnormal'⟩ := hw'
      exact hNormalUnique ((f^[k]) (γ 1).val)
        (nativeIterate k (γ 1).val (h z.val)) w w'
        (hd.trans_le (ENNReal.ofReal_le_ofReal hEndpointBase.le))
        (hd'.trans_le (ENNReal.ofReal_le_ofReal hEndpointBase.le))
        ξ ζ hbase hbase' (hsize.trans hEndpointSize) (hsize'.trans hEndpointSize)
        hnormal hnormal' (hexp.trans hexp'.symm)
    obtain ⟨projection,hProjectionSmall⟩ := unique_small_selection_g18
      (X := fun _ : ℕ ↦ W) (Y := fun k ↦ L.U ((f^[k]) (γ 1).val)) atTop
      (fun k (z : W) ↦ nativeIterate k (γ 1).val (h z.val)) endpoint
      (fun _ _ _ _ _ he hle ↦ hEndpointMono he hle)
      endpointRadius hEndpointRadius
      (fun _ _ _ _ he he' ↦ hEndpointUnique he he') hEndpointExists
    let selected (k : ℕ) : L.U (γ 0).val → L.U ((f^[k]) (γ 1).val) := fun z ↦
      if hz : z ∈ W then projection k ⟨z,hz⟩ else nativeIterate k (γ 1).val (h z)
    let expanded (k : ℕ) : L.U ((f^[k]) (γ 0).val) → L.U ((f^[k]) (γ 1).val) :=
      fun z ↦ selected k ((nativeIterate k (γ 0).val).symm z)
    have hWsource : W ⊆ h.source := fun z hz ↦ (hWN hz).1.2
    have hExpandedLocalFormula (C : M → Set M) (hCo : ∀ p, IsOpen (C p))
        (hCp : ∀ p, p ∈ C p) : ∀ᶠ k : ℕ in atTop,
        letI := nativeTopology ((f^[k]) (γ 0).val)
        letI := nativeCharts ((f^[k]) (γ 0).val)
        letI := nativeTopology ((f^[k]) (γ 1).val)
        letI := nativeCharts ((f^[k]) (γ 1).val)
        ∀ (z : L.U ((f^[k]) (γ 0).val)),
          z ∈ nativeIterate k (γ 0).val '' interior W →
          ∃ p : M, ∃ q : tubeLabels p,
            q.val.val ∈ C p ∧ z.val ∈ C p ∧ z.val ∈ (tubeChart p).source ∧
            tubeChart p z.val ∈ (tubeInverse p q).target ∧
            ContMDiffAt (L.uModel ((f^[k]) (γ 0).val))
              (L.uModel ((f^[k]) (γ 1).val)) 1 (expanded k) z ∧
            (fun z : L.U ((f^[k]) (γ 0).val) ↦ ((expanded k z).val,tubeChart p (expanded k z).val)) =ᶠ[𝓝 z]
              (fun z : L.U ((f^[k]) (γ 0).val) ↦ tubeProjectionPair p q z.val) := by
      have hquarter : endpointRadius / 4 < endpointRadius :=
        div_lt_self hEndpointRadius (by norm_num)
      filter_upwards [hLocalEndpointExists C hCo hCp (endpointRadius / 4) (by positivity),
        hProjectionSmall endpointRadius hEndpointRadius] with k hloc hsel
      let xk := (f^[k]) (γ 0).val
      let yk := (f^[k]) (γ 1).val
      let := nativeTopology xk
      let := nativeCharts xk
      let := nativeTopology yk
      let := nativeCharts yk
      let ix := nativeIterate k (γ 0).val
      let Wk : Set (L.U xk) := ix.symm ⁻¹' W
      have hiterateVal (z : L.U xk) : (f^[k]) (ix.symm z).val = z.val := by
        exact (L.iterateUnstable_points k (γ 0).val (ix.symm z)).symm.trans
          (congrArg (fun w : L.U xk ↦ w.val) (ix.apply_symm_apply z))
      intro z₀ hz₀
      have huInterior : ix.symm z₀ ∈ interior W := by
        obtain ⟨u,hu,huz⟩ := hz₀
        rw [← huz,ix.symm_apply_apply]
        exact hu
      have huW : ix.symm z₀ ∈ W := interior_subset huInterior
      have hzInterior : z₀ ∈ interior Wk :=
        preimage_interior_subset_interior_preimage ix.symm.continuous huInterior
      obtain ⟨w,⟨p,q,hqval,hchart,htarget,hwval,hsize₀,hqC,hxC⟩,hw⟩ :=
        hloc ⟨ix.symm z₀,huW⟩
      have hchart : z₀.val ∈ (tubeChart p).source := hiterateVal z₀ ▸ hchart
      have htarget : tubeChart p z₀.val ∈ (tubeInverse p q).target := hiterateVal z₀ ▸ htarget
      have hwval : w.val = ((coherentU.family 2 p).family.plaque q.val).param
          (((tubeInverse p q).symm (tubeChart p z₀.val)).1) := hiterateVal z₀ ▸ hwval
      have hsize₀ : tubeNormalSize p
          ((q.val,((tubeInverse p q).symm (tubeChart p z₀.val)).1),
            ((tubeInverse p q).symm (tubeChart p z₀.val)).2) < endpointRadius / 4 :=
        hiterateVal z₀ ▸ hsize₀
      have hxC : z₀.val ∈ C p := hiterateVal z₀ ▸ hxC
      have hclass : @ForwardAsymptotic M originalAmbientMetric
          (f.symm : M → M) yk q.val.val := by
        rw [hqval]
        have hh := (nativeIterate k (γ 1).val (h (ix.symm z₀))).property
        change @ForwardAsymptotic M originalAmbientMetric (f.symm : M → M) yk
          (nativeIterate k (γ 1).val (h (ix.symm z₀))).val at hh
        have hval := L.iterateUnstable_points k (γ 1).val (h (ix.symm z₀))
        exact hval ▸ hh
      obtain ⟨hO,ψ,hψ,hψval⟩ := hNativeLocalProjection p q yk hclass
      let O : Opens M := ⟨(tubeChart p).source ∩ (tubeChart p) ⁻¹' (tubeInverse p q).target,hO⟩
      let F : L.U xk → M := Subtype.val
      have hF : ContMDiff (L.uModel xk) (realModel d) ∞ F :=
        (L.unstable xk).inclusion_smooth
      let T : Opens (L.U xk) := ⟨F ⁻¹' O,hO.preimage hF.continuous⟩
      let t₀ : T := ⟨z₀,⟨hchart,htarget⟩⟩
      let F₁ : T → O := fun z ↦ ⟨F z.val,z.property⟩
      have hF₁ : ContMDiff (L.uModel xk) (realModel d) ∞ F₁ := by
        apply (ContMDiff.subtypeVal_comp_iff O F₁).mp
        exact hF.comp contMDiff_subtype_val
      let Ψ : T → L.U yk := ψ ∘ F₁
      have hΨ : ContMDiff (L.uModel xk) (L.uModel yk) 1 Ψ :=
        hψ.comp (hF₁.of_le (by simp))
      have hΨ₀ : Ψ t₀ = w := by
        apply Subtype.ext
        exact (hψval (F₁ t₀)).trans hwval.symm
      let anchor : T → L.U yk := fun z ↦ nativeIterate k (γ 1).val (h (ix.symm z.val))
      have hback : ContinuousAt (fun z : T ↦ ix.symm z.val) t₀ :=
        ContinuousAt.comp (g := ix.symm) (f := fun z : T ↦ z.val) (x := t₀)
          (ix.symm.continuous.continuousAt (x := z₀)) continuous_subtype_val.continuousAt
      have hhol : ContinuousAt (fun z : T ↦ h (ix.symm z.val)) t₀ :=
        ContinuousAt.comp (g := h) (f := fun z : T ↦ ix.symm z.val) (x := t₀)
          (h.continuousAt (hWsource huW)) hback
      have hanchor : ContinuousAt anchor t₀ :=
        ContinuousAt.comp (g := nativeIterate k (γ 1).val)
          (f := fun z : T ↦ h (ix.symm z.val)) (x := t₀)
          (nativeIterate k (γ 1).val).continuous.continuousAt hhol
      let distance : T → ENNReal := fun z ↦
        intrinsicHermitianLeafEDist (r := (L.unstable yk).rank)
          (Subtype.val : L.U yk → M) hmetric (anchor z) (Ψ z)
      have hdistance : ContinuousAt distance t₀ :=
        ContinuousAt.comp (x := t₀) (f := fun z : T ↦ (anchor z,Ψ z))
          (g := fun xy : L.U yk × L.U yk ↦
            intrinsicHermitianLeafEDist (r := (L.unstable yk).rank)
              (Subtype.val : L.U yk → M) hmetric xy.1 xy.2)
          (hNativeDistanceContinuous yk).continuousAt
          (hanchor.prodMk hΨ.continuous.continuousAt)
      have hdistance₀ : distance t₀ < ENNReal.ofReal endpointRadius := by
        change intrinsicHermitianLeafEDist _ hmetric _ (Ψ t₀) < _
        rw [hΨ₀]
        exact hw.1.trans_le (ENNReal.ofReal_le_ofReal hquarter.le)
      let inv : T → (Fin (coherentU.dimension 2 p) → ℝ) × tubeNormalSpace p :=
        fun z ↦ (tubeInverse p q).symm (tubeChart p (F z.val))
      have hFt : ContinuousAt (fun z : T ↦ F z.val) t₀ :=
        hF.continuous.continuousAt.comp continuous_subtype_val.continuousAt
      have hct : ContinuousAt (fun z : T ↦ tubeChart p (F z.val)) t₀ :=
        ContinuousAt.comp (g := tubeChart p) (f := fun z : T ↦ F z.val) (x := t₀)
          (by exact continuousAt_extChartAt' hchart) hFt
      have hinv : ContinuousAt inv t₀ :=
        ContinuousAt.comp (g := (tubeInverse p q).symm)
          (f := fun z : T ↦ tubeChart p (F z.val)) (x := t₀)
          ((tubeInverse p q).symm.continuousAt htarget) hct
      have hbase : (inv t₀).1 ∈ Metric.ball 0 (coherentU.family 2 p).family.radius :=
        ((hTubeInverse p q).2.2.2.2 _ ((tubeInverse p q).map_target htarget)).1.2
      let size : T → ℝ := fun z ↦ tubeNormalSize p ((q.val,(inv z).1),(inv z).2)
      have hsize : ContinuousAt size t₀ := by
        have hh := HPS.native_normal_size_at_point_g18 (coherentU.coherence 2 p) g
          ⟨p,(coherentU.family 2 p).family.center_mem⟩ q.val (inv t₀).1 hbase (inv t₀).2
        exact ContinuousAt.comp (x := t₀)
          (f := inv) (g := fun v ↦ tubeNormalSize p ((q.val,v.1),v.2)) hh hinv
      have hsize₀' : size t₀ < endpointRadius := hsize₀.trans hquarter
      let admissible : L.U xk → L.U yk → Prop := fun z w ↦
        ∀ hz : ix.symm z ∈ W, endpoint k ⟨ix.symm z,hz⟩ w endpointRadius
      have hchosen : ∀ z ∈ Wk, admissible z (expanded k z) := by
        intro z hz hz'
        dsimp only [expanded,selected]
        rw [dite_eq_left hz']
        exact hsel ⟨ix.symm z,hz'⟩
      have huniq : ∀ z ∈ Wk, ∀ w w', admissible z w → admissible z w' → w = w' := by
        intro z hz w w' hw hw'
        exact hEndpointUnique (hw hz) (hw' hz)
      have hcertificate : ∀ z : T, z.val ∈ Wk →
          distance z < ENNReal.ofReal endpointRadius → size z < endpointRadius →
          admissible z.val (Ψ z) := by
        intro z hz hd hs hz'
        refine ⟨hd,?_⟩
        have hsrc : F z.val ∈ (tubeChart p).source := z.property.1
        have htgt : tubeChart p (F z.val) ∈ (tubeInverse p q).target := z.property.2
        obtain ⟨ξ,hdom,hbase,hexp,hsize,hnormal⟩ :=
          hTubePhysicalReconstruction p q (F z.val) hsrc htgt
        refine ⟨ξ,hdom,hbase.trans (hψval (F₁ z)).symm,
          hexp.trans (hiterateVal z.val).symm,?_,hnormal⟩
        rw [hsize]
        exact hs
      refine ⟨p,q,hqC,hxC,hchart,htarget,?_⟩
      apply unique_local_smooth_formula_g18 (X := L.U xk) (Y := L.U yk)
        (Z := M × ComplexModel d) (L.uModel xk) (L.uModel yk)
        Wk (expanded k) admissible hchosen huniq T t₀ hzInterior Ψ hΨ
        distance size endpointRadius hdistance hsize hdistance₀ hsize₀' hcertificate
        (fun w : L.U yk ↦ (w.val,tubeChart p w.val))
        (fun z ↦ tubeProjectionPair p q z.val)
      intro z
      have hzbase : (inv z).1 ∈ Metric.ball 0 (coherentU.family 2 p).family.radius :=
        ((hTubeInverse p q).2.2.2.2 _ ((tubeInverse p q).map_target z.property.2)).1.2
      exact Prod.ext (hψval (F₁ z))
        ((congrArg (tubeChart p) (hψval (F₁ z))).trans
          ((coherentU.coherence 2 p).coordinate_eq q.val hzbase).symm)
    let tubePhysicalOperator (p : M) (q : tubeLabels p) (x y : M)
        (hx : x ∈ (tubeChart p).source) (hy : y ∈ (tubeChart p).source) :
        TangentSpace (realModel d) x →L[ℝ] TangentSpace (realModel d) y := by
      let tr := tubeTr p
      have hxtr : x ∈ tr.baseSet := by
        simpa only [tr,tubeTr,tubeChart,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
      have hytr : y ∈ tr.baseSet := by
        simpa only [tr,tubeTr,tubeChart,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hy
      exact (tr.continuousLinearEquivAt ℝ y hytr).symm.toContinuousLinearMap.comp
        ((fderiv ℝ (tubeProjectedCoordinate p q) (tubeChart p x)).comp
          (tr.continuousLinearEquivAt ℝ x hxtr).toContinuousLinearMap)
    let normIndex (k : ℕ) :=
      (nativeIterate k (γ 0).val '' interior W) ×
        (Fin (L.unstable ((f^[k]) (γ 0).val)).rank → ℝ)
    let sourceNorm (k : ℕ) (q : normIndex k) : ℝ :=
      let := nativeTopology ((f^[k]) (γ 0).val)
      let := nativeCharts ((f^[k]) (γ 0).val)
      leafPullbackHermitianNorm (L := L.U ((f^[k]) (γ 0).val))
        (r := (L.unstable ((f^[k]) (γ 0).val)).rank)
        (Subtype.val : L.U ((f^[k]) (γ 0).val) → M) hmetric q.1.val q.2
    let targetNorm (k : ℕ) (q : normIndex k) : ℝ :=
      let := nativeTopology ((f^[k]) (γ 0).val)
      let := nativeCharts ((f^[k]) (γ 0).val)
      let := nativeTopology ((f^[k]) (γ 1).val)
      let := nativeCharts ((f^[k]) (γ 1).val)
      leafPullbackHermitianNorm (L := L.U ((f^[k]) (γ 1).val))
        (r := (L.unstable ((f^[k]) (γ 1).val)).rank)
        (Subtype.val : L.U ((f^[k]) (γ 1).val) → M) hmetric (expanded k q.1.val)
        (mfderiv (L.uModel ((f^[k]) (γ 0).val))
          (L.uModel ((f^[k]) (γ 1).val)) (expanded k) q.1.val q.2)
    have hExpandedControl (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop,
        letI := nativeTopology ((f^[k]) (γ 0).val)
        letI := nativeCharts ((f^[k]) (γ 0).val)
        letI := nativeTopology ((f^[k]) (γ 1).val)
        letI := nativeCharts ((f^[k]) (γ 1).val)
        ∀ (z : L.U ((f^[k]) (γ 0).val))
          (hz : z ∈ nativeIterate k (γ 0).val '' interior W),
          (∀ v : TangentSpace (L.uModel ((f^[k]) (γ 0).val)) z,
            (1-ε)*sourceNorm k ⟨⟨z,hz⟩,v⟩ ≤ targetNorm k ⟨⟨z,hz⟩,v⟩ ∧
              targetNorm k ⟨⟨z,hz⟩,v⟩ ≤ (1+ε)*sourceNorm k ⟨⟨z,hz⟩,v⟩) ∧
          letI : ChartedSpace (ComplexModel 1) (L.U ((f^[k]) (γ 0).val)) :=
            (L.complexUnstable ((f^[k]) (γ 0).val)).charts
          letI : ChartedSpace (ComplexModel 1) (L.U ((f^[k]) (γ 1).val)) :=
            (L.complexUnstable ((f^[k]) (γ 1).val)).charts
          0 < LinearMap.det
            (fderiv ℝ ((chartAt (ComplexModel 1) (expanded k z)) ∘ expanded k ∘
              (chartAt (ComplexModel 1) z).symm) (chartAt (ComplexModel 1) z z)).toLinearMap := by
      exact ExpandedControlBlock f hmetric hmetric_smooth hM a hb ιs Ls rs ts cs ss Fs invS ιu Lu ru tu cu su Fu invU coherentU L tubeDomain tubeLabels tubeImage tubeInverse hTubeInverse complexDist complexBundle hComplexBundle hComplexReal complexFrame hComplexFrameLinear hNativeControl q x y γ h sourceOpen m projection hExpandedLocalFormula ε hε
    have hSourceNonneg : ∀ k q, 0 ≤ sourceNorm k q := fun _ _ ↦ Real.sqrt_nonneg _
    have hNormBounds (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop,
        ∀ q : normIndex k, (1-ε)*sourceNorm k q ≤ targetNorm k q ∧
          targetNorm k q ≤ (1+ε)*sourceNorm k q := by
      filter_upwards [hExpandedControl ε hε] with k hk
      let := nativeTopology ((f^[k]) (γ 0).val)
      let := nativeCharts ((f^[k]) (γ 0).val)
      let := nativeTopology ((f^[k]) (γ 1).val)
      let := nativeCharts ((f^[k]) (γ 1).val)
      intro q
      exact (hk q.1.val q.1.property).1 q.2
    obtain ⟨ε,hεnonneg,hεt,hεbound⟩ := uniform_multiplicative_null_error_g18
      atTop sourceNorm targetNorm hSourceNonneg hNormBounds
    have hExpandedOrientation : ∀ᶠ k : ℕ in atTop,
        letI := nativeTopology ((f^[k]) (γ 0).val)
        letI := nativeCharts ((f^[k]) (γ 0).val)
        letI := nativeTopology ((f^[k]) (γ 1).val)
        letI := nativeCharts ((f^[k]) (γ 1).val)
        ∀ z ∈ nativeIterate k (γ 0).val '' interior W,
          letI : ChartedSpace (ComplexModel 1) (L.U ((f^[k]) (γ 0).val)) :=
            (L.complexUnstable ((f^[k]) (γ 0).val)).charts
          letI : ChartedSpace (ComplexModel 1) (L.U ((f^[k]) (γ 1).val)) :=
            (L.complexUnstable ((f^[k]) (γ 1).val)).charts
          0 < LinearMap.det
            (fderiv ℝ ((chartAt (ComplexModel 1) (expanded k z)) ∘ expanded k ∘
              (chartAt (ComplexModel 1) z).symm) (chartAt (ComplexModel 1) z z)).toLinearMap := by
      filter_upwards [hExpandedControl 1 zero_lt_one] with k hk
      let := nativeTopology ((f^[k]) (γ 0).val)
      let := nativeCharts ((f^[k]) (γ 0).val)
      let := nativeTopology ((f^[k]) (γ 1).val)
      let := nativeCharts ((f^[k]) (γ 1).val)
      intro z hz
      exact (hk z hz).2
    have hPullbackSmall (ε : ℝ) (hε : 0 < ε) :
        letI := nativeTopology (γ 1).val
        letI := nativeCharts (γ 1).val
        ∀ᶠ k : ℕ in atTop, ∀ z : W,
          intrinsicHermitianLeafEDist (L := L.U (γ 1).val) (r := (L.unstable (γ 1).val).rank)
            (Subtype.val : L.U (γ 1).val → M) hmetric (h z.val)
              ((nativeIterate k (γ 1).val).symm (projection k z)) ≤ ENNReal.ofReal ε := by
      let := nativeTopology (γ 1).val
      let := nativeCharts (γ 1).val
      obtain ⟨C,expansion,hC,hexpansion,_,hInv⟩ := hAnosov
      filter_upwards [hProjectionSmall (ε / C) (div_pos hε hC),
        eventually_gt_atTop (0 : ℕ)] with k hk hkpos
      let yk : M := (f^[k]) (γ 1).val
      let := nativeTopology yk
      let := nativeCharts yk
      have hbound (z : M) (v : TangentSpace (realModel d) z)
          (hv : v ∈ a.splitting.unstable.toDistribution z) :
          givenHermitianNorm hmetric ((f.symm^[k]) z)
            (mfderiv (realModel d) (realModel d) (f.symm^[k]) z v) ≤
              C * givenHermitianNorm hmetric z v := by
        have hp : expansion ^ (-(k : ℤ)) ≤ 1 :=
          zpow_le_one_of_nonpos₀ hexpansion.le (neg_nonpos.mpr (Int.natCast_nonneg k))
        exact (hInv k hkpos z v hv).trans
          (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC.le hp) (Real.sqrt_nonneg _))
      have he (w : L.U yk) : ((nativeIterate k (γ 1).val).symm w).val =
          (f.symm^[k]) w.val := by
        have hh := L.iterateUnstable_points k (γ 1).val
          ((nativeIterate k (γ 1).val).symm w)
        have heq : w.val = (f^[k]) (((nativeIterate k (γ 1).val).symm w).val) :=
          (congrArg (fun v : L.U yk ↦ v.val)
            ((nativeIterate k (γ 1).val).apply_symm_apply w)).symm.trans hh
        have hinv : Function.LeftInverse f.symm f := f.symm_apply_apply
        exact ((congrArg (f.symm^[k]) heq).trans (hinv.iterate k _)).symm
      intro z
      have hc : intrinsicHermitianLeafEDist (L := L.U (γ 1).val)
          (r := (L.unstable (γ 1).val).rank) (Subtype.val : L.U (γ 1).val → M) hmetric
          ((nativeIterate k (γ 1).val).symm (nativeIterate k (γ 1).val (h z.val)))
          ((nativeIterate k (γ 1).val).symm (projection k z)) ≤
          ENNReal.ofReal C * intrinsicHermitianLeafEDist (L := L.U yk)
            (r := (L.unstable yk).rank) (Subtype.val : L.U yk → M) hmetric
            (nativeIterate k (γ 1).val (h z.val)) (projection k z) :=
        native_unstable_intrinsic_contraction f a.splitting.unstable.toDistribution
        yk (γ 1).val (L.unstable yk) (L.unstable (γ 1).val) hmetric k C hC hbound
        (nativeIterate k (γ 1).val).symm he
        (nativeIterate k (γ 1).val (h z.val)) (projection k z)
      rw [(nativeIterate k (γ 1).val).symm_apply_apply] at hc
      apply hc.trans
      calc
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal (ε / C) :=
          mul_le_mul' (le_refl (ENNReal.ofReal C)) (hk z).1.le
        _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hC.le]
          congr 1
          field_simp [hC.ne']
    have hPulledCoordinateError (ε : ℝ) (hε : 0 < ε) :
        ∀ᶠ k : ℕ in atTop, ∀ z : W,
          (nativeIterate k (γ 1).val).symm (projection k z) ∈ receivingChart.source ∧
          dist (receivingChart ((nativeIterate k (γ 1).val).symm (projection k z)))
            (receivingChart (h z.val)) < ε := by
      let := nativeTopology (γ 1).val
      let := nativeCharts (γ 1).val
      let : T2Space (L.U (γ 1).val) := (L.unstable (γ 1).val).hausdorff
      let : IsManifold (L.uModel (γ 1).val) ∞ (L.U (γ 1).val) :=
        (L.unstable (γ 1).val).smoothAtlas
      have hK : IsCompact (h '' W) := hWcompact.image_of_continuousOn
        (h.continuousOn.mono (fun z hz ↦ (hWN hz).1.2))
      have hKs : h '' W ⊆ receivingChart.source := by
        rintro _ ⟨z,hz,rfl⟩
        exact hReceivingOn z hz
      obtain ⟨η,hη,hcoord⟩ := intrinsic_compact_chart_error_g18
        (Z := L.U (γ 1).val) (r := (L.unstable (γ 1).val).rank)
        hmetric hmetric_smooth (Subtype.val : L.U (γ 1).val → M)
        (L.unstable (γ 1).val).inclusion_smooth
        (fun z ↦ ((L.unstable (γ 1).val).inclusion_immersion z).mfderiv_injective (by simp))
        receivingChart (h '' W) hK hKs ε hε
      filter_upwards [hPullbackSmall η hη] with k hk
      intro z
      exact hcoord (h z.val) (mem_image_of_mem h z.property)
        ((nativeIterate k (γ 1).val).symm (projection k z)) (hk z)
    let pulledMap (k : ℕ) (z : L.U (γ 0).val) : L.U (γ 1).val :=
      (nativeIterate k (γ 1).val).symm (selected k z)
    have hPulledExpanded (k : ℕ) (z : L.U (γ 0).val) :
        pulledMap k z = (nativeIterate k (γ 1).val).symm
          (expanded k (nativeIterate k (γ 0).val z)) := by
      dsimp only [expanded]
      rw [(nativeIterate k (γ 0).val).symm_apply_apply]
    let coordinateLimit : OpenPartialHomeomorph (ComplexModel 1) (ComplexModel 1) :=
      sourceChart.symm.trans (h.trans receivingChart)
    have hLimitDomain : coordinateBuffer ⊆ coordinateLimit.source := by
      intro z hz
      exact ⟨hz.1,(hWN (interior_subset hz.2)).1.2,
        hReceivingOn _ (interior_subset hz.2)⟩
    let coordinateMap (k : ℕ) : ComplexModel 1 → ComplexModel 1 :=
      fun z ↦ receivingChart (pulledMap k (sourceChart.symm z))
    have hCoordinateUniform : TendstoUniformlyOn coordinateMap coordinateLimit atTop
        (Metric.closedBall sourceCenter regularRadius) := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro η hη
      filter_upwards [hPulledCoordinateError η hη] with k hk
      intro z hz
      have hzw : sourceChart.symm z ∈ W := interior_subset (hRegularBuffer hz).2
      have hpull : pulledMap k (sourceChart.symm z) =
          (nativeIterate k (γ 1).val).symm (projection k ⟨sourceChart.symm z,hzw⟩) :=
        congrArg (nativeIterate k (γ 1).val).symm (dite_eq_left hzw)
      exact (dist_comm _ _).trans_lt
        ((congrArg (fun w ↦ dist (receivingChart w) (receivingChart (h (sourceChart.symm z))))
          hpull).trans_lt (hk ⟨sourceChart.symm z,hzw⟩).2)
    have hCoordinateRegular : ∀ᶠ k : ℕ in atTop,
        ContDiffOn ℝ 1 (coordinateMap k) coordinateBuffer ∧
          ∀ z ∈ coordinateBuffer, 0 < (fderiv ℝ (coordinateMap k) z).det := by
      filter_upwards [hExpandedLocalFormula (fun _ ↦ univ) (fun _ ↦ isOpen_univ)
        (fun _ ↦ mem_univ _),hExpandedOrientation,hPulledCoordinateError 1 zero_lt_one]
        with k hs ho ht
      let xk := (f^[k]) (γ 0).val
      let yk := (f^[k]) (γ 1).val
      let := nativeTopology xk
      let := nativeCharts xk
      let := nativeTopology yk
      let := nativeCharts yk
      let : IsManifold (L.uModel xk) ∞ (L.U xk) := (L.unstable xk).smoothAtlas
      let : IsManifold (L.uModel yk) ∞ (L.U yk) := (L.unstable yk).smoothAtlas
      have hsm (z : L.U xk) (hz : z ∈ nativeIterate k (γ 0).val '' interior W) :
          ContMDiffAt (L.uModel xk) (L.uModel yk) 1 (expanded k) z := by
        obtain ⟨p,q,_,_,_,_,hsm,_⟩ := hs z hz
        exact hsm
      let : ChartedSpace (ComplexModel 1) (L.U (γ 0).val) := (L.complexUnstable (γ 0).val).charts
      let : ChartedSpace (ComplexModel 1) (L.U (γ 1).val) := (L.complexUnstable (γ 1).val).charts
      let : ChartedSpace (ComplexModel 1) (L.U xk) := (L.complexUnstable xk).charts
      let : ChartedSpace (ComplexModel 1) (L.U yk) := (L.complexUnstable yk).charts
      let : IsManifold (complexModel 1) ∞ (L.U (γ 0).val) := (L.complexUnstable (γ 0).val).complex_manifold
      let : IsManifold (complexModel 1) ∞ (L.U (γ 1).val) := (L.complexUnstable (γ 1).val).complex_manifold
      let : IsManifold (complexModel 1) ∞ (L.U xk) := (L.complexUnstable xk).complex_manifold
      let : IsManifold (complexModel 1) ∞ (L.U yk) := (L.complexUnstable yk).complex_manifold
      let eX := (nativeIterate k (γ 0).val).symm.toHomeomorph.toOpenPartialHomeomorph.trans sourceChart
      let eY := (nativeIterate k (γ 1).val).symm.toHomeomorph.toOpenPartialHomeomorph.trans receivingChart
      have hX := holomorphic_pullback_chart_g18 (nativeIterate k (γ 0).val).toHomeomorph
        (native_unstable_iterate_holomorphic L k (γ 0).val).1
        (native_unstable_iterate_holomorphic L k (γ 0).val).2 sourceChart
        (IsManifold.subset_maximalAtlas (I := complexModel 1) (n := ∞) hSourceChart)
      have hY := holomorphic_pullback_chart_g18 (nativeIterate k (γ 1).val).toHomeomorph
        (native_unstable_iterate_holomorphic L k (γ 1).val).1
        (native_unstable_iterate_holomorphic L k (γ 1).val).2 receivingChart
        (IsManifold.chart_mem_maximalAtlas (I := complexModel 1) (n := ∞) (L.uPoint (γ 1).val))
      have hmem (z : ComplexModel 1) (hz : z ∈ coordinateBuffer) :
          eX.symm z ∈ nativeIterate k (γ 0).val '' interior W :=
        ⟨sourceChart.symm z,hz.2,rfl⟩
      have hguard (z : ComplexModel 1) (hz : z ∈ coordinateBuffer) :
          z ∈ eX.target ∧ expanded k (eX.symm z) ∈ eY.source := by
        constructor
        · exact ⟨hz.1,mem_univ _⟩
        · refine ⟨mem_univ _,?_⟩
          have hw : sourceChart.symm z ∈ W := interior_subset hz.2
          have hpull : pulledMap k (sourceChart.symm z) =
              (nativeIterate k (γ 1).val).symm (projection k ⟨sourceChart.symm z,hw⟩) :=
            congrArg (nativeIterate k (γ 1).val).symm (dite_eq_left hw)
          change (nativeIterate k (γ 1).val).symm
            (expanded k (nativeIterate k (γ 0).val (sourceChart.symm z))) ∈ receivingChart.source
          rw [← hPulledExpanded,hpull]
          exact (ht ⟨sourceChart.symm z,hw⟩).1
      have hregular := positive_in_holomorphic_charts_on_g18 eX eY hX hY
        (expanded k) coordinateBuffer hguard
        (fun z hz ↦ native_upgrade_real_c1_at_g18 (X := L.U xk) (Y := L.U yk) (M := M)
          (rx := (L.unstable xk).rank) (ry := (L.unstable yk).rank) (n := 1) (d := d)
          (Subtype.val : L.U xk → M) (Subtype.val : L.U yk → M)
          (L.complexUnstable xk) (L.complexUnstable yk) (expanded k) (eX.symm z)
          (hsm _ (hmem z hz))) (fun z hz ↦ ho _ (hmem z hz))
      have heq : eY ∘ expanded k ∘ eX.symm = coordinateMap k := by
        funext z
        exact congrArg receivingChart (hPulledExpanded k (sourceChart.symm z)).symm
      exact heq ▸ hregular
    have hCoordinateInjective : ∀ᶠ k : ℕ in atTop,
        InjOn (coordinateMap k) (Metric.closedBall sourceCenter degreeRadius) := by
      exact eventually_complex_buffered_disk_comparison_injective_g18
        sourceCenter regularRadius (hSourceRadius.trans (hSourceDegree.trans hDegreeRegular))
        coordinateBuffer hCoordinateBufferOpen hRegularBuffer coordinateMap coordinateLimit
        (coordinateLimit.continuousOn.mono (hRegularBuffer.trans hLimitDomain))
        coordinateLimit.source coordinateLimit.target coordinateLimit.open_source
        coordinateLimit.open_target coordinateLimit.toHomeomorphSourceTarget
        (hRegularBuffer.trans hLimitDomain) (fun _ ↦ rfl)
        (Metric.closedBall sourceCenter degreeRadius) (isCompact_closedBall _ _)
        (Metric.closedBall_subset_ball hDegreeRegular) hCoordinateUniform hCoordinateRegular
    let intrinsicError (k : ℕ) (z : W) : ENNReal :=
      let := nativeTopology ((f^[k]) (γ 1).val)
      let := nativeCharts ((f^[k]) (γ 1).val)
      intrinsicHermitianLeafEDist (L := L.U ((f^[k]) (γ 1).val))
        (r := (L.unstable ((f^[k]) (γ 1).val)).rank)
        (Subtype.val : L.U ((f^[k]) (γ 1).val) → M) hmetric (nativeIterate k (γ 1).val (h z.val)) (projection k z)
    have hIntrinsicErrorSmall (ε : ℝ) (hε : 0 < ε) :
        ∀ᶠ k : ℕ in atTop, ∀ z : W, intrinsicError k z ≤ ENNReal.ofReal ε := by
      filter_upwards [hProjectionSmall ε hε] with k hk
      intro z
      exact (hk z).1.le
    obtain ⟨δ,hδnonneg,hδt,hδbound⟩ := uniform_ennreal_null_majorant_g18
      atTop intrinsicError hIntrinsicErrorSmall
    let originalComparisonOpen := sourceChart.symm '' Metric.ball sourceCenter degreeRadius
    have hDegreeBall : Metric.ball sourceCenter degreeRadius ⊆ coordinateBuffer :=
      (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall hDegreeRegular.le)).trans hRegularBuffer
    have hOriginalComparisonOpen : IsOpen originalComparisonOpen :=
      sourceChart.isOpen_image_symm_of_subset_target Metric.isOpen_ball
        (fun z hz ↦ (hDegreeBall hz).1)
    have hOriginalComparisonInterior : originalComparisonOpen ⊆ interior W := by
      rintro _ ⟨z,hz,rfl⟩
      exact (hDegreeBall hz).2
    have hOriginalComparisonTarget : Wtarget ⊆ originalComparisonOpen := by
      rw [hWtargetEq]
      exact Set.image_mono (Metric.closedBall_subset_ball hSourceDegree)
    refine ⟨ε,δ,hεnonneg,hδnonneg,hεt,hδt,?_⟩
    apply Filter.eventually_atTop.mp
    filter_upwards [hCoordinateInjective,hExpandedLocalFormula (fun _ ↦ univ)
      (fun _ ↦ isOpen_univ) (fun _ ↦ mem_univ _),hExpandedOrientation,hεbound,hδbound]
      with k hinj hs ho hn hd
    let xk := (f^[k]) (γ 0).val
    let yk := (f^[k]) (γ 1).val
    let := nativeTopology xk
    let := nativeCharts xk
    let := nativeTopology yk
    let := nativeCharts yk
    let : IsManifold (L.uModel xk) ∞ (L.U xk) := (L.unstable xk).smoothAtlas
    let : IsManifold (L.uModel yk) ∞ (L.U yk) := (L.unstable yk).smoothAtlas
    let : Nonempty (L.U xk) := ⟨L.uPoint xk⟩
    let O := nativeIterate k (γ 0).val '' originalComparisonOpen
    have hO : IsOpen O := (nativeIterate k (γ 0).val).toHomeomorph.isOpenMap _ hOriginalComparisonOpen
    have hOsub : O ⊆ nativeIterate k (γ 0).val '' interior W :=
      Set.image_mono hOriginalComparisonInterior
    have hWkO : nativeIterate k (γ 0).val '' Wtarget ⊆ O :=
      Set.image_mono hOriginalComparisonTarget
    have hC1 : ContMDiffOn (L.uModel xk) (L.uModel yk) 1 (expanded k) O := by
      intro z hz
      obtain ⟨p,q,_,_,_,_,hsm,_⟩ := hs z (hOsub hz)
      exact hsm.contMDiffWithinAt
    have hInj : InjOn (expanded k) O := by
      rintro _ ⟨u,⟨a,ha,rfl⟩,rfl⟩ _ ⟨v,⟨b,hb,rfl⟩,rfl⟩ he
      apply congrArg (nativeIterate k (γ 0).val)
      apply congrArg sourceChart.symm
      apply hinj (Metric.ball_subset_closedBall ha) (Metric.ball_subset_closedBall hb)
      change receivingChart (pulledMap k (sourceChart.symm a)) =
        receivingChart (pulledMap k (sourceChart.symm b))
      rw [hPulledExpanded,hPulledExpanded]
      exact congrArg (fun w ↦ receivingChart ((nativeIterate k (γ 1).val).symm w)) he
    obtain ⟨piMap,hpiMapO,hpiMap,hpiMapsmooth,hpiMapinverse⟩ :=
      native_positive_injective_c1_partial_homeomorph_g18
        (X := L.U xk) (Y := L.U yk) (M := M)
        (rx := (L.unstable xk).rank) (ry := (L.unstable yk).rank) (n := 1) (d := d)
        (Subtype.val : L.U xk → M) (Subtype.val : L.U yk → M)
        (L.complexUnstable xk) (L.complexUnstable yk) (expanded k) O hO hC1 hInj
        (fun z hz ↦ ho z (hOsub hz))
    have hWkSource : nativeIterate k (γ 0).val '' Wtarget ⊆ piMap.source := by
      rw [hpiMapO]
      exact hWkO
    refine ⟨piMap,hWkSource,hpiMapsmooth,hpiMapinverse,?_,?_,?_,?_⟩
    · exact piMap.injOn.mono hWkSource
    · intro z hz
      rw [hpiMap]
      exact ho z (hOsub (hWkO hz))
    · intro z hz v
      rw [hpiMap]
      exact hn ⟨⟨z,hOsub (hWkO hz)⟩,v⟩
    · rintro _ ⟨z,hz,rfl⟩
      have hzW : z ∈ W := interior_subset (hTargetInterior hz)
      have hexpanded : expanded k (nativeIterate k (γ 0).val z) = projection k ⟨z,hzW⟩ := by
        dsimp only [expanded,selected]
        rw [(nativeIterate k (γ 0).val).symm_apply_apply,dite_eq_left hzW]
      change intrinsicHermitianLeafEDist (L := L.U yk) (r := (L.unstable yk).rank)
        (Subtype.val : L.U yk → M) hmetric (piMap (nativeIterate k (γ 0).val z))
        (nativeIterate k (γ 1).val (h ((nativeIterate k (γ 0).val).symm
          (nativeIterate k (γ 0).val z)))) ≤ ENNReal.ofReal (δ k)
      rw [hpiMap,hexpanded,(nativeIterate k (γ 0).val).symm_apply_apply,
        IntrinsicPiecewiseC1Path.intrinsicHermitianLeafEDist_comm]
      exact hd ⟨z,hzW⟩

end OriginalStatement

end
end HolomorphicAnosov.Ghys

