import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! Intrinsic metric confinement in unstable plaque charts. (Ghys, Prop. 2.2) -/

open Manifold MeasureTheory
namespace HolomorphicAnosov.Ghys
open Set Filter TopologicalSpace _root_.Topology
open scoped ContDiff Manifold Bundle _root_.Topology
noncomputable section
universe u
attribute [local instance] complex_isManifold_real
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

set_option backward.isDefEq.respectTransparency false in
/-- An intrinsic leaf ball of radius `lowerBound p * R` lies in the unstable plaque chart,
with coordinate norm less than `R`. (Ghys, Prop. 2.2) -/
theorem NativeConfinementBlock {d : ℕ} {M : Type u} [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : CompactSpace M] [inst_4 : ChartedSpace (ComplexModel d) M] [inst_5 : IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M) (hmetric : HermitianTangentMetricCore d M) (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric) : let this_1 : MetricSpace M := rankComparisonMetric (d := d);
  Nonempty M →
  let originalAmbientMetric : MetricSpace M := inferInstance;
  let g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d) fun (x : M) => TangentSpace (realModel d) x := StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth;
  ∀ (a : AnosovDatum f), a.metric = g →
  Nonempty (TensorAnosovBounds f.toReal a.splitting (StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth)) →
  ∀ (ιs : Type u) (Ls : ιs → Type u) (rs : ιs → ℕ) (ts : (i : ιs) → TopologicalSpace (Ls i)) (cs : (i : ιs) → ChartedSpace (Fin (rs i) → ℝ) (Ls i)) (ss : ∀ (i : ιs), IsManifold 𝓘(ℝ, Fin (rs i) → ℝ) ∞ (Ls i)) (Fs : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls rs), (∃ (β : Type u) (d_1 : β → ℕ) (T : β → Type u) (topT : (b : β) → TopologicalSpace (T b)), Nonempty (HPS.LaminationBoxes Fs β d_1 T)) →
  Nonempty (HPS.LeafDynamicalInvariance Fs f.toReal) →
  ∀ (familiesS : HPS.SelectedFiniteC1NativePlaqueFamilies Fs) (coherentS : HPS.SelectedFiniteOrderNativePlaqueFamilies Fs), HPS.SourceBoundDistanceOutput Fs familiesS coherentS f.toReal edist →
  ∀ (ιu : Type u) (Lu : ιu → Type u) (ru : ιu → ℕ) (tu : (i : ιu) → TopologicalSpace (Lu i)) (cu : (i : ιu) → ChartedSpace (Fin (ru i) → ℝ) (Lu i)) (su : ∀ (i : ιu), IsManifold 𝓘(ℝ, Fin (ru i) → ℝ) ∞ (Lu i)) (Fu : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu ru), (∃ (β : Type u) (d_1 : β → ℕ) (T : β → Type u) (topT : (b : β) → TopologicalSpace (T b)), Nonempty (HPS.LaminationBoxes Fu β d_1 T)) →
  Nonempty (HPS.LeafDynamicalInvariance Fu f.toReal) →
  ∀ (familiesU : HPS.SelectedFiniteC1NativePlaqueFamilies Fu) (coherentU : HPS.SelectedFiniteOrderNativePlaqueFamilies Fu) (L : RankOneNativeLeaves f a.splitting) (labelU : M → ιu) (discU : (x : M) → TopologicalSpace.Opens (Fin (ru (labelU x)) → ℝ)) (mapU : (x : M) → ↥(discU x) → M) (stagesU : HPS.NativeSourcePlaqueStages (fun (i : ιu) => (Fu.leaf i).inclusion) labelU f.toReal.symm discU mapU) (AU : HPS.DistanceLeafIdentification Fu f.toReal.symm edist), AU.label = labelU →
  (∀ (p₀ : M), let Φ : HPS.FiniteC1NativePlaqueFamily Fu p₀ (familiesU.dimension p₀) := familiesU.family p₀; Nonempty (HPS.SelectedFamilyGermRestriction (L := Lu) labelU discU mapU stagesU.center (familiesU.dimension p₀) Φ.family.centerDomain (TopologicalSpace.Opens.mk (Metric.ball (0) Φ.family.radius) (Metric.isOpen_ball)) (fun (z : Φ.family.centerDomain.Elem × ↥(TopologicalSpace.Opens.mk (Metric.ball (0) Φ.family.radius) (Metric.isOpen_ball))) => (Φ.family.plaque z.1).param z.2.val) (Subtype.mk (0) (Metric.mem_ball_self Φ.family.radius_pos))) ∧ ∀ (p : Φ.family.centerDomain.Elem), Φ.label p = labelU p.val) →
  (∀ (N : ℕ) (p₀ : M), let Φ : HPS.FiniteC1NativePlaqueFamily Fu p₀ (coherentU.dimension N p₀) := coherentU.family N p₀; Nonempty (HPS.SelectedFamilyGermRestriction (L := Lu) labelU discU mapU stagesU.center (coherentU.dimension N p₀) Φ.family.centerDomain (TopologicalSpace.Opens.mk (Metric.ball (0) Φ.family.radius) (Metric.isOpen_ball)) (fun (z : Φ.family.centerDomain.Elem × ↥(TopologicalSpace.Opens.mk (Metric.ball (0) Φ.family.radius) (Metric.isOpen_ball))) => (Φ.family.plaque z.1).param z.2.val) (Subtype.mk (0) (Metric.mem_ball_self Φ.family.radius_pos))) ∧ ∀ (p : Φ.family.centerDomain.Elem), Φ.label p = labelU p.val) →
  ∀ (tubeLabels : (p : M) → TopologicalSpace.Opens (coherentU.family (2) p).family.centerDomain.Elem), (∀ (p : M), Subtype.mk p (coherentU.family (2) p).family.center_mem ∈ tubeLabels p) →
  ∀ (tubeImage : M → Set (ComplexModel d)), (∀ (p : M), IsOpen (tubeImage p)) →
  ∀ (tubeInverse : (p : M) → ↥(tubeLabels p) → OpenPartialHomeomorph ((Fin (coherentU.dimension (2) p) → ℝ) × ↥(plaqueNormalSpace ((fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => originalMetricChartTensor_g18 g (coherentU.family (2) p).family.receivingAnchor ((coherentU.coherence (2) p).coordinate z.1 z.2)) (Subtype.mk p (coherentU.family (2) p).family.center_mem, 0)) ((fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => fderiv ℝ ((coherentU.coherence (2) p).coordinate z.1) z.2) (Subtype.mk p (coherentU.family (2) p).family.center_mem, 0)))) (ComplexModel d)), (∀ (p : M), ContinuousOn (fun (z : ↥(tubeLabels p) × ComplexModel d) => (tubeInverse p z.1).symm.toFun' z.2) (univ ×ˢ tubeImage p)) →
  ∀ (coefficientLabels : (p : M) → Set (coherentU.family (2) p).family.centerDomain.Elem), (∀ (p : M), coefficientLabels p ∈ 𝓝 (Subtype.mk p (coherentU.family (2) p).family.center_mem)) →
  ∀ (coefficientRadius : M → ℝ), (∀ (p : M), 0 < coefficientRadius p) →
  ∀ (fixedTubeRadius : M → ℝ), (∀ (p : M), 0 < fixedTubeRadius p) →
  ∀ (fixedTubeLabels : (p : M) → Set (coherentU.family (2) p).family.centerDomain.Elem), (∀ (p : M), fixedTubeLabels p ∈ 𝓝 (Subtype.mk p (coherentU.family (2) p).family.center_mem)) →
  let tubeChart : M →
  PartialEquiv M (ComplexModel d) := fun (p : M) => extChartAt (realModel d) (coherentU.family (2) p).family.receivingAnchor;
  let tubeTensor : (p : M) →
  (coherentU.family (2) p).family.centerDomain.Elem →
  (Fin (coherentU.dimension (2) p) → ℝ) →
  ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ := fun (p : M) (q : (coherentU.family (2) p).family.centerDomain.Elem) (v : Fin (coherentU.dimension (2) p) → ℝ) => originalMetricChartTensor_g18 g (coherentU.family (2) p).family.receivingAnchor ((coherentU.coherence (2) p).coordinate q v);
  let tubeDerivative : (p : M) →
  (coherentU.family (2) p).family.centerDomain.Elem →
  (Fin (coherentU.dimension (2) p) → ℝ) →
  (Fin (coherentU.dimension (2) p) → ℝ) →L[ℝ] ComplexModel d := fun (p : M) (q : (coherentU.family (2) p).family.centerDomain.Elem) (v : Fin (coherentU.dimension (2) p) → ℝ) => fderiv ℝ ((coherentU.coherence (2) p).coordinate q) v;
  let tubeNormalSpace : M →
  Submodule ℝ (ComplexModel d) := fun (p : M) => plaqueNormalSpace (tubeTensor p (Subtype.mk p (coherentU.family (2) p).family.center_mem) (0)) (tubeDerivative p (Subtype.mk p (coherentU.family (2) p).family.center_mem) (0));
  let tubeNormal : (p : M) →
  (coherentU.family (2) p).family.centerDomain.Elem →
  (Fin (coherentU.dimension (2) p) → ℝ) →
  ↥(tubeNormalSpace p) →L[ℝ] ComplexModel d := fun (p : M) (q : (coherentU.family (2) p).family.centerDomain.Elem) (v : Fin (coherentU.dimension (2) p) → ℝ) => plaqueNormalFrame (tubeTensor p q v) (tubeDerivative p q v) (tubeNormalSpace p).subtypeL;
  (∀ (p : M), have D : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ) → (Fin (coherentU.dimension (2) p) → ℝ) →L[ℝ] ComplexModel d := fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => fderiv ℝ ((coherentU.coherence (2) p).coordinate z.1) z.2; have b : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ) → ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ := fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => originalMetricChartTensor_g18 g (coherentU.family (2) p).family.receivingAnchor ((coherentU.coherence (2) p).coordinate z.1 z.2); let K : Submodule ℝ (ComplexModel d) := plaqueNormalSpace (b (Subtype.mk p (coherentU.family (2) p).family.center_mem, 0)) (D (Subtype.mk p (coherentU.family (2) p).family.center_mem, 0)); have N : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ) → ↥K →L[ℝ] ComplexModel d := fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => plaqueNormalFrame (b z) (D z) K.subtypeL; have size : ((coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) × ↥K → ℝ := fun (z : ((coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) × ↥K) => √(DFunLike.coe (DFunLike.coe (b z.1) (DFunLike.coe (N z.1) z.2)) (DFunLike.coe (N z.1) z.2)); ContinuousAt size ((Subtype.mk p (coherentU.family (2) p).family.center_mem, 0), 0) ∧ size ((Subtype.mk p (coherentU.family (2) p).family.center_mem, 0), 0) = 0) →
  (∀ (p : M), (tubeChart p).toFun p ∈ tubeImage p) →
  let tubeNormalSize : (p : M) →
  ((coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) × ↥(tubeNormalSpace p) →
  ℝ := fun (p : M) (z : ((coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) × ↥(tubeNormalSpace p)) => √(DFunLike.coe (DFunLike.coe (tubeTensor p z.1.1 z.1.2) (DFunLike.coe (tubeNormal p z.1.1 z.1.2) z.2)) (DFunLike.coe (tubeNormal p z.1.1 z.1.2) z.2));
  ∀ (speedCore : (p : M) → Set (coherentU.family (2) p).family.centerDomain.Elem), (∀ (p : M), speedCore p ∈ 𝓝 (Subtype.mk p (coherentU.family (2) p).family.center_mem)) →
  let speedCover : M →
  Set M := fun (p : M) => Subtype.val '' interior (speedCore p ∩ (fixedTubeLabels p ∩ coefficientLabels p));
  (∀ (p : M), IsOpen (speedCover p)) →
  (∀ (p : M), p ∈ speedCover p) →
  let this : ChartedSpace (Fin (L.stableDimension + 2) → ℝ) M := L.realAmbientCharts;
  
  ∀ (hNativeChart : ∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain)
      (x : M) (hclass : ForwardAsymptotic (f.symm : M → M) x q.val),
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
          ∃ center : L.U x, center.val = q.val ∧ center ∈ c.source ∧ c center = 0)
    (lowerBound : M → ℝ) (hLowerBound : ∀ p, 0 < lowerBound p)
    (hLower : ∀ p, ∀ q ∈ speedCore p,
      ∀ u ∈ Metric.closedBall (0 : Fin (coherentU.dimension 2 p) → ℝ)
        ((coherentU.family 2 p).family.radius / 2),
      ∀ v : Fin (coherentU.dimension 2 p) → ℝ,
        lowerBound p * ‖v‖ ≤ Real.sqrt
          ((StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth).inner
            (((coherentU.family 2 p).family.plaque q).param u)
            (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
              ((coherentU.family 2 p).family.plaque q).param u v)
            (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
              ((coherentU.family 2 p).family.plaque q).param u v)))
    (p : M) (q : (coherentU.family 2 p).family.centerDomain)
      (hqK : q ∈ speedCore p) (x : M)
      (hclass : ForwardAsymptotic (f.symm : M → M) x q.val)
      (R : ℝ) (hR : 0 < R)
      (hRδ : R < (coherentU.family 2 p).family.radius / 2),
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
                ((coherentU.family 2 p).family.plaque q).param (J (c y)) = y.val := by
  classical
  intro this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius fixedTubeRadius hFixedTubeRadius fixedTubeLabels hFixedTubeLabels tubeChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hTubeNormalSizeContinuous hTubeImageCenter tubeNormalSize speedCore hSpeedCoreCenter speedCover hSpeedCoverOpen hSpeedCoverCenter this hNativeChart lowerBound hLowerBound hLower p q hqK x hclass R hR hRδ
  letI := L.identification.unstableTopology x
  letI := L.identification.unstableCharts x
  letI : IsManifold (L.uModel x) ∞ (L.U x) := (L.unstable x).smoothAtlas
  letI : T2Space (L.U x) := (L.unstable x).hausdorff
  obtain ⟨J,c,hc,htarget,hinv,center,hcenter,hcsource,hc0⟩ := hNativeChart p q x hclass
  refine ⟨J,c,hc,center,hcenter,hcsource,hc0,?_⟩
  intro y hd
  let Φ := coherentU.family 2 p
  let P := Φ.family.plaque q
  let δ := Φ.family.radius / 2
  have hδ : δ < Φ.family.radius := half_lt_self Φ.family.radius_pos
  have hmaps : MapsTo J (Metric.ball (0 : Fin (L.unstable x).rank → ℝ) δ)
      (Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ) δ) := by
    intro v hv
    simpa only [Metric.mem_ball,dist_zero_right,J.norm_map] using hv
  have hJ : ContMDiff (L.uModel x) 𝓘(ℝ,Fin (coherentU.dimension 2 p) → ℝ) ∞ J :=
    contMDiff_iff_contDiff.mpr J.toContinuousLinearEquiv.contDiff
  have hP : ContMDiffOn 𝓘(ℝ,Fin (coherentU.dimension 2 p) → ℝ) (realModel d) ∞
      P.param (Metric.ball 0 δ) := P.smooth.mono (by
    intro u hu
    rw [Φ.family.domain_eq]
    exact Metric.ball_subset_ball hδ.le hu)
  have hcomp : ContMDiffOn (L.uModel x) (realModel d) ∞ (P.param ∘ J)
      (Metric.ball 0 δ) := hP.comp hJ.contMDiffOn hmaps
  have hlo : ∀ u ∈ Metric.ball (0 : Fin (L.unstable x).rank → ℝ) δ,
      ∀ w : Fin (L.unstable x).rank → ℝ,
        lowerBound p * ‖w‖ ≤ Real.sqrt (g.inner (P.param (J u))
          (mfderiv (L.uModel x) (realModel d) (P.param ∘ J) u w)
          (mfderiv (L.uModel x) (realModel d) (P.param ∘ J) u w)) := by
    intro u hu w
    have hchain := mfderiv_comp u
      ((hP.contMDiffAt (Metric.isOpen_ball.mem_nhds (hmaps hu))).mdifferentiableAt (by simp))
      (hJ.mdifferentiableAt (by simp))
    rw [hchain]
    have hder : mfderiv (L.uModel x) 𝓘(ℝ,Fin (coherentU.dimension 2 p) → ℝ) J u =
        J.toContinuousLinearEquiv.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact J.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.fderiv
    rw [hder]
    change lowerBound p * ‖w‖ ≤ Real.sqrt (g.inner (P.param (J u))
      (mfderiv 𝓘(ℝ,Fin (coherentU.dimension 2 p) → ℝ) (realModel d) P.param (J u) (J w))
      (mfderiv 𝓘(ℝ,Fin (coherentU.dimension 2 p) → ℝ) (realModel d) P.param (J u) (J w)))
    simpa only [J.norm_map] using hLower p q hqK (J u)
      (Metric.ball_subset_closedBall (hmaps hu)) (J w)
  obtain ⟨hy,hcy⟩ := native_plaque_intrinsic_ball_confinement (L := L.U x) (r := (L.unstable x).rank) hmetric hmetric_smooth
    (Subtype.val : L.U x → M) c hc (P.param ∘ J) δ R (lowerBound p)
    hR hRδ (hLowerBound p)
    (fun v hv ↦ by rw [htarget]; exact Metric.ball_subset_ball hδ.le (hmaps hv))
    hcomp (fun v hv ↦ (hinv v (Metric.ball_subset_ball hδ.le (hmaps hv))).symm)
    hlo hcsource hc0 hd
  refine ⟨hy,?_,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right,J.norm_map] using hcy
  · have htargety := c.map_source hy
    rw [htarget] at htargety
    have hh := hinv (c y) htargety
    rw [c.left_inv hy] at hh
    exact hh.symm


end
end HolomorphicAnosov.Ghys
