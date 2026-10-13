import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18
import Mathlib.Util.CountHeartbeats



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

#count_heartbeats in
set_option backward.isDefEq.respectTransparency false in
theorem NativeMetricLowerBoundsBlock : ∀ {d : ℕ} {M : Type u}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ChartedSpace (ComplexModel d) M] [inst_5 : IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M)
  (hmetric : HermitianTangentMetricCore d M) (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric),
  let this : MetricSpace M := rankComparisonMetric (d := d);
  Nonempty M →
    let originalAmbientMetric : MetricSpace M := inferInstance;
    let g :
      Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d) fun (x : M) => TangentSpace (realModel d) x :=
      StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth;
    ∀ (a : AnosovDatum f),
      a.metric = g →
        Nonempty
            (TensorAnosovBounds f.toReal a.splitting
              (StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth)) →
          ∀ (ιs : Type u) (Ls : ιs → Type u) (rs : ιs → ℕ) (ts : (i : ιs) → TopologicalSpace (Ls i))
            (cs : (i : ιs) → ChartedSpace (Fin (rs i) → ℝ) (Ls i))
            (ss : ∀ (i : ιs), IsManifold 𝓘(ℝ, Fin (rs i) → ℝ) ∞ (Ls i))
            (Fs : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls rs),
            (∃ (β : Type u) (d_1 : β → ℕ) (T : β → Type u) (topT : (b : β) → TopologicalSpace (T b)),
                Nonempty (HPS.LaminationBoxes Fs β d_1 T)) →
              Nonempty (HPS.LeafDynamicalInvariance Fs f.toReal) →
                ∀ (familiesS : HPS.SelectedFiniteC1NativePlaqueFamilies Fs)
                  (coherentS : HPS.SelectedFiniteOrderNativePlaqueFamilies Fs),
                  HPS.SourceBoundDistanceOutput Fs familiesS coherentS f.toReal edist →
                    ∀ (ιu : Type u) (Lu : ιu → Type u) (ru : ιu → ℕ) (tu : (i : ιu) → TopologicalSpace (Lu i))
                      (cu : (i : ιu) → ChartedSpace (Fin (ru i) → ℝ) (Lu i))
                      (su : ∀ (i : ιu), IsManifold 𝓘(ℝ, Fin (ru i) → ℝ) ∞ (Lu i))
                      (Fu : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu ru),
                      (∃ (β : Type u) (d_1 : β → ℕ) (T : β → Type u) (topT : (b : β) → TopologicalSpace (T b)),
                          Nonempty (HPS.LaminationBoxes Fu β d_1 T)) →
                        Nonempty (HPS.LeafDynamicalInvariance Fu f.toReal) →
                          ∀ (familiesU : HPS.SelectedFiniteC1NativePlaqueFamilies Fu)
                            (coherentU : HPS.SelectedFiniteOrderNativePlaqueFamilies Fu)
                            (L : RankOneNativeLeaves f a.splitting) (labelU : M → ιu)
                            (discU : (x : M) → TopologicalSpace.Opens (Fin (ru (labelU x)) → ℝ)) (mapU : (x : M) → ↥(discU x) → M)
                            (stagesU :
                              HPS.NativeSourcePlaqueStages (fun (i : ιu) => (Fu.leaf i).inclusion) labelU f.toReal.symm
                                discU mapU)
                            (AU : HPS.DistanceLeafIdentification Fu f.toReal.symm edist),
                            AU.label = labelU →
                              (∀ (p₀ : M),
                                  let Φ : HPS.FiniteC1NativePlaqueFamily Fu p₀ (familiesU.dimension p₀) :=
                                    familiesU.family p₀;
                                  Nonempty
                                      (HPS.SelectedFamilyGermRestriction (L := Lu) labelU discU mapU stagesU.center
                                        (familiesU.dimension p₀) Φ.family.centerDomain
                                        (TopologicalSpace.Opens.mk (Metric.ball (0) Φ.family.radius)
                                          (Metric.isOpen_ball))
                                        (fun
                                            (z :
                                              Φ.family.centerDomain.Elem ×
                                                ↥(TopologicalSpace.Opens.mk (Metric.ball (0) Φ.family.radius)
                                                    (Metric.isOpen_ball))) =>
                                          (Φ.family.plaque z.1).param z.2.val)
                                        (Subtype.mk (0)
                                          (Metric.mem_ball_self Φ.family.radius_pos))) ∧
                                    ∀ (p : Φ.family.centerDomain.Elem), Φ.label p = labelU p.val) →
                                (∀ (N : ℕ) (p₀ : M),
                                    let Φ : HPS.FiniteC1NativePlaqueFamily Fu p₀ (coherentU.dimension N p₀) :=
                                      coherentU.family N p₀;
                                    Nonempty
                                        (HPS.SelectedFamilyGermRestriction (L := Lu) labelU discU mapU stagesU.center
                                          (coherentU.dimension N p₀) Φ.family.centerDomain
                                          (TopologicalSpace.Opens.mk (Metric.ball (0) Φ.family.radius)
                                            (Metric.isOpen_ball))
                                          (fun
                                              (z :
                                                Φ.family.centerDomain.Elem ×
                                                  ↥(TopologicalSpace.Opens.mk (Metric.ball (0) Φ.family.radius)
                                                      (Metric.isOpen_ball))) =>
                                            (Φ.family.plaque z.1).param z.2.val)
                                          (Subtype.mk (0)
                                            (Metric.mem_ball_self Φ.family.radius_pos))) ∧
                                      ∀ (p : Φ.family.centerDomain.Elem), Φ.label p = labelU p.val) →
                                  ∀
                                    (tubeLabels :
                                      (p : M) →
                                        TopologicalSpace.Opens (coherentU.family (2) p).family.centerDomain.Elem),
                                    (∀ (p : M),
                                        Subtype.mk p (coherentU.family (2) p).family.center_mem ∈
                                          tubeLabels p) →
                                      ∀ (tubeImage : M → Set (ComplexModel d)),
                                        (∀ (p : M), IsOpen (tubeImage p)) →
                                          ∀
                                            (tubeInverse :
                                              (p : M) →
                                                ↥(tubeLabels p) →
                                                  OpenPartialHomeomorph
                                                    ((Fin (coherentU.dimension (2) p) → ℝ) ×
                                                      ↥(plaqueNormalSpace
                                                          ((fun
                                                                (z :
                                                                  (coherentU.family (2)
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension (2)
                                                                          p) →
                                                                      ℝ)) =>
                                                              originalMetricChartTensor_g18 g
                                                                (coherentU.family (2)
                                                                      p).family.receivingAnchor
                                                                ((coherentU.coherence (2)
                                                                      p).coordinate
                                                                  z.1 z.2))
                                                            (Subtype.mk p
                                                                (coherentU.family (2)
                                                                      p).family.center_mem,
                                                              0))
                                                          ((fun
                                                                (z :
                                                                  (coherentU.family (2)
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension (2)
                                                                          p) →
                                                                      ℝ)) =>
                                                              fderiv ℝ
                                                                ((coherentU.coherence (2)
                                                                      p).coordinate
                                                                  z.1)
                                                                z.2)
                                                            (Subtype.mk p
                                                                (coherentU.family (2)
                                                                      p).family.center_mem,
                                                              0))))
                                                    (ComplexModel d)),
                                            (∀ (p : M),
                                                ContinuousOn
                                                  (fun (z : ↥(tubeLabels p) × ComplexModel d) =>
                                                    (tubeInverse p z.1).symm.toFun' z.2)
                                                  (univ ×ˢ tubeImage p)) →
                                              ∀
                                                (coefficientLabels :
                                                  (p : M) →
                                                    Set
                                                      (coherentU.family (2)
                                                              p).family.centerDomain.Elem),
                                                (∀ (p : M),
                                                    coefficientLabels p ∈
                                                      𝓝
                                                        (Subtype.mk p
                                                          (coherentU.family (2)
                                                                p).family.center_mem)) →
                                                  ∀
                                                    (fixedTubeLabels :
                                                      (p : M) →
                                                        Set
                                                          (coherentU.family (2)
                                                                  p).family.centerDomain.Elem),
                                                    (∀ (p : M),
                                                        fixedTubeLabels p ∈
                                                          𝓝
                                                            (Subtype.mk p
                                                              (coherentU.family (2)
                                                                    p).family.center_mem)) →
                                                      let tubeChart : M → PartialEquiv M (ComplexModel d) :=
                                                        fun (p : M) =>
                                                        extChartAt (realModel d)
                                                          (coherentU.family (2)
                                                                p).family.receivingAnchor;
                                                      let tubeTensor :
                                                        (p : M) →
                                                          (coherentU.family (2)
                                                                    p).family.centerDomain.Elem →
                                                            (Fin (coherentU.dimension (2) p) →
                                                                ℝ) →
                                                              ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ :=
                                                        fun (p : M)
                                                          (q :
                                                            (coherentU.family (2)
                                                                    p).family.centerDomain.Elem)
                                                          (v :
                                                            Fin (coherentU.dimension (2) p) →
                                                              ℝ) =>
                                                        originalMetricChartTensor_g18 g
                                                          (coherentU.family (2)
                                                                p).family.receivingAnchor
                                                          ((coherentU.coherence (2) p).coordinate
                                                            q v);
                                                      let tubeDerivative :
                                                        (p : M) →
                                                          (coherentU.family (2)
                                                                    p).family.centerDomain.Elem →
                                                            (Fin (coherentU.dimension (2) p) →
                                                                ℝ) →
                                                              (Fin (coherentU.dimension (2) p) →
                                                                  ℝ) →L[ℝ]
                                                                ComplexModel d :=
                                                        fun (p : M)
                                                          (q :
                                                            (coherentU.family (2)
                                                                    p).family.centerDomain.Elem)
                                                          (v :
                                                            Fin (coherentU.dimension (2) p) →
                                                              ℝ) =>
                                                        fderiv ℝ
                                                          ((coherentU.coherence (2) p).coordinate
                                                            q)
                                                          v;
                                                      let tubeNormalSpace : M → Submodule ℝ (ComplexModel d) :=
                                                        fun (p : M) =>
                                                        plaqueNormalSpace
                                                          (tubeTensor p
                                                            (Subtype.mk p
                                                              (coherentU.family (2)
                                                                    p).family.center_mem)
                                                            (0))
                                                          (tubeDerivative p
                                                            (Subtype.mk p
                                                              (coherentU.family (2)
                                                                    p).family.center_mem)
                                                            (0));
                                                      let tubeNormal :
                                                        (p : M) →
                                                          (coherentU.family (2)
                                                                    p).family.centerDomain.Elem →
                                                            (Fin (coherentU.dimension (2) p) →
                                                                ℝ) →
                                                              ↥(tubeNormalSpace p) →L[ℝ] ComplexModel d :=
                                                        fun (p : M)
                                                          (q :
                                                            (coherentU.family (2)
                                                                    p).family.centerDomain.Elem)
                                                          (v :
                                                            Fin (coherentU.dimension (2) p) →
                                                              ℝ) =>
                                                        plaqueNormalFrame (tubeTensor p q v) (tubeDerivative p q v)
                                                          (tubeNormalSpace p).subtypeL;
                                                      (∀ (p : M),
                                                          have D :
                                                            (coherentU.family (2)
                                                                        p).family.centerDomain.Elem ×
                                                                (Fin (coherentU.dimension (2) p) →
                                                                  ℝ) →
                                                              (Fin (coherentU.dimension (2) p) →
                                                                  ℝ) →L[ℝ]
                                                                ComplexModel d :=
                                                            fun
                                                              (z :
                                                                (coherentU.family (2)
                                                                          p).family.centerDomain.Elem ×
                                                                  (Fin
                                                                      (coherentU.dimension (2)
                                                                        p) →
                                                                    ℝ)) =>
                                                            fderiv ℝ
                                                              ((coherentU.coherence (2)
                                                                    p).coordinate
                                                                z.1)
                                                              z.2;
                                                          have b :
                                                            (coherentU.family (2)
                                                                        p).family.centerDomain.Elem ×
                                                                (Fin (coherentU.dimension (2) p) →
                                                                  ℝ) →
                                                              ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ :=
                                                            fun
                                                              (z :
                                                                (coherentU.family (2)
                                                                          p).family.centerDomain.Elem ×
                                                                  (Fin
                                                                      (coherentU.dimension (2)
                                                                        p) →
                                                                    ℝ)) =>
                                                            originalMetricChartTensor_g18 g
                                                              (coherentU.family (2)
                                                                    p).family.receivingAnchor
                                                              ((coherentU.coherence (2)
                                                                    p).coordinate
                                                                z.1 z.2);
                                                          let K : Submodule ℝ (ComplexModel d) :=
                                                            plaqueNormalSpace
                                                              (b
                                                                (Subtype.mk p
                                                                    (coherentU.family (2)
                                                                          p).family.center_mem,
                                                                  0))
                                                              (D
                                                                (Subtype.mk p
                                                                    (coherentU.family (2)
                                                                          p).family.center_mem,
                                                                  0));
                                                          have N :
                                                            (coherentU.family (2)
                                                                        p).family.centerDomain.Elem ×
                                                                (Fin (coherentU.dimension (2) p) →
                                                                  ℝ) →
                                                              ↥K →L[ℝ] ComplexModel d :=
                                                            fun
                                                              (z :
                                                                (coherentU.family (2)
                                                                          p).family.centerDomain.Elem ×
                                                                  (Fin
                                                                      (coherentU.dimension (2)
                                                                        p) →
                                                                    ℝ)) =>
                                                            plaqueNormalFrame (b z) (D z) K.subtypeL;
                                                          have size :
                                                            ((coherentU.family (2)
                                                                          p).family.centerDomain.Elem ×
                                                                  (Fin
                                                                      (coherentU.dimension (2)
                                                                        p) →
                                                                    ℝ)) ×
                                                                ↥K →
                                                              ℝ :=
                                                            fun
                                                              (z :
                                                                ((coherentU.family (2)
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension (2)
                                                                          p) →
                                                                      ℝ)) ×
                                                                  ↥K) =>
                                                            √(DFunLike.coe
                                                                (DFunLike.coe (b z.1) (DFunLike.coe (N z.1) z.2))
                                                                (DFunLike.coe (N z.1) z.2));
                                                          ContinuousAt size
                                                              ((Subtype.mk p
                                                                    (coherentU.family (2)
                                                                          p).family.center_mem,
                                                                  0),
                                                                0) ∧
                                                            size
                                                                ((Subtype.mk p
                                                                      (coherentU.family (2)
                                                                            p).family.center_mem,
                                                                    0),
                                                                  0) =
                                                              0) →
                                                        (∀ (p : M), (tubeChart p).toFun p ∈ tubeImage p) →
                                                          let tubeNormalSize :
                                                            (p : M) →
                                                              ((coherentU.family (2)
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension (2)
                                                                          p) →
                                                                      ℝ)) ×
                                                                  ↥(tubeNormalSpace p) →
                                                                ℝ :=
                                                            fun (p : M)
                                                              (z :
                                                                ((coherentU.family (2)
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension (2)
                                                                          p) →
                                                                      ℝ)) ×
                                                                  ↥(tubeNormalSpace p)) =>
                                                            √(DFunLike.coe
                                                                (DFunLike.coe (tubeTensor p z.1.1 z.1.2)
                                                                  (DFunLike.coe (tubeNormal p z.1.1 z.1.2) z.2))
                                                                (DFunLike.coe (tubeNormal p z.1.1 z.1.2) z.2));
                                                          ∀
                                                            (speedCore :
                                                              (p : M) →
                                                                Set
                                                                  (coherentU.family (2)
                                                                          p).family.centerDomain.Elem),
                                                            (∀ (p : M), IsCompact (speedCore p)) →
                                                              (∀ (p : M),
                                                                  speedCore p ∈
                                                                    𝓝
                                                                      (Subtype.mk p
                                                                        (coherentU.family (2)
                                                                              p).family.center_mem)) →
                                                                ∀ (p : M),
                                                                  ∃ (c : ℝ),
                                                                    0 < c ∧
                                                                      ∀ q ∈ speedCore p,
                                                                        ∀
                                                                          u ∈
                                                                            Metric.closedBall (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                              ((coherentU.family
                                                                                      (2)
                                                                                      p).family.radius /
                                                                                2),
                                                                          ∀
                                                                            (v :
                                                                              Fin
                                                                                  (coherentU.dimension
                                                                                    (2) p) →
                                                                                ℝ),
                                                                            c * ‖v‖ ≤
                                                                              √(DFunLike.coe
                                                                                  (DFunLike.coe
                                                                                    (g.inner
                                                                                      (((coherentU.family
                                                                                                  (2)
                                                                                                  p).family.plaque
                                                                                            q).param
                                                                                        u))
                                                                                    (DFunLike.coe
                                                                                      (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
                                                                                          ((coherentU.family
                                                                                                    (2)
                                                                                                    p).family.plaque
                                                                                              q).param
                                                                                        u)
                                                                                      v))
                                                                                  (DFunLike.coe
                                                                                    (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
                                                                                        ((coherentU.family
                                                                                                  (2)
                                                                                                  p).family.plaque
                                                                                            q).param
                                                                                      u)
                                                                                    v)) := by
  intro d M inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 f hmetric hmetric_smooth this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels tubeChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hTubeNormalSizeContinuous hTubeImageCenter tubeNormalSize speedCore hSpeedCore hSpeedCoreCenter p
  let Φ := coherentU.family 2 p
  let V := Fin (coherentU.dimension 2 p) → ℝ
  rcases subsingleton_or_nontrivial V with hV | hV
  · letI := hV
    refine ⟨1,zero_lt_one,?_⟩
    intro q hq u hu v
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv,norm_zero,mul_zero]
    exact Real.sqrt_nonneg _
  letI := hV
  let B := Metric.closedBall (0 : V) (Φ.family.radius / 2)
  let X := speedCore p × B
  letI : CompactSpace (speedCore p) := isCompact_iff_compactSpace.mp (hSpeedCore p)
  letI : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  letI : Nonempty X := ⟨(⟨⟨p,Φ.family.center_mem⟩,mem_of_mem_nhds (hSpeedCoreCenter p)⟩,
    ⟨0,Metric.mem_closedBall_self (half_pos Φ.family.radius_pos).le⟩)⟩
  let base (z : X) := (Φ.family.plaque z.1.val).param z.2.val
  let D (z : X) := mfderiv 𝓘(ℝ,V) (realModel d) (Φ.family.plaque z.1.val).param z.2.val
  have hball (z : X) : z.2.val ∈ Metric.ball (0 : V) Φ.family.radius :=
    Metric.closedBall_subset_ball (half_lt_self Φ.family.radius_pos) z.2.property
  have hD : Continuous (fun z : X × V ↦
      (⟨base z.1,D z.1 z.2⟩ : TangentBundle (realModel d) M)) := by
    let j : X × V → (Φ.family.centerDomain × Metric.ball (0 : V) Φ.family.radius) × V :=
      fun z ↦ ((z.1.1.val,⟨z.1.2.val,hball z.1⟩),z.2)
    have hj : Continuous j := by
      dsimp only [j,X]
      fun_prop
    exact Φ.family.continuous_tangent_w04.comp hj
  have hDinj (z : X) : Function.Injective (D z) := by
    apply (Φ.family.plaque z.1.val).immersed
    rw [Φ.family.domain_eq]
    exact hball z
  obtain ⟨c,hc,hbound⟩ := Analysis.exists_uniform_metric_pullback_lower_bound g base D hD hDinj
  exact ⟨c,hc,fun q hq u hu v ↦ hbound (⟨q,hq⟩,⟨u,hu⟩) v⟩


end
end HolomorphicAnosov.Ghys
