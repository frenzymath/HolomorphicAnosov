import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! A bound `C` on the plaque derivative in the original metric gives an intrinsic
Hermitian leaf distance bound `C * ‖v‖` from the plaque center to a point with parameter
`v` in the closed half-radius ball. (Ghys, Prop. 2.2) -/

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
theorem NativeRadialBoundBlock {d : ℕ} {M : Type u}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ChartedSpace (ComplexModel d) M] [inst_5 : IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M)
  (hmetric : HermitianTangentMetricCore d M) (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric) :
  let this_1 : MetricSpace M := rankComparisonMetric (d := d);
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
                                                            (∀ (p : M),
                                                                speedCore p ∈
                                                                  𝓝
                                                                    (Subtype.mk p
                                                                      (coherentU.family (2)
                                                                            p).family.center_mem)) →
                                                              let speedCover : M → Set M := fun (p : M) =>
                                                                Subtype.val ''
                                                                  interior
                                                                    (speedCore p ∩
                                                                      (fixedTubeLabels p ∩ coefficientLabels p));
                                                              (∀ (p : M), IsOpen (speedCover p)) →
                                                                (∀ (p : M), p ∈ speedCover p) →
                                                                  let this :
                                                                    ChartedSpace
                                                                      (Fin
                                                                          (L.stableDimension +
                                                                            2) →
                                                                        ℝ)
                                                                      M :=
                                                                    L.realAmbientCharts;
                                                                  ∀ (p : M)
                                                                    (q :
                                                                      (coherentU.family (2)
                                                                              p).family.centerDomain.Elem)
                                                                    (x : M),
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
            (coherentU.family 2 p).family.radius_pos) hv⟩) ≤ ENNReal.ofReal (C * ‖v‖) := by
  intro this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels tubeChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hTubeNormalSizeContinuous hTubeImageCenter tubeNormalSize speedCore hSpeedCoreCenter speedCover hSpeedCoverOpen hSpeedCoverCenter this p q x
  dsimp only
  letI := L.identification.unstableTopology x
  letI := L.identification.unstableCharts x
  letI := (L.unstable x).smoothAtlas
  let Φ := coherentU.family 2 p
  let P := Φ.family.plaque q
  let D : Opens (Fin (coherentU.dimension 2 p) → ℝ) :=
    ⟨Metric.ball 0 Φ.family.radius,Metric.isOpen_ball⟩
  intro l hl hlocal C hbound v hv
  let η : ℝ →ᵃ[ℝ] (Fin (coherentU.dimension 2 p) → ℝ) := AffineMap.lineMap 0 v
  have hη : ContMDiff 𝓘(ℝ) 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) ∞ η :=
    contMDiff_iff_contDiff.mpr (AffineMap.contDiff_lineMap _ _)
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) : η t ∈ Metric.closedBall 0 (Φ.family.radius / 2) :=
    (convex_closedBall _ _).mapsTo_lineMap
      (Metric.mem_closedBall_self (half_pos Φ.family.radius_pos).le) hv ht
  have hball (t : ℝ) (ht : t ∈ Icc 0 1) : η t ∈ Metric.ball 0 Φ.family.radius :=
    Metric.closedBall_subset_ball (half_lt_self Φ.family.radius_pos) (hmem t ht)
  let ηD : ℝ → D := fun t ↦
    ⟨η (projIcc 0 1 zero_le_one t).val,
      hball (projIcc 0 1 zero_le_one t).val (projIcc 0 1 zero_le_one t).property⟩
  have hηDeq (t : ℝ) (ht : t ∈ Icc 0 1) : (ηD t).val = η t := by
    change η (projIcc 0 1 zero_le_one t).val = η t
    rw [projIcc_of_mem _ ht]
  have hηD : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) ∞ ηD (Icc 0 1) := by
    intro t ht
    apply (ContMDiffWithinAt.subtypeVal_comp_iff D ηD (Icc 0 1) t).mp
    exact (hη t).contMDiffWithinAt.congr (fun s hs ↦ hηDeq s hs) (hηDeq t ht)
  let γ : ℝ → L.U x := l ∘ ηD
  have hγ : ContMDiffOn 𝓘(ℝ) (L.uModel x) 1 γ (Icc 0 1) :=
    (hlocal.contMDiff.comp_contMDiffOn hηD).of_le (by simp)
  have hparam (t : ℝ) (ht : t ∈ Icc 0 1) :
      ((Subtype.val : L.U x → M) ∘ γ) t = P.param (η t) := by
    exact (hl (ηD t)).trans (congrArg P.param (hηDeq t ht))
  letI : Bundle.RiemannianBundle (fun y : M ↦ TangentSpace (realModel d) y) :=
    ⟨g.toRiemannianMetric⟩
  have hspeed (t : ℝ) (ht : t ∈ Icc 0 1) :
      ‖mfderivWithin 𝓘(ℝ) (realModel d) (P.param ∘ η)
        (Icc 0 1) t 1‖ ≤ C * ‖v‖ := by
    have hdomain : η t ∈ P.domain := by rw [Φ.family.domain_eq q]; exact hball t ht
    have hd := mfderiv_comp_mfderivWithin t
      (((P.smooth (η t) hdomain).contMDiffAt (P.domain_open.mem_nhds hdomain)).mdifferentiableAt (by simp))
      (hη.contMDiffOn.mdifferentiableOn (by simp) t ht)
      ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
    rw [hd]
    have hvη : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ)
        η (Icc 0 1) t 1 = v := by
      rw [mfderivWithin_eq_fderivWithin,
        AffineMap.hasDerivWithinAt_lineMap.hasFDerivWithinAt.fderivWithin
          (uniqueDiffOn_Icc zero_lt_one t ht)]
      change (1 : ℝ) • (v-0) = v
      simp only [sub_zero,one_smul]
    change ‖mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d) P.param (η t)
      (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) η (Icc 0 1) t 1)‖ ≤ _
    rw [hvη]
    exact hbound (η t) (hmem t ht) v
  have hb := intrinsicHermitianLeafEDist_le_included_curve
    (Subtype.val : L.U x → M) ((L.unstable x).inclusion_smooth.of_le (by simp))
    hmetric g (StableFoliationsSupport.originalSmoothRealMetric_inner hmetric hmetric_smooth)
    γ hγ
  have hpath : pathELength (realModel d) ((Subtype.val : L.U x → M) ∘ γ) 0 1 =
      pathELength (realModel d) (P.param ∘ η) 0 1 := by
    exact pathELength_congr hparam
  have hlength : pathELength (realModel d) (P.param ∘ η) 0 1 ≤ ENNReal.ofReal (C * ‖v‖) := by
    rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (C * ‖v‖) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hspeed t ht)
      _ = _ := by simp
  have hb' := hb.trans (hpath.trans_le hlength)
  have hzero : γ 0 = l ⟨0,Metric.mem_ball_self Φ.family.radius_pos⟩ := by
    apply congrArg l
    apply Subtype.ext
    exact (hηDeq 0 (by simp)).trans (AffineMap.lineMap_apply_zero _ _)
  have hone : γ 1 = l ⟨v,Metric.closedBall_subset_ball (half_lt_self Φ.family.radius_pos) hv⟩ := by
    apply congrArg l
    apply Subtype.ext
    exact (hηDeq 1 (by simp)).trans (AffineMap.lineMap_apply_one _ _)
  rw [hzero,hone] at hb'
  exact hb'


end
end HolomorphicAnosov.Ghys
