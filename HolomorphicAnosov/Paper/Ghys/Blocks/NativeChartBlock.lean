import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! Maximal-atlas charts for lifted unstable plaques with prescribed linear coordinates. -/

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
/-- The lifted unstable plaque defines a maximal-atlas chart with the prescribed
linear coordinates and sends its center to zero. -/
theorem NativeChartBlock {d : ℕ} {M : Type u}
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
                                        (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesU.dimension p₀) → ℝ) Φ.family.radius)
                                          Metric.isOpen_ball)
                                        (fun
                                            (z :
                                              Φ.family.centerDomain.Elem ×
                                                ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesU.dimension p₀) → ℝ) Φ.family.radius)
                                                    Metric.isOpen_ball)) =>
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
                                          (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (coherentU.dimension N p₀) → ℝ) Φ.family.radius)
                                            Metric.isOpen_ball)
                                          (fun
                                              (z :
                                                Φ.family.centerDomain.Elem ×
                                                  ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (coherentU.dimension N p₀) → ℝ) Φ.family.radius)
                                                      Metric.isOpen_ball)) =>
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
                                                    ((Fin (coherentU.dimension 2 p) → ℝ) ×
                                                      ↥(plaqueNormalSpace
                                                          ((fun
                                                                (z :
                                                                  (coherentU.family (2)
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension 2 p) →
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
                                                                        (coherentU.dimension 2 p) →
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
                                                  ∀ (coefficientRadius : M → ℝ),
                                                    (∀ (p : M), 0 < coefficientRadius p) →
                                                      ∀ (fixedTubeRadius : M → ℝ),
                                                        (∀ (p : M), 0 < fixedTubeRadius p) →
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
                                                                    (Fin
                                                                          (coherentU.dimension 2 p) →
                                                                        ℝ) →
                                                                      ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ :=
                                                                fun (p : M)
                                                                  (q :
                                                                    (coherentU.family (2)
                                                                            p).family.centerDomain.Elem)
                                                                  (v :
                                                                    Fin
                                                                        (coherentU.dimension 2 p) →
                                                                      ℝ) =>
                                                                originalMetricChartTensor_g18 g
                                                                  (coherentU.family (2)
                                                                        p).family.receivingAnchor
                                                                  ((coherentU.coherence (2)
                                                                        p).coordinate
                                                                    q v);
                                                              let tubeDerivative :
                                                                (p : M) →
                                                                  (coherentU.family (2)
                                                                            p).family.centerDomain.Elem →
                                                                    (Fin
                                                                          (coherentU.dimension 2 p) →
                                                                        ℝ) →
                                                                      (Fin
                                                                            (coherentU.dimension 2 p) →
                                                                          ℝ) →L[ℝ]
                                                                        ComplexModel d :=
                                                                fun (p : M)
                                                                  (q :
                                                                    (coherentU.family (2)
                                                                            p).family.centerDomain.Elem)
                                                                  (v :
                                                                    Fin
                                                                        (coherentU.dimension 2 p) →
                                                                      ℝ) =>
                                                                fderiv ℝ
                                                                  ((coherentU.coherence (2)
                                                                        p).coordinate
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
                                                                    (Fin
                                                                          (coherentU.dimension 2 p) →
                                                                        ℝ) →
                                                                      ↥(tubeNormalSpace p) →L[ℝ] ComplexModel d :=
                                                                fun (p : M)
                                                                  (q :
                                                                    (coherentU.family (2)
                                                                            p).family.centerDomain.Elem)
                                                                  (v :
                                                                    Fin
                                                                        (coherentU.dimension 2 p) →
                                                                      ℝ) =>
                                                                plaqueNormalFrame (tubeTensor p q v)
                                                                  (tubeDerivative p q v) (tubeNormalSpace p).subtypeL;
                                                              (∀ (p : M),
                                                                  have D :
                                                                    (coherentU.family (2)
                                                                                p).family.centerDomain.Elem ×
                                                                        (Fin
                                                                            (coherentU.dimension 2 p) →
                                                                          ℝ) →
                                                                      (Fin
                                                                            (coherentU.dimension 2 p) →
                                                                          ℝ) →L[ℝ]
                                                                        ComplexModel d :=
                                                                    fun
                                                                      (z :
                                                                        (coherentU.family (2)
                                                                                  p).family.centerDomain.Elem ×
                                                                          (Fin
                                                                              (coherentU.dimension 2 p) →
                                                                            ℝ)) =>
                                                                    fderiv ℝ
                                                                      ((coherentU.coherence (2)
                                                                            p).coordinate
                                                                        z.1)
                                                                      z.2;
                                                                  have b :
                                                                    (coherentU.family (2)
                                                                                p).family.centerDomain.Elem ×
                                                                        (Fin
                                                                            (coherentU.dimension 2 p) →
                                                                          ℝ) →
                                                                      ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ :=
                                                                    fun
                                                                      (z :
                                                                        (coherentU.family (2)
                                                                                  p).family.centerDomain.Elem ×
                                                                          (Fin
                                                                              (coherentU.dimension 2 p) →
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
                                                                        (Fin
                                                                            (coherentU.dimension 2 p) →
                                                                          ℝ) →
                                                                      ↥K →L[ℝ] ComplexModel d :=
                                                                    fun
                                                                      (z :
                                                                        (coherentU.family (2)
                                                                                  p).family.centerDomain.Elem ×
                                                                          (Fin
                                                                              (coherentU.dimension 2 p) →
                                                                            ℝ)) =>
                                                                    plaqueNormalFrame (b z) (D z) K.subtypeL;
                                                                  have size :
                                                                    ((coherentU.family (2)
                                                                                  p).family.centerDomain.Elem ×
                                                                          (Fin
                                                                              (coherentU.dimension 2 p) →
                                                                            ℝ)) ×
                                                                        ↥K →
                                                                      ℝ :=
                                                                    fun
                                                                      (z :
                                                                        ((coherentU.family (2)
                                                                                    p).family.centerDomain.Elem ×
                                                                            (Fin
                                                                                (coherentU.dimension 2 p) →
                                                                              ℝ)) ×
                                                                          ↥K) =>
                                                                    √(DFunLike.coe
                                                                        (DFunLike.coe (b z.1)
                                                                          (DFunLike.coe (N z.1) z.2))
                                                                        (DFunLike.coe (N z.1) z.2));
                                                                  ContinuousAt size
                                                                      ((Subtype.mk p
                                                                            (coherentU.family (2)
                                                                                  p).family.center_mem,
                                                                          0),
                                                                        0) ∧
                                                                    size
                                                                        ((Subtype.mk p
                                                                              (coherentU.family
                                                                                    (2)
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
                                                                                (coherentU.dimension 2 p) →
                                                                              ℝ)) ×
                                                                          ↥(tubeNormalSpace p) →
                                                                        ℝ :=
                                                                    fun (p : M)
                                                                      (z :
                                                                        ((coherentU.family (2)
                                                                                    p).family.centerDomain.Elem ×
                                                                            (Fin
                                                                                (coherentU.dimension 2 p) →
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
                                                                              (coherentU.family
                                                                                    (2)
                                                                                    p).family.center_mem)) →
                                                                      (∀ (p : M),
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
                                                                                          (coherentU.dimension 2 p) →
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
                                                                                            v))) →
                                                                        let speedCover : M → Set M := fun (p : M) =>
                                                                          Subtype.val ''
                                                                            interior
                                                                              (speedCore p ∩
                                                                                (fixedTubeLabels p ∩
                                                                                  coefficientLabels p));
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
                                                                            (∀ (p : M)
                                                                                (q :
                                                                                  (coherentU.family
                                                                                          (2)
                                                                                          p).family.centerDomain.Elem)
                                                                                (x : M),
                                                                                ForwardAsymptotic
                                                                                    (DFunLike.coe (Diffeomorph.symm f))
                                                                                    x q.val →
                                                                                  let B :
                                                                                    TopologicalSpace.Opens
                                                                                      (Fin
                                                                                          (coherentU.dimension 2 p) →
                                                                                        ℝ) :=
                                                                                    TopologicalSpace.Opens.mk
                                                                                      (Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                                        (coherentU.family
                                                                                              (2)
                                                                                              p).family.radius)
                                                                                      Metric.isOpen_ball;
                                                                                  ∃ (l : ↥B → L.U x),
                                                                                    (∀ (v : ↥B),
                                                                                        (l v).val =
                                                                                          ((coherentU.family
                                                                                                      (2)
                                                                                                      p).family.plaque
                                                                                                q).param
                                                                                            v.val) ∧
                                                                                      IsLocalDiffeomorph
                                                                                          𝓘(ℝ,
                                                                                            Fin
                                                                                                (coherentU.dimension 2 p) →
                                                                                              ℝ)
                                                                                          (L.uModel x) ∞ l ∧
                                                                                        IsOpenEmbedding l) →
                                                                              ∀ (p : M)
                                                                                (q :
                                                                                  (coherentU.family
                                                                                          (2)
                                                                                          p).family.centerDomain.Elem)
                                                                                (x : M),
                                                                                ForwardAsymptotic
                                                                                    (DFunLike.coe (Diffeomorph.symm f))
                                                                                    x q.val →
                                                                                  ∃ (J :
                                                                                    (Fin (L.unstable x).rank → ℝ) ≃ₗᵢ[ℝ]
                                                                                      Fin
                                                                                          (coherentU.dimension 2 p) →
                                                                                        ℝ),
                                                                                    ∃
                                                                                      c ∈
                                                                                        IsManifold.maximalAtlas
                                                                                          (L.uModel x) ∞ (L.U x),
                                                                                      c.target =
                                                                                          DFunLike.coe J ⁻¹'
                                                                                            Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                                              (coherentU.family
                                                                                                    (2)
                                                                                                    p).family.radius ∧
                                                                                        (∀
                                                                                            (v :
                                                                                              Fin (L.unstable x).rank →
                                                                                                ℝ),
                                                                                            DFunLike.coe J v ∈
                                                                                                Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                                                  (coherentU.family
                                                                                                        (2)
                                                                                                        p).family.radius →
                                                                                              (c.symm.toFun' v).val =
                                                                                                ((coherentU.family
                                                                                                            (2)
                                                                                                            p).family.plaque
                                                                                                      q).param
                                                                                                  (DFunLike.coe J v)) ∧
                                                                                          ∃ (center : L.U x),
                                                                                            center.val = q.val ∧
                                                                                              center ∈ c.source ∧
                                                                                                c.toFun' center =
                                                                                                  0 := by
  intro this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius fixedTubeRadius hFixedTubeRadius fixedTubeLabels hFixedTubeLabels tubeChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hTubeNormalSizeContinuous hTubeImageCenter tubeNormalSize speedCore hSpeedCoreCenter hNativeMetricLowerBounds speedCover hSpeedCoverOpen hSpeedCoverCenter this hNativeLift p q x hclass
  letI := L.identification.unstableTopology x
  letI := L.identification.unstableCharts x
  letI : IsManifold (L.uModel x) ∞ (L.U x) := (L.unstable x).smoothAtlas
  letI : T2Space (L.U x) := (L.unstable x).hausdorff
  let B : Opens (Fin (coherentU.dimension 2 p) → ℝ) :=
    ⟨Metric.ball 0 (coherentU.family 2 p).family.radius,Metric.isOpen_ball⟩
  let v₀ : B := ⟨0,Metric.mem_ball_self (coherentU.family 2 p).family.radius_pos⟩
  obtain ⟨l,hl,hlocal,hopen⟩ := hNativeLift p q x hclass
  obtain ⟨J,c,hc,hsource,htarget,hinv,hfor⟩ :=
    native_plaque_chart_from_lift_g18 B v₀ l hlocal hopen
  refine ⟨J,c,hc,htarget,?_,l v₀,?_,?_,?_⟩
  · intro v hv
    rw [hinv v hv]
    exact hl _
  · exact (hl v₀).trans ((coherentU.family 2 p).family.plaque q).centered
  · rw [hsource]
    exact Set.mem_range_self _
  · simpa only [v₀,map_zero] using hfor v₀



end
end HolomorphicAnosov.Ghys
