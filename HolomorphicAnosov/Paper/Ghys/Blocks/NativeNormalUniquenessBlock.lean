import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! Small normal vectors at points of an unstable plaque with equal exponential images
have equal plaque base coordinates. (Ghys, Prop. 2.2) -/

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
theorem NativeNormalUniquenessBlock {d : ℕ} {M : Type u}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ChartedSpace (ComplexModel d) M] [inst_5 : IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M)
  (hmetric : HermitianTangentMetricCore d M) (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric) :
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
                                        (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin _ → ℝ) Φ.family.radius)
                                          Metric.isOpen_ball)
                                        (fun
                                            (z :
                                              Φ.family.centerDomain.Elem ×
                                                ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin _ → ℝ) Φ.family.radius)
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
                                          (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin _ → ℝ) Φ.family.radius)
                                            Metric.isOpen_ball)
                                          (fun
                                              (z :
                                                Φ.family.centerDomain.Elem ×
                                                  ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin _ → ℝ) Φ.family.radius)
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
                                                  ∀ (coefficientRadius coefficientBound : M → ℝ),
                                                    (∀ (p : M), 0 < coefficientBound p) →
                                                      (∀ (p : M),
                                                          ∀ p_1 ∈ coefficientLabels p,
                                                            ∀
                                                              u ∈
                                                                Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                  (coefficientRadius p),
                                                              u ∈
                                                                  Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                    (coherentU.family (2)
                                                                          p).family.radius ∧
                                                                (((fun
                                                                              (z :
                                                                                (coherentU.family
                                                                                          (2)
                                                                                          p).family.centerDomain.Elem ×
                                                                                  (Fin
                                                                                      (coherentU.dimension
                                                                                        (2) p) →
                                                                                    ℝ)) =>
                                                                            fderiv ℝ
                                                                              ((coherentU.coherence
                                                                                    (2)
                                                                                    p).coordinate
                                                                                z.1)
                                                                              z.2)
                                                                          (p_1, u)).coprod
                                                                      ((fun
                                                                            (z :
                                                                              (coherentU.family
                                                                                        (2)
                                                                                        p).family.centerDomain.Elem ×
                                                                                (Fin
                                                                                    (coherentU.dimension
                                                                                      (2) p) →
                                                                                  ℝ)) =>
                                                                          plaqueNormalFrame
                                                                            ((fun
                                                                                  (z :
                                                                                    (coherentU.family
                                                                                              (2)
                                                                                              p).family.centerDomain.Elem ×
                                                                                      (Fin
                                                                                          (coherentU.dimension
                                                                                            (2)
                                                                                            p) →
                                                                                        ℝ)) =>
                                                                                originalMetricChartTensor_g18 g
                                                                                  (coherentU.family
                                                                                        (2)
                                                                                        p).family.receivingAnchor
                                                                                  ((coherentU.coherence
                                                                                        (2)
                                                                                        p).coordinate
                                                                                    z.1 z.2))
                                                                              z)
                                                                            ((fun
                                                                                  (z :
                                                                                    (coherentU.family
                                                                                              (2)
                                                                                              p).family.centerDomain.Elem ×
                                                                                      (Fin
                                                                                          (coherentU.dimension
                                                                                            (2)
                                                                                            p) →
                                                                                        ℝ)) =>
                                                                                fderiv ℝ
                                                                                  ((coherentU.coherence
                                                                                        (2)
                                                                                        p).coordinate
                                                                                    z.1)
                                                                                  z.2)
                                                                              z)
                                                                            (plaqueNormalSpace
                                                                                ((fun
                                                                                      (z :
                                                                                        (coherentU.family
                                                                                                  (2)
                                                                                                  p).family.centerDomain.Elem ×
                                                                                          (Fin
                                                                                              (coherentU.dimension
                                                                                                (2)
                                                                                                p) →
                                                                                            ℝ)) =>
                                                                                    originalMetricChartTensor_g18 g
                                                                                      (coherentU.family
                                                                                            (2)
                                                                                            p).family.receivingAnchor
                                                                                      ((coherentU.coherence
                                                                                            (2)
                                                                                            p).coordinate
                                                                                        z.1 z.2))
                                                                                  (Subtype.mk p
                                                                                      (coherentU.family
                                                                                            (2)
                                                                                            p).family.center_mem,
                                                                                    0))
                                                                                ((fun
                                                                                      (z :
                                                                                        (coherentU.family
                                                                                                  (2)
                                                                                                  p).family.centerDomain.Elem ×
                                                                                          (Fin
                                                                                              (coherentU.dimension
                                                                                                (2)
                                                                                                p) →
                                                                                            ℝ)) =>
                                                                                    fderiv ℝ
                                                                                      ((coherentU.coherence
                                                                                            (2)
                                                                                            p).coordinate
                                                                                        z.1)
                                                                                      z.2)
                                                                                  (Subtype.mk p
                                                                                      (coherentU.family
                                                                                            (2)
                                                                                            p).family.center_mem,
                                                                                    0))).subtypeL)
                                                                        (p_1, u))).IsInvertible ∧
                                                                  ∀ (w : ComplexModel d),
                                                                    (∀
                                                                        (v :
                                                                          Fin
                                                                              (coherentU.dimension
                                                                                (2) p) →
                                                                            ℝ),
                                                                        DFunLike.coe
                                                                            (DFunLike.coe
                                                                              ((fun
                                                                                    (z :
                                                                                      (coherentU.family
                                                                                                (2)
                                                                                                p).family.centerDomain.Elem ×
                                                                                        (Fin
                                                                                            (coherentU.dimension
                                                                                              (2)
                                                                                              p) →
                                                                                          ℝ)) =>
                                                                                  originalMetricChartTensor_g18 g
                                                                                    (coherentU.family
                                                                                          (2)
                                                                                          p).family.receivingAnchor
                                                                                    ((coherentU.coherence
                                                                                          (2)
                                                                                          p).coordinate
                                                                                      z.1 z.2))
                                                                                (p_1, u))
                                                                              w)
                                                                            (DFunLike.coe
                                                                              ((fun
                                                                                    (z :
                                                                                      (coherentU.family
                                                                                                (2)
                                                                                                p).family.centerDomain.Elem ×
                                                                                        (Fin
                                                                                            (coherentU.dimension
                                                                                              (2)
                                                                                              p) →
                                                                                          ℝ)) =>
                                                                                  fderiv ℝ
                                                                                    ((coherentU.coherence
                                                                                          (2)
                                                                                          p).coordinate
                                                                                      z.1)
                                                                                    z.2)
                                                                                (p_1, u))
                                                                              v) =
                                                                          0) →
                                                                      ∃ (k :
                                                                        ↥(plaqueNormalSpace
                                                                            ((fun
                                                                                  (z :
                                                                                    (coherentU.family
                                                                                              (2)
                                                                                              p).family.centerDomain.Elem ×
                                                                                      (Fin
                                                                                          (coherentU.dimension
                                                                                            (2)
                                                                                            p) →
                                                                                        ℝ)) =>
                                                                                originalMetricChartTensor_g18 g
                                                                                  (coherentU.family
                                                                                        (2)
                                                                                        p).family.receivingAnchor
                                                                                  ((coherentU.coherence
                                                                                        (2)
                                                                                        p).coordinate
                                                                                    z.1 z.2))
                                                                              (Subtype.mk p
                                                                                  (coherentU.family
                                                                                        (2)
                                                                                        p).family.center_mem,
                                                                                0))
                                                                            ((fun
                                                                                  (z :
                                                                                    (coherentU.family
                                                                                              (2)
                                                                                              p).family.centerDomain.Elem ×
                                                                                      (Fin
                                                                                          (coherentU.dimension
                                                                                            (2)
                                                                                            p) →
                                                                                        ℝ)) =>
                                                                                fderiv ℝ
                                                                                  ((coherentU.coherence
                                                                                        (2)
                                                                                        p).coordinate
                                                                                    z.1)
                                                                                  z.2)
                                                                              (Subtype.mk p
                                                                                  (coherentU.family
                                                                                        (2)
                                                                                        p).family.center_mem,
                                                                                0)))),
                                                                        DFunLike.coe
                                                                              ((fun
                                                                                    (z :
                                                                                      (coherentU.family
                                                                                                (2)
                                                                                                p).family.centerDomain.Elem ×
                                                                                        (Fin
                                                                                            (coherentU.dimension
                                                                                              (2)
                                                                                              p) →
                                                                                          ℝ)) =>
                                                                                  plaqueNormalFrame
                                                                                    ((fun
                                                                                          (z :
                                                                                            (coherentU.family
                                                                                                      (2)
                                                                                                      p).family.centerDomain.Elem ×
                                                                                              (Fin
                                                                                                  (coherentU.dimension
                                                                                                    (2)
                                                                                                    p) →
                                                                                                ℝ)) =>
                                                                                        originalMetricChartTensor_g18 g
                                                                                          (coherentU.family
                                                                                                (2)
                                                                                                p).family.receivingAnchor
                                                                                          ((coherentU.coherence
                                                                                                (2)
                                                                                                p).coordinate
                                                                                            z.1 z.2))
                                                                                      z)
                                                                                    ((fun
                                                                                          (z :
                                                                                            (coherentU.family
                                                                                                      (2)
                                                                                                      p).family.centerDomain.Elem ×
                                                                                              (Fin
                                                                                                  (coherentU.dimension
                                                                                                    (2)
                                                                                                    p) →
                                                                                                ℝ)) =>
                                                                                        fderiv ℝ
                                                                                          ((coherentU.coherence
                                                                                                (2)
                                                                                                p).coordinate
                                                                                            z.1)
                                                                                          z.2)
                                                                                      z)
                                                                                    (plaqueNormalSpace
                                                                                        ((fun
                                                                                              (z :
                                                                                                (coherentU.family
                                                                                                          (2)
                                                                                                          p).family.centerDomain.Elem ×
                                                                                                  (Fin
                                                                                                      (coherentU.dimension
                                                                                                        (2)
                                                                                                        p) →
                                                                                                    ℝ)) =>
                                                                                            originalMetricChartTensor_g18
                                                                                              g
                                                                                              (coherentU.family
                                                                                                    (2)
                                                                                                    p).family.receivingAnchor
                                                                                              ((coherentU.coherence
                                                                                                    (2)
                                                                                                    p).coordinate
                                                                                                z.1 z.2))
                                                                                          (Subtype.mk p
                                                                                              (coherentU.family
                                                                                                    (2)
                                                                                                    p).family.center_mem,
                                                                                            0))
                                                                                        ((fun
                                                                                              (z :
                                                                                                (coherentU.family
                                                                                                          (2)
                                                                                                          p).family.centerDomain.Elem ×
                                                                                                  (Fin
                                                                                                      (coherentU.dimension
                                                                                                        (2)
                                                                                                        p) →
                                                                                                    ℝ)) =>
                                                                                            fderiv ℝ
                                                                                              ((coherentU.coherence
                                                                                                    (2)
                                                                                                    p).coordinate
                                                                                                z.1)
                                                                                              z.2)
                                                                                          (Subtype.mk p
                                                                                              (coherentU.family
                                                                                                    (2)
                                                                                                    p).family.center_mem,
                                                                                            0))).subtypeL)
                                                                                (p_1, u))
                                                                              k =
                                                                            w ∧
                                                                          ‖k‖ ≤
                                                                            coefficientBound p *
                                                                              √(DFunLike.coe
                                                                                  (DFunLike.coe
                                                                                    ((fun
                                                                                          (z :
                                                                                            (coherentU.family
                                                                                                      (2)
                                                                                                      p).family.centerDomain.Elem ×
                                                                                              (Fin
                                                                                                  (coherentU.dimension
                                                                                                    (2)
                                                                                                    p) →
                                                                                                ℝ)) =>
                                                                                        originalMetricChartTensor_g18 g
                                                                                          (coherentU.family
                                                                                                (2)
                                                                                                p).family.receivingAnchor
                                                                                          ((coherentU.coherence
                                                                                                (2)
                                                                                                p).coordinate
                                                                                            z.1 z.2))
                                                                                      (p_1, u))
                                                                                    w)
                                                                                  w)) →
                                                        ∀ (fixedTubeRadius : M → ℝ)
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
                                                            ∀ (fixedNormalRadius : M → ℝ),
                                                              let tubeChart : M → PartialEquiv M (ComplexModel d) :=
                                                                fun (p : M) =>
                                                                extChartAt (realModel d)
                                                                  (coherentU.family (2)
                                                                        p).family.receivingAnchor;
                                                              let tubeTangentChart :
                                                                M →
                                                                  PartialEquiv
                                                                    (Bundle.TotalSpace (ComplexModel d)
                                                                      (TangentSpace (realModel d)))
                                                                    (ComplexModel d × ComplexModel d) :=
                                                                fun (p : M) =>
                                                                extChartAt (realModel d).tangent
                                                                  ⟨(coherentU.family (2)
                                                                          p).family.receivingAnchor,
                                                                    0⟩;
                                                              let tubeTensor :
                                                                (p : M) →
                                                                  (coherentU.family (2)
                                                                            p).family.centerDomain.Elem →
                                                                    (Fin
                                                                          (coherentU.dimension (2)
                                                                            p) →
                                                                        ℝ) →
                                                                      ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ :=
                                                                fun (p : M)
                                                                  (q :
                                                                    (coherentU.family (2)
                                                                            p).family.centerDomain.Elem)
                                                                  (v :
                                                                    Fin
                                                                        (coherentU.dimension (2)
                                                                          p) →
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
                                                                          (coherentU.dimension (2)
                                                                            p) →
                                                                        ℝ) →
                                                                      (Fin
                                                                            (coherentU.dimension
                                                                              (2) p) →
                                                                          ℝ) →L[ℝ]
                                                                        ComplexModel d :=
                                                                fun (p : M)
                                                                  (q :
                                                                    (coherentU.family (2)
                                                                            p).family.centerDomain.Elem)
                                                                  (v :
                                                                    Fin
                                                                        (coherentU.dimension (2)
                                                                          p) →
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
                                                                          (coherentU.dimension (2)
                                                                            p) →
                                                                        ℝ) →
                                                                      ↥(tubeNormalSpace p) →L[ℝ] ComplexModel d :=
                                                                fun (p : M)
                                                                  (q :
                                                                    (coherentU.family (2)
                                                                            p).family.centerDomain.Elem)
                                                                  (v :
                                                                    Fin
                                                                        (coherentU.dimension (2)
                                                                          p) →
                                                                      ℝ) =>
                                                                plaqueNormalFrame (tubeTensor p q v)
                                                                  (tubeDerivative p q v) (tubeNormalSpace p).subtypeL;
                                                              (∀ (p : M),
                                                                  ∀ q ∈ fixedTubeLabels p,
                                                                    ∀
                                                                      (z w :
                                                                        (Fin
                                                                              (coherentU.dimension
                                                                                (2) p) →
                                                                            ℝ) ×
                                                                          ↥(tubeNormalSpace p)),
                                                                      z ∈
                                                                          Metric.closedBall (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                              (fixedTubeRadius p) ×ˢ
                                                                            Metric.ball (0 : tubeNormalSpace p)
                                                                              (fixedNormalRadius p) →
                                                                        w ∈
                                                                            Metric.closedBall (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                                (fixedTubeRadius p) ×ˢ
                                                                              Metric.ball (0 : tubeNormalSpace p)
                                                                                (fixedNormalRadius p) →
                                                                          riemannianExponential g
                                                                                ((tubeTangentChart p).symm.toFun
                                                                                  ((coherentU.coherence
                                                                                          (2)
                                                                                          p).coordinate
                                                                                      q z.1,
                                                                                    DFunLike.coe (tubeNormal p q z.1)
                                                                                      z.2)) =
                                                                              riemannianExponential g
                                                                                ((tubeTangentChart p).symm.toFun
                                                                                  ((coherentU.coherence
                                                                                          (2)
                                                                                          p).coordinate
                                                                                      q w.1,
                                                                                    DFunLike.coe (tubeNormal p q w.1)
                                                                                      w.2)) →
                                                                            z = w) →
                                                                (∀ (p : M),
                                                                    let D :
                                                                      (coherentU.family (2)
                                                                                  p).family.centerDomain.Elem ×
                                                                          (Fin
                                                                              (coherentU.dimension
                                                                                (2) p) →
                                                                            ℝ) →
                                                                        (Fin
                                                                              (coherentU.dimension
                                                                                (2) p) →
                                                                            ℝ) →L[ℝ]
                                                                          ComplexModel d :=
                                                                      fun
                                                                        (z :
                                                                          (coherentU.family (2)
                                                                                    p).family.centerDomain.Elem ×
                                                                            (Fin
                                                                                (coherentU.dimension
                                                                                  (2) p) →
                                                                              ℝ)) =>
                                                                      fderiv ℝ
                                                                        ((coherentU.coherence (2)
                                                                              p).coordinate
                                                                          z.1)
                                                                        z.2;
                                                                    let b :
                                                                      (coherentU.family (2)
                                                                                  p).family.centerDomain.Elem ×
                                                                          (Fin
                                                                              (coherentU.dimension
                                                                                (2) p) →
                                                                            ℝ) →
                                                                        ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ :=
                                                                      fun
                                                                        (z :
                                                                          (coherentU.family (2)
                                                                                    p).family.centerDomain.Elem ×
                                                                            (Fin
                                                                                (coherentU.dimension
                                                                                  (2) p) →
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
                                                                              (coherentU.family
                                                                                    (2)
                                                                                    p).family.center_mem,
                                                                            0))
                                                                        (D
                                                                          (Subtype.mk p
                                                                              (coherentU.family
                                                                                    (2)
                                                                                    p).family.center_mem,
                                                                            0));
                                                                    let N :
                                                                      (coherentU.family (2)
                                                                                  p).family.centerDomain.Elem ×
                                                                          (Fin
                                                                              (coherentU.dimension
                                                                                (2) p) →
                                                                            ℝ) →
                                                                        ↥K →L[ℝ] ComplexModel d :=
                                                                      fun
                                                                        (z :
                                                                          (coherentU.family (2)
                                                                                    p).family.centerDomain.Elem ×
                                                                            (Fin
                                                                                (coherentU.dimension
                                                                                  (2) p) →
                                                                              ℝ)) =>
                                                                      plaqueNormalFrame (b z) (D z) K.subtypeL;
                                                                    let size :
                                                                      ((coherentU.family (2)
                                                                                    p).family.centerDomain.Elem ×
                                                                            (Fin
                                                                                (coherentU.dimension
                                                                                  (2) p) →
                                                                              ℝ)) ×
                                                                          ↥K →
                                                                        ℝ :=
                                                                      fun
                                                                        (z :
                                                                          ((coherentU.family (2)
                                                                                      p).family.centerDomain.Elem ×
                                                                              (Fin
                                                                                  (coherentU.dimension
                                                                                    (2) p) →
                                                                                ℝ)) ×
                                                                            ↥K) =>
                                                                      √(DFunLike.coe
                                                                          (DFunLike.coe (b z.1)
                                                                            (DFunLike.coe (N z.1) z.2))
                                                                          (DFunLike.coe (N z.1) z.2));
                                                                    ContinuousAt size
                                                                        ((Subtype.mk p
                                                                              (coherentU.family
                                                                                    (2)
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
                                                                                  (coherentU.dimension
                                                                                    (2) p) →
                                                                                ℝ)) ×
                                                                            ↥(tubeNormalSpace p) →
                                                                          ℝ :=
                                                                      fun (p : M)
                                                                        (z :
                                                                          ((coherentU.family (2)
                                                                                      p).family.centerDomain.Elem ×
                                                                              (Fin
                                                                                  (coherentU.dimension
                                                                                    (2) p) →
                                                                                ℝ)) ×
                                                                            ↥(tubeNormalSpace p)) =>
                                                                      √(DFunLike.coe
                                                                          (DFunLike.coe (tubeTensor p z.1.1 z.1.2)
                                                                            (DFunLike.coe (tubeNormal p z.1.1 z.1.2)
                                                                              z.2))
                                                                          (DFunLike.coe (tubeNormal p z.1.1 z.1.2)
                                                                            z.2));
                                                                    ∀ (p : M),
                                                                      ∀ q ∈ fixedTubeLabels p ∩ coefficientLabels p,
                                                                        ∀
                                                                          (u v :
                                                                            Fin
                                                                                (coherentU.dimension
                                                                                  (2) p) →
                                                                              ℝ),
                                                                          ‖u‖ <
                                                                              min (fixedTubeRadius p)
                                                                                (coefficientRadius p) →
                                                                            ‖v‖ <
                                                                                min (fixedTubeRadius p)
                                                                                  (coefficientRadius p) →
                                                                              ∀
                                                                                (ν :
                                                                                  TangentSpace (realModel d)
                                                                                    (((coherentU.family
                                                                                                (2)
                                                                                                p).family.plaque
                                                                                          q).param
                                                                                      u))
                                                                                (μ :
                                                                                  TangentSpace (realModel d)
                                                                                    (((coherentU.family
                                                                                                (2)
                                                                                                p).family.plaque
                                                                                          q).param
                                                                                      v)),
                                                                                (∀
                                                                                    w ∈
                                                                                      a.splitting.unstable.toDistribution
                                                                                        (((coherentU.family
                                                                                                    (2)
                                                                                                    p).family.plaque
                                                                                              q).param
                                                                                          u),
                                                                                    DFunLike.coe
                                                                                        (DFunLike.coe
                                                                                          (g.inner
                                                                                            (((coherentU.family
                                                                                                        (2)
                                                                                                        p).family.plaque
                                                                                                  q).param
                                                                                              u))
                                                                                          ν)
                                                                                        w =
                                                                                      0) →
                                                                                  (∀
                                                                                      w ∈
                                                                                        a.splitting.unstable.toDistribution
                                                                                          (((coherentU.family
                                                                                                      (2)
                                                                                                      p).family.plaque
                                                                                                q).param
                                                                                            v),
                                                                                      DFunLike.coe
                                                                                          (DFunLike.coe
                                                                                            (g.inner
                                                                                              (((coherentU.family
                                                                                                          (2)
                                                                                                          p).family.plaque
                                                                                                    q).param
                                                                                                v))
                                                                                            μ)
                                                                                          w =
                                                                                        0) →
                                                                                    √(DFunLike.coe
                                                                                            (DFunLike.coe
                                                                                              (g.inner
                                                                                                (((coherentU.family
                                                                                                            (2)
                                                                                                            p).family.plaque
                                                                                                      q).param
                                                                                                  u))
                                                                                              ν)
                                                                                            ν) <
                                                                                        fixedNormalRadius p /
                                                                                          coefficientBound p →
                                                                                      √(DFunLike.coe
                                                                                              (DFunLike.coe
                                                                                                (g.inner
                                                                                                  (((coherentU.family
                                                                                                              (2)
                                                                                                              p).family.plaque
                                                                                                        q).param
                                                                                                    v))
                                                                                                μ)
                                                                                              μ) <
                                                                                          fixedNormalRadius p /
                                                                                            coefficientBound p →
                                                                                        riemannianExponential g
                                                                                              ⟨((coherentU.family
                                                                                                            (2)
                                                                                                            p).family.plaque
                                                                                                      q).param
                                                                                                  u,
                                                                                                ν⟩ =
                                                                                            riemannianExponential g
                                                                                              ⟨((coherentU.family
                                                                                                            (2)
                                                                                                            p).family.plaque
                                                                                                      q).param
                                                                                                  v,
                                                                                                μ⟩ →
                                                                                          u = v := by
  intro this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels coefficientRadius coefficientBound hCoefficientBound hCoefficient fixedTubeRadius fixedTubeLabels hFixedTubeLabels fixedNormalRadius tubeChart tubeTangentChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hFixedTubeEqual hTubeNormalSizeContinuous hTubeImageCenter tubeNormalSize p q hq u v hu hv ν μ hν hμ hνsmall hμsmall he
  have huC : u ∈ Metric.ball 0 (coefficientRadius p) := by
    rw [Metric.mem_ball,dist_zero_right]
    exact hu.trans_le (min_le_right _ _)
  have hvC : v ∈ Metric.ball 0 (coefficientRadius p) := by
    rw [Metric.mem_ball,dist_zero_right]
    exact hv.trans_le (min_le_right _ _)
  obtain ⟨huB,huA,huCoeff⟩ := hCoefficient p q hq.2 u huC
  obtain ⟨hvB,hvA,hvCoeff⟩ := hCoefficient p q hq.2 v hvC
  have huR : u ∈ Metric.closedBall 0 (fixedTubeRadius p) := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (hu.trans_le (min_le_left _ _)).le
  have hvR : v ∈ Metric.closedBall 0 (fixedTubeRadius p) := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (hv.trans_le (min_le_left _ _)).le
  exact HPS.native_physical_normal_uniqueness_g18 (coherentU.coherence 2 p) g
    ⟨p,(coherentU.family 2 p).family.center_mem⟩ q (fixedTubeRadius p)
    (fixedNormalRadius p) (coefficientBound p) (hCoefficientBound p)
    (fun z hz w hw heq ↦ hFixedTubeEqual p q hq.1 z w hz hw heq)
    u v huB hvB huR hvR huCoeff hvCoeff ν μ hν hμ hνsmall hμsmall he


end
end HolomorphicAnosov.Ghys
