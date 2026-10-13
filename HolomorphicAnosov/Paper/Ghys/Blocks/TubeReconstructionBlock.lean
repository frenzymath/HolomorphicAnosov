import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! The inverse tube coordinates reconstruct the ambient point through the original Riemannian
exponential. (Ghys, Prop. 2.2, pp. 588–590) -/

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
theorem TubeReconstructionBlock {d : ℕ} {M : Type u}
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
                                  ∀ (tubeDomain : M → Set (ComplexModel d × ComplexModel d)),
                                    (∀ (p : M),
                                        ∀ z ∈ tubeDomain p,
                                          z ∈
                                              (extChartAt 𝓘(ℝ, ComplexModel d).tangent
                                                  (⟨(coherentU.family 2 p).family.receivingAnchor, 0⟩ : TangentBundle (realModel d) M)).target ∧
                                            (extChartAt 𝓘(ℝ, ComplexModel d).tangent
                                                        (⟨(coherentU.family 2 p).family.receivingAnchor, 0⟩ : TangentBundle (realModel d) M)).symm.toFun
                                                  z ∈
                                                riemannianExponentialDomain g ∧
                                              riemannianExponential g
                                                  ((extChartAt 𝓘(ℝ, ComplexModel d).tangent
                                                          (⟨(coherentU.family 2 p).family.receivingAnchor, 0⟩ : TangentBundle (realModel d) M)).symm.toFun
                                                    z) ∈
                                                (extChartAt 𝓘(ℝ, ComplexModel d)
                                                    (coherentU.family (2)
                                                          p).family.receivingAnchor).source) →
                                      ∀
                                        (tubeLabels :
                                          (p : M) →
                                            TopologicalSpace.Opens
                                              (coherentU.family (2) p).family.centerDomain.Elem),
                                        (∀ (p : M),
                                            Subtype.mk p
                                                (coherentU.family (2) p).family.center_mem ∈
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
                                                                            (coherentU.dimension
                                                                              (2) p) →
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
                                                                            (coherentU.dimension
                                                                              (2) p) →
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
                                                (∀ (p : M) (p_1 : ↥(tubeLabels p)),
                                                    ((tubeInverse p p_1).toFun' =
                                                        fun
                                                          (z :
                                                            (Fin (coherentU.dimension (2) p) →
                                                                ℝ) ×
                                                              ↥(plaqueNormalSpace
                                                                  ((fun
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
                                                                                (coherentU.dimension
                                                                                  (2) p) →
                                                                              ℝ)) =>
                                                                      fderiv ℝ
                                                                        ((coherentU.coherence (2)
                                                                              p).coordinate
                                                                          z.1)
                                                                        z.2)
                                                                    (Subtype.mk p
                                                                        (coherentU.family (2)
                                                                              p).family.center_mem,
                                                                      0)))) =>
                                                        ((extChartAt 𝓘(ℝ, ComplexModel d)
                                                                (coherentU.family (2)
                                                                      p).family.receivingAnchor).toFun ∘
                                                            riemannianExponential g ∘
                                                              (extChartAt 𝓘(ℝ, ComplexModel d).tangent
                                                                    (⟨(coherentU.family 2 p).family.receivingAnchor, 0⟩ : TangentBundle (realModel d) M)).symm.toFun)
                                                          ((coherentU.coherence (2) p).coordinate
                                                              p_1.val z.1,
                                                            DFunLike.coe
                                                              ((fun
                                                                    (z :
                                                                      (coherentU.family (2)
                                                                                p).family.centerDomain.Elem ×
                                                                        (Fin
                                                                            (coherentU.dimension
                                                                              (2) p) →
                                                                          ℝ)) =>
                                                                  plaqueNormalFrame
                                                                    ((fun
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
                                                                          ((coherentU.coherence
                                                                                (2) p).coordinate
                                                                            z.1 z.2))
                                                                      z)
                                                                    ((fun
                                                                          (z :
                                                                            (coherentU.family (2)
                                                                                      p).family.centerDomain.Elem ×
                                                                              (Fin
                                                                                  (coherentU.dimension
                                                                                    (2) p) →
                                                                                ℝ)) =>
                                                                        fderiv ℝ
                                                                          ((coherentU.coherence
                                                                                (2) p).coordinate
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
                                                                                        (2) p) →
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
                                                                                        (2) p) →
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
                                                                (p_1.val, z.1))
                                                              z.2)) ∧
                                                      (tubeInverse p p_1).target = tubeImage p ∧
                                                        ContDiffOn ℝ (1)
                                                            (tubeInverse p p_1).toFun' (tubeInverse p p_1).source ∧
                                                          ContDiffOn ℝ (1)
                                                              (tubeInverse p p_1).symm.toFun'
                                                              (tubeInverse p p_1).target ∧
                                                            ∀ z ∈ (tubeInverse p p_1).source,
                                                              (p_1.val, z.1) ∈
                                                                  univ ×ˢ
                                                                    Metric.ball (0)
                                                                      (coherentU.family (2)
                                                                            p).family.radius ∧
                                                                ((coherentU.coherence (2)
                                                                          p).coordinate
                                                                      p_1.val z.1,
                                                                    DFunLike.coe
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
                                                                                                  (OfNat.ofNat
                                                                                                    (nat_lit 2))
                                                                                                  p).family.centerDomain.Elem ×
                                                                                          (Fin
                                                                                              (coherentU.dimension
                                                                                                (OfNat.ofNat
                                                                                                  (nat_lit 2))
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
                                                                                                  (OfNat.ofNat
                                                                                                    (nat_lit 2))
                                                                                                  p).family.centerDomain.Elem ×
                                                                                          (Fin
                                                                                              (coherentU.dimension
                                                                                                (OfNat.ofNat
                                                                                                  (nat_lit 2))
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
                                                                        (p_1.val, z.1))
                                                                      z.2) ∈
                                                                  tubeDomain p) →
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
                                                            let tubeTangentChart :
                                                              M →
                                                                PartialEquiv
                                                                  (Bundle.TotalSpace (ComplexModel d)
                                                                    (TangentSpace (realModel d)))
                                                                  (ComplexModel d × ComplexModel d) :=
                                                              fun (p : M) =>
                                                              extChartAt (realModel d).tangent
                                                                (⟨(coherentU.family 2 p).family.receivingAnchor, 0⟩ : TangentBundle (realModel d) M);
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
                                                                          (coherentU.dimension (2)
                                                                            p) →
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
                                                                have D :
                                                                  (coherentU.family (2)
                                                                              p).family.centerDomain.Elem ×
                                                                      (Fin
                                                                          (coherentU.dimension (2)
                                                                            p) →
                                                                        ℝ) →
                                                                    (Fin
                                                                          (coherentU.dimension (2)
                                                                            p) →
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
                                                                have b :
                                                                  (coherentU.family (2)
                                                                              p).family.centerDomain.Elem ×
                                                                      (Fin
                                                                          (coherentU.dimension (2)
                                                                            p) →
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
                                                                          (coherentU.dimension (2)
                                                                            p) →
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
                                                                have size :
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
                                                              ∀ (p : M) (q : ↥(tubeLabels p)),
                                                                ∀ x ∈ (tubeChart p).source,
                                                                  (tubeChart p).toFun x ∈ (tubeInverse p q).target →
                                                                    let z :
                                                                      (Fin
                                                                            (coherentU.dimension
                                                                              (2) p) →
                                                                          ℝ) ×
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
                                                                                0))) :=
                                                                      (tubeInverse p q).symm.toFun'
                                                                        ((tubeChart p).toFun x);
                                                                    let ξ :
                                                                      Bundle.TotalSpace (ComplexModel d)
                                                                        (TangentSpace (realModel d)) :=
                                                                      (tubeTangentChart p).symm.toFun
                                                                        ((coherentU.coherence (2)
                                                                                p).coordinate
                                                                            q.val z.1,
                                                                          DFunLike.coe (tubeNormal p q.val z.1) z.2);
                                                                    ξ ∈ riemannianExponentialDomain g ∧
                                                                      ξ.proj =
                                                                          ((coherentU.family (2)
                                                                                      p).family.plaque
                                                                                q.val).param
                                                                            z.1 ∧
                                                                        riemannianExponential g ξ = x := by
  intro this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeDomain hTubeGuard tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels tubeChart tubeTangentChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hTubeNormalSizeContinuous p q x hx ht
  dsimp only
  let z := (tubeInverse p q).symm (tubeChart p x)
  have hz : z ∈ (tubeInverse p q).source := (tubeInverse p q).map_target ht
  have hdom := (hTubeInverse p q).2.2.2.2 z hz
  have hguard := hTubeGuard p _ hdom.2
  refine ⟨hguard.2.1,?_,?_⟩
  · have hcoord := (coherentU.coherence 2 p).coordinate_eq q.val hdom.1.2
    change ((tubeTangentChart p).symm
      ((coherentU.coherence 2 p).coordinate q.val z.1,tubeNormal p q.val z.1 z.2)).proj = _
    rw [hcoord]
    exact congrArg Bundle.TotalSpace.proj
      (extChartAt_tangent_symm_fibre_g18 (coherentU.family 2 p).family.receivingAnchor _
        ((coherentU.family 2 p).family.receiving_domain q.val z.1 hdom.1.2) _)
  · apply (tubeChart p).injOn hguard.2.2 hx
    have hh := (tubeInverse p q).right_inv ht
    rw [(hTubeInverse p q).1] at hh
    exact hh



end
end HolomorphicAnosov.Ghys
