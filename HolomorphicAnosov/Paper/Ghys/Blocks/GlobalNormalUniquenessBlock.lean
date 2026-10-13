import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! Uniform normal uniqueness for rank-one unstable plaques. (Ghys, Prop. 2.2) -/

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
/-- There are uniform positive radii such that nearby points on an unstable leaf with
small normal vectors and equal exponential images coincide. (Ghys, Prop. 2.2) -/
theorem GlobalNormalUniquenessBlock {d : ℕ} {M : Type u}
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
                                        (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin _ → ℝ) Φ.family.radius)
                                          (Metric.isOpen_ball))
                                        (fun
                                            (z :
                                              Φ.family.centerDomain.Elem ×
                                                ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin _ → ℝ) Φ.family.radius)
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
                                          (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin _ → ℝ) Φ.family.radius)
                                            (Metric.isOpen_ball))
                                          (fun
                                              (z :
                                                Φ.family.centerDomain.Elem ×
                                                  ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin _ → ℝ) Φ.family.radius)
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
                                                  ∀ (coefficientRadius : M → ℝ),
                                                    (∀ (p : M), 0 < coefficientRadius p) →
                                                      ∀ (coefficientBound : M → ℝ),
                                                        (∀ (p : M), 0 < coefficientBound p) →
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
                                                                  ∀ (fixedNormalRadius : M → ℝ),
                                                                    (∀ (p : M),
                                                                        0 < fixedNormalRadius p) →
                                                                      let tubeChart :
                                                                        M → PartialEquiv M (ComplexModel d) :=
                                                                        fun (p : M) =>
                                                                        extChartAt (realModel d)
                                                                          (coherentU.family (2)
                                                                                p).family.receivingAnchor;
                                                                      let tubeTensor :
                                                                        (p : M) →
                                                                          (coherentU.family (2)
                                                                                    p).family.centerDomain.Elem →
                                                                            (Fin
                                                                                  (coherentU.dimension
                                                                                    (2) p) →
                                                                                ℝ) →
                                                                              ComplexModel d →L[ℝ]
                                                                                ComplexModel d →L[ℝ] ℝ :=
                                                                        fun (p : M)
                                                                          (q :
                                                                            (coherentU.family (2)
                                                                                    p).family.centerDomain.Elem)
                                                                          (v :
                                                                            Fin
                                                                                (coherentU.dimension
                                                                                  (2) p) →
                                                                              ℝ) =>
                                                                        originalMetricChartTensor_g18 g
                                                                          (coherentU.family (2)
                                                                                p).family.receivingAnchor
                                                                          ((coherentU.coherence
                                                                                (2) p).coordinate
                                                                            q v);
                                                                      let tubeDerivative :
                                                                        (p : M) →
                                                                          (coherentU.family (2)
                                                                                    p).family.centerDomain.Elem →
                                                                            (Fin
                                                                                  (coherentU.dimension
                                                                                    (2) p) →
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
                                                                                (coherentU.dimension
                                                                                  (2) p) →
                                                                              ℝ) =>
                                                                        fderiv ℝ
                                                                          ((coherentU.coherence
                                                                                (2) p).coordinate
                                                                            q)
                                                                          v;
                                                                      let tubeNormalSpace :
                                                                        M → Submodule ℝ (ComplexModel d) :=
                                                                        fun (p : M) =>
                                                                        plaqueNormalSpace
                                                                          (tubeTensor p
                                                                            (Subtype.mk p
                                                                              (coherentU.family
                                                                                    (2)
                                                                                    p).family.center_mem)
                                                                            (0))
                                                                          (tubeDerivative p
                                                                            (Subtype.mk p
                                                                              (coherentU.family
                                                                                    (2)
                                                                                    p).family.center_mem)
                                                                            (0));
                                                                      let tubeNormal :
                                                                        (p : M) →
                                                                          (coherentU.family (2)
                                                                                    p).family.centerDomain.Elem →
                                                                            (Fin
                                                                                  (coherentU.dimension
                                                                                    (2) p) →
                                                                                ℝ) →
                                                                              ↥(tubeNormalSpace p) →L[ℝ]
                                                                                ComplexModel d :=
                                                                        fun (p : M)
                                                                          (q :
                                                                            (coherentU.family (2)
                                                                                    p).family.centerDomain.Elem)
                                                                          (v :
                                                                            Fin
                                                                                (coherentU.dimension
                                                                                  (2) p) →
                                                                              ℝ) =>
                                                                        plaqueNormalFrame (tubeTensor p q v)
                                                                          (tubeDerivative p q v)
                                                                          (tubeNormalSpace p).subtypeL;
                                                                      (∀ (p : M),
                                                                          have D :
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
                                                                              z.2;
                                                                          have b :
                                                                            (coherentU.family (2)
                                                                                        p).family.centerDomain.Elem ×
                                                                                (Fin
                                                                                    (coherentU.dimension
                                                                                      (2) p) →
                                                                                  ℝ) →
                                                                              ComplexModel d →L[ℝ]
                                                                                ComplexModel d →L[ℝ] ℝ :=
                                                                            fun
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
                                                                          have N :
                                                                            (coherentU.family (2)
                                                                                        p).family.centerDomain.Elem ×
                                                                                (Fin
                                                                                    (coherentU.dimension
                                                                                      (2) p) →
                                                                                  ℝ) →
                                                                              ↥K →L[ℝ] ComplexModel d :=
                                                                            fun
                                                                              (z :
                                                                                (coherentU.family
                                                                                          (2)
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
                                                                                ((coherentU.family
                                                                                            (2)
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
                                                                        (∀ (p : M),
                                                                            (tubeChart p).toFun p ∈ tubeImage p) →
                                                                          let tubeNormalSize :
                                                                            (p : M) →
                                                                              ((coherentU.family
                                                                                            (2)
                                                                                            p).family.centerDomain.Elem ×
                                                                                    (Fin
                                                                                        (coherentU.dimension
                                                                                          (2) p) →
                                                                                      ℝ)) ×
                                                                                  ↥(tubeNormalSpace p) →
                                                                                ℝ :=
                                                                            fun (p : M)
                                                                              (z :
                                                                                ((coherentU.family
                                                                                            (2)
                                                                                            p).family.centerDomain.Elem ×
                                                                                    (Fin
                                                                                        (coherentU.dimension
                                                                                          (2) p) →
                                                                                      ℝ)) ×
                                                                                  ↥(tubeNormalSpace p)) =>
                                                                            √(DFunLike.coe
                                                                                (DFunLike.coe (tubeTensor p z.1.1 z.1.2)
                                                                                  (DFunLike.coe
                                                                                    (tubeNormal p z.1.1 z.1.2) z.2))
                                                                                (DFunLike.coe (tubeNormal p z.1.1 z.1.2)
                                                                                  z.2));
                                                                          (∀ (p : M),
                                                                              ∀
                                                                                q ∈
                                                                                  fixedTubeLabels p ∩
                                                                                    coefficientLabels p,
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
                                                                                                    riemannianExponential
                                                                                                      g
                                                                                                      ⟨((coherentU.family
                                                                                                                    (2)
                                                                                                                    p).family.plaque
                                                                                                              q).param
                                                                                                          v,
                                                                                                        μ⟩ →
                                                                                                  u = v) →
                                                                            ∀
                                                                              (speedCore :
                                                                                (p : M) →
                                                                                  Set
                                                                                    (coherentU.family
                                                                                            (2)
                                                                                            p).family.centerDomain.Elem),
                                                                              (∀ (p : M),
                                                                                  speedCore p ∈
                                                                                    𝓝
                                                                                      (Subtype.mk p
                                                                                        (coherentU.family
                                                                                              (2)
                                                                                              p).family.center_mem)) →
                                                                                let speedCover : M → Set M :=
                                                                                  fun (p : M) =>
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
                                                                                    ∀ (lowerBound : M → ℝ),
                                                                                      (∀ (p : M),
                                                                                          0 <
                                                                                            lowerBound p) →
                                                                                        (∀ (p : M) (q : (coherentU.family 2 p).family.centerDomain) (hqK : q ∈ speedCore p) (x : M) (hclass : ForwardAsymptotic (f.symm : M → M) x q.val) (R : ℝ) (hR : 0 < R) (hRδ : R < (coherentU.family 2 p).family.radius / 2),
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
                ((coherentU.family 2 p).family.plaque q).param (J (c y)) = y.val) →
∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧ ∀ x : M,
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
          riemannianExponential g ξ = riemannianExponential g ζ → w₁ = w₂ := by
  intro this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius coefficientBound hCoefficientBound fixedTubeRadius hFixedTubeRadius fixedTubeLabels hFixedTubeLabels fixedNormalRadius hFixedNormalRadius tubeChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hTubeNormalSizeContinuous hTubeImageCenter tubeNormalSize hNativeNormalUniqueness speedCore hSpeedCoreCenter speedCover hSpeedCoverOpen hSpeedCoverCenter this lowerBound hLowerBound hNativeConfinement
  let R (p : M) := min (min (fixedTubeRadius p) (coefficientRadius p))
    ((coherentU.family 2 p).family.radius / 2) / 2
  have hR (p : M) : 0 < R p := half_pos
    (lt_min (lt_min (hFixedTubeRadius p) (hCoefficientRadius p))
      (half_pos (coherentU.family 2 p).family.radius_pos))
  have hRnative (p : M) : R p < (coherentU.family 2 p).family.radius / 2 :=
    (half_lt_self (lt_min (lt_min (hFixedTubeRadius p) (hCoefficientRadius p))
      (half_pos (coherentU.family 2 p).family.radius_pos))).trans_le (min_le_right _ _)
  have hRcore (p : M) : R p < min (fixedTubeRadius p) (coefficientRadius p) :=
    (half_lt_self (lt_min (lt_min (hFixedTubeRadius p) (hCoefficientRadius p))
      (half_pos (coherentU.family 2 p).family.radius_pos))).trans_le (min_le_left _ _)
  obtain ⟨T,hT⟩ := isCompact_univ.elim_finite_subcover speedCover hSpeedCoverOpen
    (fun p _ ↦ mem_iUnion.mpr ⟨p,hSpeedCoverCenter p⟩)
  have hTne : T.Nonempty := by
    obtain ⟨p⟩ := hM
    obtain ⟨q,hq,_⟩ := mem_iUnion₂.mp (hT (mem_univ p))
    exact ⟨q,hq⟩
  let δ := T.inf' hTne (fun p ↦ lowerBound p * R p)
  let η := T.inf' hTne (fun p ↦ fixedNormalRadius p / coefficientBound p)
  have hδ : 0 < δ := (Finset.lt_inf'_iff hTne).mpr
    (fun p _ ↦ mul_pos (hLowerBound p) (hR p))
  have hη : 0 < η := (Finset.lt_inf'_iff hTne).mpr
    (fun p _ ↦ div_pos (hFixedNormalRadius p) (hCoefficientBound p))
  refine ⟨δ,η,hδ,hη,?_⟩
  intro x
  letI := L.identification.unstableTopology x
  letI := L.identification.unstableCharts x
  intro anchor w₁ w₂ hd₁ hd₂ ξ ζ hξ hζ hξs hζs hξn hζn hexp
  obtain ⟨p,hp,hpa⟩ := mem_iUnion₂.mp (hT (mem_univ anchor.val))
  obtain ⟨q,hq,hqa⟩ := hpa
  have hqcore := interior_subset hq
  have hclass : ForwardAsymptotic (f.symm : M → M) x q.val := by
    rw [hqa]
    exact anchor.property
  obtain ⟨J,c,hc,center,hcenter,hcsource,hc0,hconf⟩ :=
    hNativeConfinement p q hqcore.1 x hclass (R p) (hR p) (hRnative p)
  have hca : center = anchor := Subtype.ext (hcenter.trans hqa)
  have hδp : δ ≤ lowerBound p * R p := Finset.inf'_le _ hp
  have hηp : η ≤ fixedNormalRadius p / coefficientBound p := Finset.inf'_le _ hp
  obtain ⟨hw₁,hu₁,huval⟩ := hconf w₁ (by
    rw [hca]
    exact hd₁.trans_le (ENNReal.ofReal_le_ofReal hδp))
  obtain ⟨hw₂,hu₂,hvval⟩ := hconf w₂ (by
    rw [hca]
    exact hd₂.trans_le (ENNReal.ofReal_le_ofReal hδp))
  have hpair : J (c w₁) = J (c w₂) := by
    have hxbase := hξ.trans huval.symm
    have hzbase := hζ.trans hvval.symm
    rcases ξ with ⟨bξ,ν⟩
    rcases ζ with ⟨bζ,μ⟩
    change bξ = _ at hxbase
    change bζ = _ at hzbase
    subst bξ
    subst bζ
    exact hNativeNormalUniqueness p q hqcore.2 (J (c w₁)) (J (c w₂))
      (hu₁.trans (hRcore p)) (hu₂.trans (hRcore p)) ν μ hξn hζn
      (hξs.trans_le hηp) (hζs.trans_le hηp) hexp
  exact c.injOn hw₁ hw₂ (J.injective hpair)


end
end HolomorphicAnosov.Ghys
