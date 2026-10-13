import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! Lifts of unstable plaque parametrizations to open embeddings in intrinsic unstable leaves. -/

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
/-- Unstable plaque parametrizations lift to open embeddings in the intrinsic unstable leaf. -/
theorem NativeLiftBlock : ∀ {d : ℕ} {M : Type u}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ChartedSpace (ComplexModel d) M] [inst_5 : IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M)
  (hmetric : HermitianTangentMetricCore d M) (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric),
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
                                          (Metric.isOpen_ball))
                                        (fun
                                            (z :
                                              Φ.family.centerDomain.Elem ×
                                                ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesU.dimension p₀) → ℝ) Φ.family.radius)
                                                    (Metric.isOpen_ball))) =>
                                          (Φ.family.plaque z.1).param z.2.val)
                                        (Subtype.mk 0
                                          (Metric.mem_ball_self Φ.family.radius_pos))) ∧
                                    ∀ (p : Φ.family.centerDomain.Elem), Φ.label p = labelU p.val) →
                                (∀ (N : ℕ) (p₀ : M),
                                    let Φ : HPS.FiniteC1NativePlaqueFamily Fu p₀ (coherentU.dimension N p₀) :=
                                      coherentU.family N p₀;
                                    Nonempty
                                        (HPS.SelectedFamilyGermRestriction (L := Lu) labelU discU mapU stagesU.center
                                          (coherentU.dimension N p₀) Φ.family.centerDomain
                                          (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (coherentU.dimension N p₀) → ℝ) Φ.family.radius)
                                            (Metric.isOpen_ball))
                                          (fun
                                              (z :
                                                Φ.family.centerDomain.Elem ×
                                                  ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (coherentU.dimension N p₀) → ℝ) Φ.family.radius)
                                                      (Metric.isOpen_ball))) =>
                                            (Φ.family.plaque z.1).param z.2.val)
                                          (Subtype.mk 0
                                            (Metric.mem_ball_self Φ.family.radius_pos))) ∧
                                      ∀ (p : Φ.family.centerDomain.Elem), Φ.label p = labelU p.val) →
                                  (∀ (p : M)
                                      (q : (coherentU.family 2 p).family.centerDomain.Elem),
                                      ∀
                                        v ∈
                                          Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                            (coherentU.family 2 p).family.radius,
                                        ForwardAsymptotic (DFunLike.coe (Diffeomorph.symm f)) q.val
                                          (((coherentU.family 2 p).family.plaque q).param v)) →
                                    ∀
                                      (tubeLabels :
                                        (p : M) →
                                          TopologicalSpace.Opens
                                            (coherentU.family 2 p).family.centerDomain.Elem),
                                      (∀ (p : M),
                                          Subtype.mk p
                                              (coherentU.family 2 p).family.center_mem ∈
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
                                                                    (coherentU.family 2
                                                                              p).family.centerDomain.Elem ×
                                                                      (Fin
                                                                          (coherentU.dimension 2
                                                                            p) →
                                                                        ℝ)) =>
                                                                originalMetricChartTensor_g18 g
                                                                  (coherentU.family 2
                                                                        p).family.receivingAnchor
                                                                  ((coherentU.coherence 2
                                                                        p).coordinate
                                                                    z.1 z.2))
                                                              (Subtype.mk p
                                                                  (coherentU.family 2
                                                                        p).family.center_mem,
                                                                OfNat.ofNat (nat_lit 0)))
                                                            ((fun
                                                                  (z :
                                                                    (coherentU.family 2
                                                                              p).family.centerDomain.Elem ×
                                                                      (Fin
                                                                          (coherentU.dimension 2
                                                                            p) →
                                                                        ℝ)) =>
                                                                fderiv ℝ
                                                                  ((coherentU.coherence 2
                                                                        p).coordinate
                                                                    z.1)
                                                                  z.2)
                                                              (Subtype.mk p
                                                                  (coherentU.family 2
                                                                        p).family.center_mem,
                                                                OfNat.ofNat (nat_lit 0)))))
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
                                                        (coherentU.family 2
                                                                p).family.centerDomain.Elem),
                                                  (∀ (p : M),
                                                      coefficientLabels p ∈
                                                        𝓝
                                                          (Subtype.mk p
                                                            (coherentU.family 2
                                                                  p).family.center_mem)) →
                                                    ∀
                                                      (fixedTubeLabels :
                                                        (p : M) →
                                                          Set
                                                            (coherentU.family 2
                                                                    p).family.centerDomain.Elem),
                                                      (∀ (p : M),
                                                          fixedTubeLabels p ∈
                                                            𝓝
                                                              (Subtype.mk p
                                                                (coherentU.family 2
                                                                      p).family.center_mem)) →
                                                        let tubeChart : M → PartialEquiv M (ComplexModel d) :=
                                                          fun (p : M) =>
                                                          extChartAt (realModel d)
                                                            (coherentU.family 2
                                                                  p).family.receivingAnchor;
                                                        let tubeTensor :
                                                          (p : M) →
                                                            (coherentU.family 2
                                                                      p).family.centerDomain.Elem →
                                                              (Fin (coherentU.dimension 2 p) →
                                                                  ℝ) →
                                                                ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ :=
                                                          fun (p : M)
                                                            (q :
                                                              (coherentU.family 2
                                                                      p).family.centerDomain.Elem)
                                                            (v :
                                                              Fin (coherentU.dimension 2 p) →
                                                                ℝ) =>
                                                          originalMetricChartTensor_g18 g
                                                            (coherentU.family 2
                                                                  p).family.receivingAnchor
                                                            ((coherentU.coherence 2
                                                                  p).coordinate
                                                              q v);
                                                        let tubeDerivative :
                                                          (p : M) →
                                                            (coherentU.family 2
                                                                      p).family.centerDomain.Elem →
                                                              (Fin (coherentU.dimension 2 p) →
                                                                  ℝ) →
                                                                (Fin (coherentU.dimension 2 p) →
                                                                    ℝ) →L[ℝ]
                                                                  ComplexModel d :=
                                                          fun (p : M)
                                                            (q :
                                                              (coherentU.family 2
                                                                      p).family.centerDomain.Elem)
                                                            (v :
                                                              Fin (coherentU.dimension 2 p) →
                                                                ℝ) =>
                                                          fderiv ℝ
                                                            ((coherentU.coherence 2
                                                                  p).coordinate
                                                              q)
                                                            v;
                                                        let tubeNormalSpace : M → Submodule ℝ (ComplexModel d) :=
                                                          fun (p : M) =>
                                                          plaqueNormalSpace
                                                            (tubeTensor p
                                                              (Subtype.mk p
                                                                (coherentU.family 2
                                                                      p).family.center_mem)
                                                              0)
                                                            (tubeDerivative p
                                                              (Subtype.mk p
                                                                (coherentU.family 2
                                                                      p).family.center_mem)
                                                              0);
                                                        let tubeNormal :
                                                          (p : M) →
                                                            (coherentU.family 2
                                                                      p).family.centerDomain.Elem →
                                                              (Fin (coherentU.dimension 2 p) →
                                                                  ℝ) →
                                                                ↥(tubeNormalSpace p) →L[ℝ] ComplexModel d :=
                                                          fun (p : M)
                                                            (q :
                                                              (coherentU.family 2
                                                                      p).family.centerDomain.Elem)
                                                            (v :
                                                              Fin (coherentU.dimension 2 p) →
                                                                ℝ) =>
                                                          plaqueNormalFrame (tubeTensor p q v) (tubeDerivative p q v)
                                                            (tubeNormalSpace p).subtypeL;
                                                        (∀ (p : M),
                                                            have D :
                                                              (coherentU.family 2
                                                                          p).family.centerDomain.Elem ×
                                                                  (Fin
                                                                      (coherentU.dimension 2
                                                                        p) →
                                                                    ℝ) →
                                                                (Fin (coherentU.dimension 2 p) →
                                                                    ℝ) →L[ℝ]
                                                                  ComplexModel d :=
                                                              fun
                                                                (z :
                                                                  (coherentU.family 2
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension 2
                                                                          p) →
                                                                      ℝ)) =>
                                                              fderiv ℝ
                                                                ((coherentU.coherence 2
                                                                      p).coordinate
                                                                  z.1)
                                                                z.2;
                                                            have b :
                                                              (coherentU.family 2
                                                                          p).family.centerDomain.Elem ×
                                                                  (Fin
                                                                      (coherentU.dimension 2
                                                                        p) →
                                                                    ℝ) →
                                                                ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ :=
                                                              fun
                                                                (z :
                                                                  (coherentU.family 2
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension 2
                                                                          p) →
                                                                      ℝ)) =>
                                                              originalMetricChartTensor_g18 g
                                                                (coherentU.family 2
                                                                      p).family.receivingAnchor
                                                                ((coherentU.coherence 2
                                                                      p).coordinate
                                                                  z.1 z.2);
                                                            let K : Submodule ℝ (ComplexModel d) :=
                                                              plaqueNormalSpace
                                                                (b
                                                                  (Subtype.mk p
                                                                      (coherentU.family 2
                                                                            p).family.center_mem,
                                                                    OfNat.ofNat (nat_lit 0)))
                                                                (D
                                                                  (Subtype.mk p
                                                                      (coherentU.family 2
                                                                            p).family.center_mem,
                                                                    OfNat.ofNat (nat_lit 0)));
                                                            have N :
                                                              (coherentU.family 2
                                                                          p).family.centerDomain.Elem ×
                                                                  (Fin
                                                                      (coherentU.dimension 2
                                                                        p) →
                                                                    ℝ) →
                                                                ↥K →L[ℝ] ComplexModel d :=
                                                              fun
                                                                (z :
                                                                  (coherentU.family 2
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension 2
                                                                          p) →
                                                                      ℝ)) =>
                                                              plaqueNormalFrame (b z) (D z) K.subtypeL;
                                                            have size :
                                                              ((coherentU.family 2
                                                                            p).family.centerDomain.Elem ×
                                                                    (Fin
                                                                        (coherentU.dimension 2
                                                                          p) →
                                                                      ℝ)) ×
                                                                  ↥K →
                                                                ℝ :=
                                                              fun
                                                                (z :
                                                                  ((coherentU.family 2
                                                                              p).family.centerDomain.Elem ×
                                                                      (Fin
                                                                          (coherentU.dimension 2
                                                                            p) →
                                                                        ℝ)) ×
                                                                    ↥K) =>
                                                              √(DFunLike.coe
                                                                  (DFunLike.coe (b z.1) (DFunLike.coe (N z.1) z.2))
                                                                  (DFunLike.coe (N z.1) z.2));
                                                            ContinuousAt size
                                                                ((Subtype.mk p
                                                                      (coherentU.family 2
                                                                            p).family.center_mem,
                                                                    OfNat.ofNat (nat_lit 0)),
                                                                  OfNat.ofNat (nat_lit 0)) ∧
                                                              size
                                                                  ((Subtype.mk p
                                                                        (coherentU.family 2
                                                                              p).family.center_mem,
                                                                      OfNat.ofNat (nat_lit 0)),
                                                                    OfNat.ofNat (nat_lit 0)) =
                                                                OfNat.ofNat (nat_lit 0)) →
                                                          (∀ (p : M), (tubeChart p).toFun p ∈ tubeImage p) →
                                                            let tubeNormalSize :
                                                              (p : M) →
                                                                ((coherentU.family 2
                                                                              p).family.centerDomain.Elem ×
                                                                      (Fin
                                                                          (coherentU.dimension 2
                                                                            p) →
                                                                        ℝ)) ×
                                                                    ↥(tubeNormalSpace p) →
                                                                  ℝ :=
                                                              fun (p : M)
                                                                (z :
                                                                  ((coherentU.family 2
                                                                              p).family.centerDomain.Elem ×
                                                                      (Fin
                                                                          (coherentU.dimension 2
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
                                                                    (coherentU.family 2
                                                                            p).family.centerDomain.Elem),
                                                              (∀ (p : M),
                                                                  speedCore p ∈
                                                                    𝓝
                                                                      (Subtype.mk p
                                                                        (coherentU.family 2
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
                                                                              OfNat.ofNat (nat_lit 2)) →
                                                                          ℝ)
                                                                        M :=
                                                                      L.realAmbientCharts;
                                                                    ∀ (p : M)
                                                                      (q :
                                                                        (coherentU.family 2
                                                                                p).family.centerDomain.Elem)
                                                                      (x : M),
                                                                      ForwardAsymptotic
                                                                          (DFunLike.coe (Diffeomorph.symm f)) x q.val →
                                                                        let B :
                                                                          TopologicalSpace.Opens
                                                                            (Fin
                                                                                (coherentU.dimension
                                                                                  2 p) →
                                                                              ℝ) :=
                                                                          TopologicalSpace.Opens.mk
                                                                            (Metric.ball (0 : Fin (coherentU.dimension 2 p) → ℝ)
                                                                              (coherentU.family
                                                                                    2
                                                                                    p).family.radius)
                                                                            Metric.isOpen_ball;
                                                                        ∃ (l : ↥B → L.U x),
                                                                          (∀ (v : ↥B),
                                                                              (l v).val =
                                                                                ((coherentU.family
                                                                                            2
                                                                                            p).family.plaque
                                                                                      q).param
                                                                                  v.val) ∧
                                                                            IsLocalDiffeomorph
                                                                                𝓘(ℝ,
                                                                                  Fin
                                                                                      (coherentU.dimension
                                                                                        2 p) →
                                                                                    ℝ)
                                                                                (L.uModel x) ∞ l ∧
                                                                              IsOpenEmbedding l := by
  intro d M inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 f hmetric hmetric_smooth this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU hNativeUnstableAsymptotic tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels tubeChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hTubeNormalSizeContinuous hTubeImageCenter tubeNormalSize speedCore hSpeedCoreCenter speedCover hSpeedCoverOpen hSpeedCoverCenter this p q x hclass
  letI := L.identification.unstableTopology x
  letI := L.identification.unstableCharts x
  let Φ := coherentU.family 2 p
  let P := Φ.family.plaque q
  let B : Opens (Fin (coherentU.dimension 2 p) → ℝ) :=
    ⟨Metric.ball 0 Φ.family.radius, Metric.isOpen_ball⟩
  let j : B → M := fun v ↦ P.param v.val
  have hv (v : B) : v.val ∈ P.domain := by
    rw [Φ.family.domain_eq q]
    exact v.property
  have hj : ContMDiff 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d) ∞ j := by
    intro v
    exact contMDiffAt_subtype_iff.mpr
      ((P.smooth v.val (hv v)).contMDiffAt (P.domain_open.mem_nhds (hv v)))
  have hd (v : B) : mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d) j v =
      (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d) P.param v.val).comp
        (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ)
          𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ)
          (Subtype.val : B → (Fin (coherentU.dimension 2 p) → ℝ)) v) :=
    mfderiv_comp v
      (((P.smooth v.val (hv v)).contMDiffAt
        (P.domain_open.mem_nhds (hv v))).mdifferentiableAt (by simp))
      (contMDiff_subtype_val.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  have hji (v : B) : Function.Injective
      (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d) j v) := by
    rw [hd]
    exact (P.immersed v.val (hv v)).comp
      (openSubsetInclusion_mfderiv_bijective 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) B v).injective
  have hT (v : B) : (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ)
      (realModel d) j v).range = a.splitting.unstable.toDistribution (j v) := by
    rw [hd, ← P.tangent v.val (hv v)]
    apply LinearMap.range_comp_of_range_eq_top
    exact LinearMap.range_eq_top.mpr
      (openSubsetInclusion_mfderiv_bijective 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) B v).surjective
  letI := (L.unstable x).smoothAtlas
  letI := (L.unstable x).secondCountable
  letI := L.foliation.unstableTopology (Quotient.mk L.foliation.unstablePartition x)
  let e := L.identification.unstableClassHomeomorph x
  letI : SecondCountableTopology (L.foliation.ULeaf x) := e.secondCountableTopology
  letI : LocallyConnectedSpace B :=
    ChartedSpace.locallyConnectedSpace (Fin (coherentU.dimension 2 p) → ℝ) B
  let l : B → L.U x := fun v ↦
    ⟨j v, by
      apply squeeze_zero (fun _ ↦ dist_nonneg)
        (fun n ↦ dist_triangle ((f.symm^[n]) (j v)) ((f.symm^[n]) q.val) ((f.symm^[n]) x))
      simpa only [add_zero] using
        (hNativeUnstableAsymptotic p q v.val v.property).add hclass⟩
  have he (z : L.U x) : (e.symm z).val = z.val := by
    have h := L.identification.unstable_points x (e.symm z)
    change (e (e.symm z)).val = _ at h
    exact h.symm.trans (congrArg Subtype.val (e.apply_symm_apply z))
  have hc₀ : Continuous (e.symm ∘ l) := by
    apply continuous_unstable_leaf_lift_g1 L.foliation _ inferInstance (e.symm ∘ l)
    have hpoint : (fun x : B ↦ ((e.symm ∘ l) x).val) = j :=
      funext fun x ↦ he (l x)
    rw [hpoint]
    exact hj.continuous
  have hc : Continuous l := by
    have hh := e.continuous.comp hc₀
    have heq : e ∘ (e.symm ∘ l) = l := funext fun x ↦ e.apply_symm_apply (l x)
    rw [heq] at hh
    exact hh
  have hr (v : B) : (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ)
      (realModel d) j v).range =
      (mfderiv (L.uModel x) (realModel d) (Subtype.val : L.U x → M) (l v)).range := by
    rw [hT v, (L.unstable x).tangent_image]
  obtain ⟨hlocal,hopen⟩ := immersed_leaf_lift_local_diffeomorph j
    (Subtype.val : L.U x → M) l hj (L.unstable x).inclusion_smooth
    hji (L.unstable x).inclusion_immersion hc rfl hr
  refine ⟨l, fun _ ↦ rfl, hlocal, hopen ?_⟩
  intro v w h
  apply Subtype.ext
  exact congrArg (fun z : P.domain ↦ z.val) (P.embedded.injective (a₁ := ⟨v.val,hv v⟩)
    (a₂ := ⟨w.val,hv w⟩) h)


end
end HolomorphicAnosov.Ghys
