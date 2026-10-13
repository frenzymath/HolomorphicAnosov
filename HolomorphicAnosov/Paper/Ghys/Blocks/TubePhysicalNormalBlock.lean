import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! The transported tube normal frame is orthogonal to the tangent space of the native plaque.
(Ghys, Prop. 2.2, pp. 588–590) -/

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
theorem TubePhysicalNormalBlock : ∀ {d : ℕ} {M : Type u}
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
                                                      let tubePhysicalNormal :
                                                        (p : M) →
                                                          (q :
                                                              (coherentU.family (2)
                                                                      p).family.centerDomain.Elem) →
                                                            (u :
                                                                Fin (coherentU.dimension (2) p) →
                                                                  ℝ) →
                                                              u ∈
                                                                  Metric.ball (0)
                                                                    (coherentU.family (2)
                                                                          p).family.radius →
                                                                ↥(tubeNormalSpace p) →
                                                                  TangentSpace (realModel d)
                                                                    (((coherentU.family (2)
                                                                                p).family.plaque
                                                                          q).param
                                                                      u) :=
                                                        fun (p : M)
                                                          (q :
                                                            (coherentU.family (2)
                                                                    p).family.centerDomain.Elem)
                                                          (u :
                                                            Fin (coherentU.dimension (2) p) → ℝ)
                                                          (hu :
                                                            u ∈
                                                              Metric.ball (0)
                                                                (coherentU.family (2)
                                                                      p).family.radius)
                                                          (k : ↥(tubeNormalSpace p)) =>
                                                        let P :
                                                          NativeEmbeddedPlaque 𝓘(ℝ, ComplexModel d)
                                                            a.splitting.unstable.toDistribution q.val :=
                                                          (coherentU.family (2) p).family.plaque
                                                            q;
                                                        let tr :
                                                          Bundle.Trivialization (ComplexModel d)
                                                            Bundle.TotalSpace.proj :=
                                                          trivializationAt (ComplexModel d) (TangentSpace (realModel d))
                                                            (coherentU.family (2)
                                                                  p).family.receivingAnchor;
                                                        let hx : P.param u ∈ tr.baseSet :=
                                                          id
                                                            (Eq.mp
                                                              (congrFun'
                                                                (congrArg Membership.mem
                                                                  (extChartAt_source 𝓘(ℝ, ComplexModel d)
                                                                    (coherentU.family (2)
                                                                          p).family.receivingAnchor))
                                                                (((coherentU.family (2)
                                                                            p).family.plaque
                                                                      q).param
                                                                  u))
                                                              ((coherentU.family (2)
                                                                      p).family.receiving_domain
                                                                q u hu));
                                                        let J :
                                                          TangentSpace (realModel d) (P.param u) ≃L[ℝ] ComplexModel d :=
                                                          Bundle.Trivialization.continuousLinearEquivAt ℝ tr (P.param u)
                                                            hx;
                                                        DFunLike.coe J.symm (DFunLike.coe (tubeNormal p q u) k);
                                                      ∀ (p : M)
                                                        (q :
                                                          (coherentU.family (2)
                                                                  p).family.centerDomain.Elem)
                                                        (u : Fin (coherentU.dimension (2) p) → ℝ)
                                                        (hu :
                                                          u ∈
                                                            Metric.ball (0)
                                                              (coherentU.family (2)
                                                                    p).family.radius)
                                                        (k : ↥(tubeNormalSpace p)),
                                                        ∀
                                                          v ∈
                                                            (mfderiv 𝓘(ℝ, Fin (coherentU.dimension 2 p) → ℝ) (realModel d)
                                                                  ((coherentU.family (2)
                                                                            p).family.plaque
                                                                      q).param
                                                                u).range,
                                                          DFunLike.coe
                                                              (DFunLike.coe
                                                                (g.inner
                                                                  (((coherentU.family (2)
                                                                              p).family.plaque
                                                                        q).param
                                                                    u))
                                                                (tubePhysicalNormal p q u hu k))
                                                              v =
                                                            0  := by
  intro d M inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 f hmetric hmetric_smooth this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels tubeChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal tubePhysicalNormal p q u hu k
  let Φ := coherentU.family 2 p
  let H := coherentU.coherence 2 p
  let P := Φ.family.plaque q
  have huP : u ∈ P.domain := by rw [Φ.family.domain_eq]; exact hu
  have hs := (P.smooth u huP).contMDiffAt (P.domain_open.mem_nhds huP)
  have heq : H.coordinate q =ᶠ[𝓝 u] ((tubeChart p) ∘ P.param) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hu] with v hv
    exact H.coordinate_eq q hv
  have hD : tubeDerivative p q u = fderiv ℝ ((tubeChart p) ∘ P.param) u := heq.fderiv_eq
  have hb : tubeTensor p q u = originalMetricChartTensor_g18 g Φ.family.receivingAnchor
      (tubeChart p (P.param u)) := by
    change originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q u) = _
    rw [H.coordinate_eq q hu]
  simp only [tubePhysicalNormal,tubeNormal,hD,hb]
  exact plaque_physical_normal_g18 g Φ.family.receivingAnchor P.param u
    (hs.mdifferentiableAt (by simp)) (P.immersed u huP)
    (Φ.family.receiving_domain q u hu) (tubeNormalSpace p).subtypeL k


end
end HolomorphicAnosov.Ghys
