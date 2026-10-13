import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18
import HolomorphicAnosov.Geometry.HolomorphicCoordinateOrientationG18
import HolomorphicAnosov.Analysis.UniqueSmallSelectionG18

open Manifold MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Bundle
namespace HolomorphicAnosov.Ghys
noncomputable section
open Set Filter _root_.Topology
universe u
attribute [local instance] complex_isManifold_real Classical.propDecidable
set_option backward.isDefEq.respectTransparency false in
/-- The expanded intrinsic plaque comparison has positive complex orientation and
near-isometry bounds inherited from the native metric-normal projection.
(Ghys, Prop. 2.2) -/
theorem ExpandedControlBlock {d : Nat} {M : Type u}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ChartedSpace (ComplexModel d) M] [inst_5 : IsManifold (complexModel d) (WithTop.some Top.top) M]
  (f : Biholomorph d d M M) (hmetric : HermitianTangentMetricCore d M)
  (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric) :
  let _this_1 : MetricSpace M := rankComparisonMetric (d := d);
  Nonempty M →
    let _realManifold : IsManifold (realModel d) (WithTop.some Top.top) M := complex_isManifold_real d M;
    let originalAmbientMetric : MetricSpace M := inferInstance;
    let g :
      Bundle.ContMDiffRiemannianMetric (realModel d) (WithTop.some Top.top) (ComplexModel d) fun (x : M) =>
        TangentSpace (realModel d) x :=
      StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth;
    ∀ (a : AnosovDatum f),
      Nonempty
          (TensorAnosovBounds f.toReal a.splitting
            (StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth)) →
        ∀ (ιs : Type u) (Ls : ιs → Type u) (rs : ιs → Nat) (_ts : (i : ιs) → TopologicalSpace (Ls i))
          (_cs : (i : ιs) → ChartedSpace (Fin (rs i) → Real) (Ls i))
          (_ss : ∀ (i : ιs), IsManifold (modelWithCornersSelf Real (Fin (rs i) → Real)) (WithTop.some Top.top) (Ls i))
          (Fs : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls rs),
          Nonempty (HPS.LeafDynamicalInvariance Fs f.toReal) →
            ∀ (ιu : Type u) (Lu : ιu → Type u) (ru : ιu → Nat) (_tu : (i : ιu) → TopologicalSpace (Lu i))
              (_cu : (i : ιu) → ChartedSpace (Fin (ru i) → Real) (Lu i))
              (_su :
                ∀ (i : ιu), IsManifold (modelWithCornersSelf Real (Fin (ru i) → Real)) (WithTop.some Top.top) (Lu i))
              (Fu : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu ru),
              Nonempty (HPS.LeafDynamicalInvariance Fu f.toReal) →
                ∀ (coherentU : HPS.SelectedFiniteOrderNativePlaqueFamilies Fu),
                  let _nativeNorm : (p : M) → NormedAddCommGroup (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real) :=
                    fun (_p : M) => inferInstance;
                  let _nativeSpace : (p : M) → NormedSpace Real (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real) :=
                    fun (_p : M) => inferInstance;
                  let _nativeFinite :
                    ∀ (p : M), FiniteDimensional Real (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real) :=
                    fun (_p : M) => inferInstance;
                  ∀ (L : RankOneNativeLeaves f a.splitting),
                    let nativeTopology :
                      (p : M) → TopologicalSpace (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f) p) :=
                      fun (p : M) => L.identification.unstableTopology p;
                    let nativeCharts :
                      (p : M) →
                        ChartedSpace (Fin (L.unstable p).rank → Real)
                          (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f) p) :=
                      fun (p : M) => L.identification.unstableCharts p;
                    let nativeIterate :
                      (k : Nat) →
                        (x : M) →
                          let _this : TopologicalSpace (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f) x) :=
                            nativeTopology x;
                          let _this :
                            ChartedSpace (Fin (L.unstable x).rank → Real)
                              (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f) x) :=
                            nativeCharts x;
                          let _this :
                            TopologicalSpace
                              (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                (Nat.iterate (DFunLike.coe f) k x)) :=
                            nativeTopology (Nat.iterate (DFunLike.coe f) k x);
                          let _this :
                            ChartedSpace (Fin (L.unstable (Nat.iterate (DFunLike.coe f) k x)).rank → Real)
                              (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                (Nat.iterate (DFunLike.coe f) k x)) :=
                            nativeCharts (Nat.iterate (DFunLike.coe f) k x);
                          Diffeomorph (L.uModel x) (L.uModel (Nat.iterate (DFunLike.coe f) k x)) (L.U x)
                            (L.U (Nat.iterate (DFunLike.coe f) k x)) (WithTop.some Top.top) :=
                      fun (k : Nat) (x : M) => L.iterateUnstable k x;
                    ∀ (tubeDomain : M → Set (Prod (ComplexModel d) (ComplexModel d)))
                      (tubeLabels : (p : M) → TopologicalSpace.Opens (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem)
                      (tubeImage : M → Set (ComplexModel d))
                      (tubeInverse :
                        (p : M) →
                          (Subtype fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                              Membership.mem (tubeLabels p) x) →
                            OpenPartialHomeomorph
                              (Prod (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)
                                (Subtype fun (x : ComplexModel d) =>
                                  Membership.mem
                                    (plaqueNormalSpace
                                      ((fun
                                            (z :
                                              Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                          originalMetricChartTensor_g18 g
                                            (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                            ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1 z.2))
                                        (Prod.mk (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                          (OfNat.ofNat 0)))
                                      ((fun
                                            (z :
                                              Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                          fderiv Real ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1) z.2)
                                        (Prod.mk (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                          (OfNat.ofNat 0))))
                                    x))
                              (ComplexModel d)),
                      (∀ (p : M)
                          (p_1 :
                            Subtype fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                              Membership.mem (tubeLabels p) x),
                          And
                            (Eq (tubeInverse p p_1).toFun'
                              fun
                                (z :
                                  Prod (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)
                                    (Subtype fun (x : ComplexModel d) =>
                                      Membership.mem
                                        (plaqueNormalSpace
                                          ((fun
                                                (z :
                                                  Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                    (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                              originalMetricChartTensor_g18 g
                                                (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                                ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1 z.2))
                                            (Prod.mk
                                              (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                              (OfNat.ofNat 0)))
                                          ((fun
                                                (z :
                                                  Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                    (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                              fderiv Real ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1) z.2)
                                            (Prod.mk
                                              (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                              (OfNat.ofNat 0))))
                                        x)) =>
                              Function.comp
                                (extChartAt (modelWithCornersSelf Real (ComplexModel d))
                                    (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor).toFun
                                (Function.comp (riemannianExponential g)
                                  (extChartAt (modelWithCornersSelf Real (ComplexModel d)).tangent
                                        (Bundle.TotalSpace.mk
                                          (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                          (OfNat.ofNat 0))).symm.toFun)
                                (Prod.mk ((coherentU.coherence (OfNat.ofNat 2) p).coordinate p_1.val z.1)
                                  (DFunLike.coe
                                    ((fun
                                          (z :
                                            Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                              (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                        plaqueNormalFrame
                                          ((fun
                                                (z :
                                                  Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                    (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                              originalMetricChartTensor_g18 g
                                                (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                                ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1 z.2))
                                            z)
                                          ((fun
                                                (z :
                                                  Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                    (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                              fderiv Real ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1) z.2)
                                            z)
                                          (plaqueNormalSpace
                                              ((fun
                                                    (z :
                                                      Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                        (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                  originalMetricChartTensor_g18 g
                                                    (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                                    ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1 z.2))
                                                (Prod.mk
                                                  (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                  (OfNat.ofNat 0)))
                                              ((fun
                                                    (z :
                                                      Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                        (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                  fderiv Real ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1)
                                                    z.2)
                                                (Prod.mk
                                                  (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                  (OfNat.ofNat 0)))).subtypeL)
                                      (Prod.mk p_1.val z.1))
                                    z.2)))
                            (And (Eq (tubeInverse p p_1).target (tubeImage p))
                              (And
                                (ContDiffOn Real (OfNat.ofNat 1) (tubeInverse p p_1).toFun' (tubeInverse p p_1).source)
                                (And
                                  (ContDiffOn Real (OfNat.ofNat 1) (tubeInverse p p_1).symm.toFun'
                                    (tubeInverse p p_1).target)
                                  (∀
                                    (z :
                                      Prod (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)
                                        (Subtype fun (x : ComplexModel d) =>
                                          Membership.mem
                                            (plaqueNormalSpace
                                              ((fun
                                                    (z :
                                                      Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                        (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                  originalMetricChartTensor_g18 g
                                                    (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                                    ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1 z.2))
                                                (Prod.mk
                                                  (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                  (OfNat.ofNat 0)))
                                              ((fun
                                                    (z :
                                                      Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                        (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                  fderiv Real ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1)
                                                    z.2)
                                                (Prod.mk
                                                  (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                  (OfNat.ofNat 0))))
                                            x)),
                                    Membership.mem (tubeInverse p p_1).source z →
                                      And
                                        (Membership.mem
                                          (SProd.sprod univ
                                            (Metric.ball (OfNat.ofNat 0)
                                              (coherentU.family (OfNat.ofNat 2) p).family.radius))
                                          (Prod.mk p_1.val z.1))
                                        (Membership.mem (tubeDomain p)
                                          (Prod.mk ((coherentU.coherence (OfNat.ofNat 2) p).coordinate p_1.val z.1)
                                            (DFunLike.coe
                                              ((fun
                                                    (z :
                                                      Prod (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem
                                                        (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                  plaqueNormalFrame
                                                    ((fun
                                                          (z :
                                                            Prod
                                                              (coherentU.family (OfNat.ofNat 2)
                                                                      p).family.centerDomain.Elem
                                                              (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                        originalMetricChartTensor_g18 g
                                                          (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                                          ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1 z.2))
                                                      z)
                                                    ((fun
                                                          (z :
                                                            Prod
                                                              (coherentU.family (OfNat.ofNat 2)
                                                                      p).family.centerDomain.Elem
                                                              (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                        fderiv Real
                                                          ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1) z.2)
                                                      z)
                                                    (plaqueNormalSpace
                                                        ((fun
                                                              (z :
                                                                Prod
                                                                  (coherentU.family (OfNat.ofNat 2)
                                                                          p).family.centerDomain.Elem
                                                                  (Fin (coherentU.dimension (OfNat.ofNat 2) p) →
                                                                    Real)) =>
                                                            originalMetricChartTensor_g18 g
                                                              (coherentU.family (OfNat.ofNat 2)
                                                                    p).family.receivingAnchor
                                                              ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1
                                                                z.2))
                                                          (Prod.mk
                                                            (Subtype.mk p
                                                              (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                            (OfNat.ofNat 0)))
                                                        ((fun
                                                              (z :
                                                                Prod
                                                                  (coherentU.family (OfNat.ofNat 2)
                                                                          p).family.centerDomain.Elem
                                                                  (Fin (coherentU.dimension (OfNat.ofNat 2) p) →
                                                                    Real)) =>
                                                            fderiv Real
                                                              ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1)
                                                              z.2)
                                                          (Prod.mk
                                                            (Subtype.mk p
                                                              (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                            (OfNat.ofNat 0)))).subtypeL)
                                                (Prod.mk p_1.val z.1))
                                              z.2)))))))) →
                        let tubeChart : M → PartialEquiv M (ComplexModel d) := fun (p : M) =>
                          extChartAt (realModel d) (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor;
                        let tubeTr : M → Bundle.Trivialization (ComplexModel d) (Bundle.TotalSpace.proj (E := TangentSpace (realModel d))) := fun (p : M) =>
                          trivializationAt (ComplexModel d) (TangentSpace (realModel d))
                            (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor;
                        let tubeProjectedCoordinate :
                          (p : M) →
                            (Subtype fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                Membership.mem (tubeLabels p) x) →
                              ComplexModel d → ComplexModel d :=
                          fun (p : M)
                            (q :
                              Subtype fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                Membership.mem (tubeLabels p) x)
                            (w : ComplexModel d) =>
                          (coherentU.coherence (OfNat.ofNat 2) p).coordinate q.val ((tubeInverse p q).symm.toFun' w).1;
                        let tubeProjectionPair :
                          (p : M) →
                            (Subtype fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                Membership.mem (tubeLabels p) x) →
                              M → Prod M (ComplexModel d) :=
                          fun (p : M)
                            (q :
                              Subtype fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                Membership.mem (tubeLabels p) x)
                            (x : M) =>
                          Prod.mk
                            (((coherentU.family (OfNat.ofNat 2) p).family.plaque q.val).param
                              ((tubeInverse p q).symm.toFun' ((tubeChart p).toFun x)).1)
                            (tubeProjectedCoordinate p q ((tubeChart p).toFun x));
                        ∀ (complexDist : (x : M) → Submodule Complex (TangentSpace (complexModel d) x))
                          (complexBundle : ContinuousComplexTangentSubbundle (complexModel d) M),
                          Eq complexBundle.toDistribution complexDist →
                            (∀ (x : M),
                                Eq
                                  (Submodule.map (complexTangentToReal d x).toLinearMap
                                    (Submodule.restrictScalars Real (complexDist x)))
                                  (a.splitting.unstable.toDistribution x)) →
                              letI _complexTopology : TopologicalSpace
                                (Bundle.TotalSpace (ComplexModel 1) (fun x : M => ↥(complexBundle.toDistribution x))) :=
                                TopologicalSpace.induced (fun z => (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance;
                              ∀
                                (complexFrame :
                                  M → Bundle.Trivialization (ComplexModel 1) (Bundle.TotalSpace.proj (E := fun x : M => ↥(complexBundle.toDistribution x))))
                                (hComplexFrameLinear :
                                  ∀ (p : M), Bundle.Trivialization.IsLinear Complex (complexFrame p)),
                                (∀ (p : M) (ε : Real),
                                    LT.lt (OfNat.ofNat 0) ε →
                                      let _this : Bundle.Trivialization.IsLinear Complex (complexFrame p) :=
                                        hComplexFrameLinear p;
                                      let frame :
                                        Bundle.Trivialization (ComplexModel 1) (Bundle.TotalSpace.proj (E := fun x : M => ↥(complexBundle.toDistribution x))) :=
                                        complexFrame p;
                                      let tr : Bundle.Trivialization (ComplexModel d) (Bundle.TotalSpace.proj (E := TangentSpace (realModel d))) :=
                                        tubeTr p;
                                      let τ :
                                        (Subtype
                                            fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                            Membership.mem (tubeLabels p) x) →
                                          M → M :=
                                        fun
                                          (q :
                                            Subtype
                                              fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                              Membership.mem (tubeLabels p) x)
                                          (x : M) =>
                                        ((coherentU.family (OfNat.ofNat 2) p).family.plaque q.val).param
                                          ((tubeInverse p q).symm.toFun' ((tubeChart p).toFun x)).1;
                                      let V :
                                        (Subtype
                                            fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                            Membership.mem (tubeLabels p) x) →
                                          M → ContinuousLinearMap (RingHom.id Real) (ComplexModel d) (ComplexModel d) :=
                                        fun
                                          (q :
                                            Subtype
                                              fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                              Membership.mem (tubeLabels p) x)
                                          (x : M) =>
                                        fderiv Real
                                          (fun (w : ComplexModel d) =>
                                            (coherentU.coherence (OfNat.ofNat 2) p).coordinate q.val
                                              ((tubeInverse p q).symm.toFun' w).1)
                                          ((tubeChart p).toFun x);
                                      Exists fun (A : Set M) =>
                                        And (IsOpen A)
                                          (And (Membership.mem A p)
                                            (And
                                              (LE.le A
                                                (Inter.inter (tubeChart p).source
                                                  (preimage (tubeChart p).toFun (tubeImage p))))
                                              (∀
                                                (q :
                                                  Subtype
                                                    fun
                                                      (x :
                                                        (coherentU.family (OfNat.ofNat 2)
                                                                p).family.centerDomain.Elem) =>
                                                    Membership.mem (tubeLabels p) x),
                                                Membership.mem A q.val.val →
                                                  ∀ (x : M),
                                                    Membership.mem A x →
                                                      Exists fun (hxf : Membership.mem frame.baseSet x) =>
                                                        Exists fun (hyf : Membership.mem frame.baseSet (τ q x)) =>
                                                          Exists fun (hx : Membership.mem tr.baseSet x) =>
                                                            Exists fun (hy : Membership.mem tr.baseSet (τ q x)) =>
                                                              Exists
                                                                fun
                                                                  (C :
                                                                    ContinuousLinearMap (RingHom.id Real)
                                                                      (ComplexModel (OfNat.ofNat 1))
                                                                      (ComplexModel (OfNat.ofNat 1))) =>
                                                                And (LT.lt (OfNat.ofNat 0) C.det)
                                                                  (And
                                                                    (∀ (v : ComplexModel (OfNat.ofNat 1)),
                                                                      Eq
                                                                        (DFunLike.coe (complexTangentToReal d (τ q x))
                                                                          (DFunLike.coe
                                                                              (Bundle.Trivialization.linearEquivAt
                                                                                  Complex frame (τ q x) hyf).symm
                                                                              (DFunLike.coe C v)).val)
                                                                        (DFunLike.coe
                                                                          (Bundle.Trivialization.continuousLinearEquivAt
                                                                              Real tr (τ q x) hy).symm
                                                                          (DFunLike.coe (V q x)
                                                                            (DFunLike.coe
                                                                              (Bundle.Trivialization.continuousLinearEquivAt
                                                                                Real tr x hx)
                                                                              (DFunLike.coe (complexTangentToReal d x)
                                                                                (DFunLike.coe
                                                                                    (Bundle.Trivialization.linearEquivAt
                                                                                        Complex frame x hxf).symm
                                                                                    v).val)))))
                                                                    (∀
                                                                      (v :
                                                                        Subtype
                                                                          fun (x_1 : TangentSpace (realModel d) x) =>
                                                                          Membership.mem
                                                                            (a.splitting.unstable.toDistribution x)
                                                                            x_1),
                                                                      let av : TangentSpace (realModel d) (τ q x) :=
                                                                        DFunLike.coe
                                                                          (Bundle.Trivialization.continuousLinearEquivAt
                                                                              Real tr (τ q x) hy).symm
                                                                          (DFunLike.coe (V q x)
                                                                            (DFunLike.coe
                                                                              (Bundle.Trivialization.continuousLinearEquivAt
                                                                                Real tr x hx)
                                                                              v.val));
                                                                      And
                                                                        (LE.le
                                                                          (HMul.hMul (HSub.hSub (OfNat.ofNat 1) ε)
                                                                            (DFunLike.coe
                                                                                (DFunLike.coe (g.inner x) v.val)
                                                                                v.val).sqrt)
                                                                          (DFunLike.coe
                                                                              (DFunLike.coe (g.inner (τ q x)) av)
                                                                              av).sqrt)
                                                                        (LE.le
                                                                          (DFunLike.coe
                                                                              (DFunLike.coe (g.inner (τ q x)) av)
                                                                              av).sqrt
                                                                          (HMul.hMul (HAdd.hAdd (OfNat.ofNat 1) ε)
                                                                            (DFunLike.coe
                                                                                (DFunLike.coe (g.inner x) v.val)
                                                                                v.val).sqrt)))))))) →
                                  let _this_2 :
                                    ChartedSpace (Fin (HAdd.hAdd L.stableDimension (OfNat.ofNat 2)) → Real) M :=
                                    L.realAmbientCharts;
                                  ∀ (q : Quotient L.foliation.stablePartition)
                                    (x y : IntrinsicFoliationLeaf L.foliation.stablePartition q) (γ : Path x y)
                                    (h :
                                      OpenPartialHomeomorph (L.U (DFunLike.coe γ (OfNat.ofNat 0)).val)
                                        (L.U (DFunLike.coe γ (OfNat.ofNat 1)).val)),
                                    let _this_3 :
                                      TopologicalSpace (IntrinsicFoliationLeaf L.foliation.stablePartition q) :=
                                      L.foliation.stableTopology q;
                                    let _this_4 :
                                      TopologicalSpace
                                        (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                          (DFunLike.coe γ (OfNat.ofNat 0)).val) :=
                                      nativeTopology (DFunLike.coe γ (OfNat.ofNat 0)).val;
                                    let _this_5 :
                                      TopologicalSpace
                                        (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                          (DFunLike.coe γ (OfNat.ofNat 1)).val) :=
                                      nativeTopology (DFunLike.coe γ (OfNat.ofNat 1)).val;
                                    let _this_6 :
                                      ChartedSpace (Fin (L.unstable (DFunLike.coe γ (OfNat.ofNat 0)).val).rank → Real)
                                        (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                          (DFunLike.coe γ (OfNat.ofNat 0)).val) :=
                                      nativeCharts (DFunLike.coe γ (OfNat.ofNat 0)).val;
                                    let _this_7 : T2Space (L.U (DFunLike.coe γ (OfNat.ofNat 0)).val) :=
                                      (L.unstable (DFunLike.coe γ (OfNat.ofNat 0)).val).hausdorff;
                                    let _this_8 : LocallyCompactSpace (L.U (DFunLike.coe γ (OfNat.ofNat 0)).val) :=
                                      ChartedSpace.locallyCompactSpace
                                        (Fin (L.unstable (DFunLike.coe γ (OfNat.ofNat 0)).val).rank → Real)
                                        (L.U (DFunLike.coe γ (OfNat.ofNat 0)).val);
                                    ∀ (sourceOpen : Set (L.U (DFunLike.coe γ (OfNat.ofNat 0)).val)),
                                      let W : Set (L.U (DFunLike.coe γ (OfNat.ofNat 0)).val) := closure sourceOpen;
                                      ∀ (_m : MetricSpace M),
                                        let _this : MetricSpace M := originalAmbientMetric;
                                        ∀
                                          (projection :
                                            (i : Nat) →
                                              W.Elem →
                                                L.U
                                                  (Nat.iterate (DFunLike.coe f) i
                                                    (DFunLike.coe γ (OfNat.ofNat 1)).val)),
                                          let selected :
                                            (k : Nat) →
                                              L.U (DFunLike.coe γ (OfNat.ofNat 0)).val →
                                                L.U
                                                  (Nat.iterate (DFunLike.coe f) k
                                                    (DFunLike.coe γ (OfNat.ofNat 1)).val) :=
                                            fun (k : Nat) (z : L.U (DFunLike.coe γ (OfNat.ofNat 0)).val) =>
                                            dite (Membership.mem W z)
                                              (fun (hz : Membership.mem W z) => projection k (Subtype.mk z hz))
                                              fun (_hz : Not (Membership.mem W z)) =>
                                              DFunLike.coe (nativeIterate k (DFunLike.coe γ (OfNat.ofNat 1)).val)
                                                (h.toFun' z);
                                          let expanded :
                                            (k : Nat) →
                                              L.U
                                                  (Nat.iterate (DFunLike.coe f) k
                                                    (DFunLike.coe γ (OfNat.ofNat 0)).val) →
                                                L.U
                                                  (Nat.iterate (DFunLike.coe f) k
                                                    (DFunLike.coe γ (OfNat.ofNat 1)).val) :=
                                            fun (k : Nat)
                                              (z :
                                                L.U
                                                  (Nat.iterate (DFunLike.coe f) k
                                                    (DFunLike.coe γ (OfNat.ofNat 0)).val)) =>
                                            selected k
                                              (DFunLike.coe
                                                (Diffeomorph.symm
                                                  (nativeIterate k (DFunLike.coe γ (OfNat.ofNat 0)).val))
                                                z);
                                          (∀ (C : M → Set M),
                                              (∀ (p : M), IsOpen (C p)) →
                                                (∀ (p : M), Membership.mem (C p) p) →
                                                  Filter.Eventually
                                                    (fun (k : Nat) =>
                                                      ∀
                                                        (z :
                                                          L.U
                                                            (Nat.iterate (DFunLike.coe f) k
                                                              (DFunLike.coe γ (OfNat.ofNat 0)).val)),
                                                        Membership.mem
                                                            (image
                                                              (DFunLike.coe
                                                                (nativeIterate k (DFunLike.coe γ (OfNat.ofNat 0)).val))
                                                              (interior W))
                                                            z →
                                                          Exists fun (p : M) =>
                                                            Exists
                                                              fun
                                                                (q_1 :
                                                                  Subtype
                                                                    fun
                                                                      (x :
                                                                        (coherentU.family (OfNat.ofNat 2)
                                                                                p).family.centerDomain.Elem) =>
                                                                    Membership.mem (tubeLabels p) x) =>
                                                              And (Membership.mem (C p) q_1.val.val)
                                                                (And (Membership.mem (C p) z.val)
                                                                  (And (Membership.mem (tubeChart p).source z.val)
                                                                    (And
                                                                      (Membership.mem (tubeInverse p q_1).target
                                                                        ((tubeChart p).toFun z.val))
                                                                      (And
                                                                        (ContMDiffAt
                                                                          (L.uModel
                                                                            (Nat.iterate (DFunLike.coe f) k
                                                                              (DFunLike.coe γ (OfNat.ofNat 0)).val))
                                                                          (L.uModel
                                                                            (Nat.iterate (DFunLike.coe f) k
                                                                              (DFunLike.coe γ (OfNat.ofNat 1)).val))
                                                                          (OfNat.ofNat 1) (expanded k) z)
                                                                        ((nhds z).EventuallyEq
                                                                          (fun
                                                                              (z :
                                                                                L.U
                                                                                  (Nat.iterate (DFunLike.coe f) k
                                                                                    (DFunLike.coe γ
                                                                                        (OfNat.ofNat 0)).val)) =>
                                                                            Prod.mk (expanded k z).val
                                                                              ((tubeChart p).toFun (expanded k z).val))
                                                                          fun
                                                                            (z :
                                                                              L.U
                                                                                (Nat.iterate (DFunLike.coe f) k
                                                                                  (DFunLike.coe γ
                                                                                      (OfNat.ofNat 0)).val)) =>
                                                                          tubeProjectionPair p q_1 z.val))))))
                                                    atTop) →
                                            let _tubePhysicalOperator :
                                              (p : M) →
                                                (Subtype
                                                    fun
                                                      (x :
                                                        (coherentU.family (OfNat.ofNat 2)
                                                                p).family.centerDomain.Elem) =>
                                                    Membership.mem (tubeLabels p) x) →
                                                  (x y : M) →
                                                    Membership.mem (tubeChart p).source x →
                                                      Membership.mem (tubeChart p).source y →
                                                        ContinuousLinearMap (RingHom.id Real)
                                                          (TangentSpace (realModel d) x)
                                                          (TangentSpace (realModel d) y) :=
                                              fun (p : M)
                                                (q :
                                                  Subtype
                                                    fun
                                                      (x :
                                                        (coherentU.family (OfNat.ofNat 2)
                                                                p).family.centerDomain.Elem) =>
                                                    Membership.mem (tubeLabels p) x)
                                                (x y : M) (hx : Membership.mem (tubeChart p).source x)
                                                (hy : Membership.mem (tubeChart p).source y) =>
                                              let tr : Bundle.Trivialization (ComplexModel d) (Bundle.TotalSpace.proj (E := TangentSpace (realModel d))) :=
                                                tubeTr p;
                                              have hxtr : Membership.mem tr.baseSet x :=
                                                id
                                                  (Eq.mp
                                                    (congrFun'
                                                      (congrArg Membership.mem
                                                        (extChartAt_source (realModel d)
                                                          (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor))
                                                      x)
                                                    hx);
                                              have hytr : Membership.mem tr.baseSet y :=
                                                id
                                                  (Eq.mp
                                                    (congrFun'
                                                      (congrArg Membership.mem
                                                        (extChartAt_source (realModel d)
                                                          (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor))
                                                      y)
                                                    hy);
                                              (Bundle.Trivialization.continuousLinearEquivAt Real tr y
                                                        hytr).symm.toContinuousLinearMap.comp
                                                ((fderiv Real (tubeProjectedCoordinate p q)
                                                      ((tubeChart p).toFun x)).comp
                                                  (Bundle.Trivialization.continuousLinearEquivAt Real tr x
                                                      hxtr).toContinuousLinearMap);
                                            let normIndex : Nat → Type u := fun (k : Nat) =>
                                              Prod
                                                (image
                                                    (DFunLike.coe
                                                      (nativeIterate k (DFunLike.coe γ (OfNat.ofNat 0)).val))
                                                    (interior W)).Elem
                                                (Fin
                                                    (L.unstable
                                                        (Nat.iterate (DFunLike.coe f) k
                                                          (DFunLike.coe γ (OfNat.ofNat 0)).val)).rank →
                                                  Real);
                                            let sourceNorm : (k : Nat) → normIndex k → Real :=
                                              fun (k : Nat) (q_1 : normIndex k) =>
                                              let _this :
                                                TopologicalSpace
                                                  (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                                    (Nat.iterate (DFunLike.coe f) k
                                                      (DFunLike.coe γ (OfNat.ofNat 0)).val)) :=
                                                nativeTopology
                                                  (Nat.iterate (DFunLike.coe f) k (DFunLike.coe γ (OfNat.ofNat 0)).val);
                                              let _this :
                                                ChartedSpace
                                                  (Fin
                                                      (L.unstable
                                                          (Nat.iterate (DFunLike.coe f) k
                                                            (DFunLike.coe γ (OfNat.ofNat 0)).val)).rank →
                                                    Real)
                                                  (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                                    (Nat.iterate (DFunLike.coe f) k
                                                      (DFunLike.coe γ (OfNat.ofNat 0)).val)) :=
                                                nativeCharts
                                                  (Nat.iterate (DFunLike.coe f) k (DFunLike.coe γ (OfNat.ofNat 0)).val);
                                              leafPullbackHermitianNorm Subtype.val hmetric q_1.1.val q_1.2;
                                            let targetNorm : (k : Nat) → normIndex k → Real :=
                                              fun (k : Nat) (q_1 : normIndex k) =>
                                              let _this :
                                                TopologicalSpace
                                                  (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                                    (Nat.iterate (DFunLike.coe f) k
                                                      (DFunLike.coe γ (OfNat.ofNat 0)).val)) :=
                                                nativeTopology
                                                  (Nat.iterate (DFunLike.coe f) k (DFunLike.coe γ (OfNat.ofNat 0)).val);
                                              let _this :
                                                ChartedSpace
                                                  (Fin
                                                      (L.unstable
                                                          (Nat.iterate (DFunLike.coe f) k
                                                            (DFunLike.coe γ (OfNat.ofNat 0)).val)).rank →
                                                    Real)
                                                  (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                                    (Nat.iterate (DFunLike.coe f) k
                                                      (DFunLike.coe γ (OfNat.ofNat 0)).val)) :=
                                                nativeCharts
                                                  (Nat.iterate (DFunLike.coe f) k (DFunLike.coe γ (OfNat.ofNat 0)).val);
                                              let _this :
                                                TopologicalSpace
                                                  (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                                    (Nat.iterate (DFunLike.coe f) k
                                                      (DFunLike.coe γ (OfNat.ofNat 1)).val)) :=
                                                nativeTopology
                                                  (Nat.iterate (DFunLike.coe f) k (DFunLike.coe γ (OfNat.ofNat 1)).val);
                                              let _this :
                                                ChartedSpace
                                                  (Fin
                                                      (L.unstable
                                                          (Nat.iterate (DFunLike.coe f) k
                                                            (DFunLike.coe γ (OfNat.ofNat 1)).val)).rank →
                                                    Real)
                                                  (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f)
                                                    (Nat.iterate (DFunLike.coe f) k
                                                      (DFunLike.coe γ (OfNat.ofNat 1)).val)) :=
                                                nativeCharts
                                                  (Nat.iterate (DFunLike.coe f) k (DFunLike.coe γ (OfNat.ofNat 1)).val);
                                              leafPullbackHermitianNorm Subtype.val hmetric (expanded k q_1.1.val)
                                                (DFunLike.coe
                                                  (mfderiv
                                                    (L.uModel
                                                      (Nat.iterate (DFunLike.coe f) k
                                                        (DFunLike.coe γ (OfNat.ofNat 0)).val))
                                                    (L.uModel
                                                      (Nat.iterate (DFunLike.coe f) k
                                                        (DFunLike.coe γ (OfNat.ofNat 1)).val))
                                                    (expanded k) q_1.1.val)
                                                  q_1.2);
∀ (ε : ℝ) (_hε : 0 < ε), ∀ᶠ k : ℕ in atTop,
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
              (chartAt (ComplexModel 1) z).symm) (chartAt (ComplexModel 1) z z)).toLinearMap  := by
  intro this hM realManifold originalAmbientMetric g a hb ιs Ls rs ts cs ss Fs invS ιu Lu ru tu cu su Fu invU coherentU nativeNorm nativeSpace nativeFinite L nativeTopology nativeCharts nativeIterate tubeDomain tubeLabels tubeImage tubeInverse hTubeInverse tubeChart tubeTr tubeProjectedCoordinate tubeProjectionPair complexDist complexBundle hComplexBundle hComplexReal complexFrame hComplexFrameLinear hNativeControl this q x y γ h this this this this this this sourceOpen W m this projection selected expanded hExpandedLocalFormula tubePhysicalOperator normIndex sourceNorm targetNorm ε hε
  choose C hControl using fun p ↦ hNativeControl p ε hε
  filter_upwards [hExpandedLocalFormula C (fun p ↦ (hControl p).1)
    (fun p ↦ (hControl p).2.1)] with k hk
  let xk := (f^[k]) (γ 0).val
  let yk := (f^[k]) (γ 1).val
  let := nativeTopology xk
  let := nativeCharts xk
  let := nativeTopology yk
  let := nativeCharts yk
  let : IsManifold (L.uModel xk) ∞ (L.U xk) := (L.unstable xk).smoothAtlas
  let : IsManifold (L.uModel yk) ∞ (L.U yk) := (L.unstable yk).smoothAtlas
  intro z hz
  have hzFormula := hk z hz
  refine hzFormula.elim (fun p hp ↦ hp.elim (fun q hq ↦ ?_))
  have hqC := hq.1
  have hzC := hq.2.1
  have hchart := hq.2.2.1
  have htarget := hq.2.2.2.1
  have hs := hq.2.2.2.2.1
  have hformula := hq.2.2.2.2.2
  let Φ := coherentU.family 2 p
  let H := coherentU.coherence 2 p
  let e := tubeInverse p q
  let ca := tubeChart p
  let Fraw := tubeProjectedCoordinate p q
  have hfoot : (expanded k z).val = (Φ.family.plaque q.val).param (e.symm (ca z.val)).1 :=
    congrArg (fun r : M × ComplexModel d ↦ r.1) hformula.self_of_nhds
  have hbase : (e.symm (ca z.val)).1 ∈ Metric.ball 0 Φ.family.radius :=
    ((hTubeInverse p q).2.2.2.2 _ (e.map_target htarget)).1.2
  have hout : (expanded k z).val ∈ ca.source := by
    rw [hfoot]
    exact Φ.family.receiving_domain q.val _ hbase
  have heDiff : DifferentiableAt ℝ e.symm (ca z.val) :=
    (((hTubeInverse p q).2.2.2.1).contDiffAt (e.open_target.mem_nhds htarget)).differentiableAt
      (by simp)
  have hqDiff : DifferentiableAt ℝ (H.coordinate q.val) (e.symm (ca z.val)).1 :=
    ((H.coordinate_smooth q.val).contDiffAt (Metric.isOpen_ball.mem_nhds hbase)).differentiableAt
      (by simp)
  have hF : HasFDerivAt Fraw (fderiv ℝ Fraw (ca z.val)) (ca z.val) :=
    (hqDiff.comp (ca z.val) heDiff.fst).hasFDerivAt
  have hcoord : (ca ∘ (Subtype.val : L.U yk → M) ∘ expanded k) =ᶠ[𝓝 z]
      (Fraw ∘ ca ∘ (Subtype.val : L.U xk → M)) := by
    filter_upwards [hformula] with w hw
    exact congrArg (fun r : M × ComplexModel d ↦ r.2) hw
  have hD := intrinsic_coordinate_derivative_g18 (X := L.U xk) (Y := L.U yk)
    (M := M) (E := ComplexModel d) (L.uModel xk) (L.uModel yk)
    Φ.family.receivingAnchor (Subtype.val : L.U xk → M) (Subtype.val : L.U yk → M)
    (expanded k) z ((L.unstable xk).inclusion_smooth.mdifferentiableAt (by simp))
    ((L.unstable yk).inclusion_smooth.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp)) hchart hout Fraw (fderiv ℝ Fraw (ca z.val)) hF hcoord
  have hA (w : TangentSpace (L.uModel xk) z) :
      tubePhysicalOperator p q z.val (expanded k z).val hchart hout
        (mfderiv (L.uModel xk) (realModel d) (Subtype.val : L.U xk → M) z w) =
      mfderiv (L.uModel yk) (realModel d) (Subtype.val : L.U yk → M) (expanded k z)
        (mfderiv (L.uModel xk) (L.uModel yk) (expanded k) z w) :=
    (congrArg (fun D ↦ D w) hD).symm
  let tr := tubeTr p
  let A := tubePhysicalOperator p q z.val (expanded k z).val hchart hout
  let : TopologicalSpace (Bundle.TotalSpace (ComplexModel 1)
      (fun x : M ↦ ↥(complexBundle.toDistribution x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let := hComplexFrameLinear p
  refine ((hControl p).2.2.2 q hqC z.val hzC).elim (fun hxf hrest ↦
    hrest.elim (fun hyf hrest ↦ hrest.elim (fun hx hrest ↦
      hrest.elim (fun hy hrest ↦ hrest.elim (fun B hrest ↦ ?_)))))
  have hBpos := hrest.1
  have hB := hrest.2.1
  have hnorm := hrest.2.2
  have hztr : z.val ∈ tr.baseSet := hx
  have hwtr : (expanded k z).val ∈ tr.baseSet := hfoot.symm ▸ hy
  let Dinc : (Fin (L.unstable xk).rank → ℝ) →L[ℝ] ComplexModel d :=
    mfderiv (M := L.U xk) (M' := M) (L.uModel xk) (realModel d)
      (Subtype.val : L.U xk → M) z
  constructor
  · intro v
    have hbound : ∀ w ∈ Dinc.range,
        (1-ε)*Real.sqrt (g.inner z.val w w) ≤
            Real.sqrt (g.inner (expanded k z).val (A w) (A w)) ∧
          Real.sqrt (g.inner (expanded k z).val (A w) (A w)) ≤
            (1+ε)*Real.sqrt (g.inner z.val w w) := by
      intro w hw
      have hwDist : w ∈ a.splitting.unstable.toDistribution z.val := by
        rw [← (L.unstable xk).tangent_image z]
        exact hw
      let Pbound (y : M) : Prop := ∀ hy : y ∈ tr.baseSet,
        let aw := (tr.continuousLinearEquivAt ℝ y hy).symm
          ((fderiv ℝ Fraw (ca z.val)) ((tr.continuousLinearEquivAt ℝ z.val hztr) w))
        (1-ε)*Real.sqrt (g.inner z.val w w) ≤ Real.sqrt (g.inner y aw aw) ∧
          Real.sqrt (g.inner y aw aw) ≤ (1+ε)*Real.sqrt (g.inner z.val w w)
      have hbraw : Pbound ((Φ.family.plaque q.val).param (e.symm (ca z.val)).1) := by
        intro hy
        exact hnorm ⟨w,hwDist⟩
      have hbpoint : Pbound (expanded k z).val := Eq.mp (congrArg Pbound hfoot.symm) hbraw
      exact hbpoint hwtr
    exact intrinsic_nearisometry_of_physical_g18
      (X := L.U xk) (Y := L.U yk) (M := M)
      (rx := (L.unstable xk).rank) (ry := (L.unstable yk).rank) (d := d)
      (Subtype.val : L.U xk → M) (Subtype.val : L.U yk → M) (expanded k) z
      hmetric g.inner (StableFoliationsSupport.originalSmoothRealMetric_inner hmetric hmetric_smooth)
      A hA ε hbound v
  ·
    have hyf' : (expanded k z).val ∈ (complexFrame p).baseSet := hfoot.symm ▸ hyf
    have hB' : ∀ v,
        complexTangentToReal d (expanded k z).val
          ((((complexFrame p).linearEquivAt ℂ (expanded k z).val hyf').symm (B v)).val) =
        A (complexTangentToReal d z.val
          ((((complexFrame p).linearEquivAt ℂ z.val hxf).symm v).val)) := by
      let Psquare (y : M) : Prop := ∀ (hyf : y ∈ (complexFrame p).baseSet)
          (hy : y ∈ tr.baseSet), ∀ v,
        complexTangentToReal d y
          ((((complexFrame p).linearEquivAt ℂ y hyf).symm (B v)).val) =
        (tr.continuousLinearEquivAt ℝ y hy).symm
          ((fderiv ℝ Fraw (ca z.val)) ((tr.continuousLinearEquivAt ℝ z.val hztr)
            (complexTangentToReal d z.val
              ((((complexFrame p).linearEquivAt ℂ z.val hxf).symm v).val))))
      have hbraw : Psquare ((Φ.family.plaque q.val).param (e.symm (ca z.val)).1) := by
        intro hyf hy v
        exact hB v
      have hbpoint : Psquare (expanded k z).val := Eq.mp (congrArg Psquare hfoot.symm) hbraw
      exact hbpoint hyf' hwtr
    have hXS : ((complexBundle.toDistribution z.val).restrictScalars ℝ).map
        (complexTangentToReal d z.val).toLinearEquiv.toLinearMap =
        (mfderiv (L.uModel xk) (realModel d) (Subtype.val : L.U xk → M) z).range := by
      rw [hComplexBundle,hComplexReal]
      exact (L.unstable xk).tangent_image z |>.symm
    have hYS : ((complexBundle.toDistribution (expanded k z).val).restrictScalars ℝ).map
        (complexTangentToReal d (expanded k z).val).toLinearEquiv.toLinearMap =
        (mfderiv (L.uModel yk) (realModel d) (Subtype.val : L.U yk → M) (expanded k z)).range := by
      rw [hComplexBundle,hComplexReal]
      exact (L.unstable yk).tangent_image (expanded k z) |>.symm
    exact native_upgrade_orientation_from_original_g18
      (X := L.U xk) (Y := L.U yk) (M := M)
      (rx := (L.unstable xk).rank) (ry := (L.unstable yk).rank) (n := 1) (d := d)
      (Subtype.val : L.U xk → M) (Subtype.val : L.U yk → M)
      (L.complexUnstable xk) (L.complexUnstable yk) (expanded k) z
      (hs.mdifferentiableAt (by simp))
      ((L.unstable xk).inclusion_smooth.mdifferentiableAt (by simp))
      ((L.unstable yk).inclusion_smooth.mdifferentiableAt (by simp))
      (complexBundle.toDistribution z.val) (complexBundle.toDistribution (expanded k z).val)
      hXS hYS ((complexFrame p).linearEquivAt ℂ z.val hxf)
      ((complexFrame p).linearEquivAt ℂ (expanded k z).val hyf') A B hBpos hB' hA
end
end HolomorphicAnosov.Ghys
