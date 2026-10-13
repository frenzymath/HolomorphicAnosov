import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18
import HolomorphicAnosov.Geometry.HolomorphicCoordinateOrientationG18

open Manifold MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Bundle
namespace HolomorphicAnosov.Ghys
noncomputable section
open Set Filter _root_.Topology
universe u
attribute [local instance] complex_isManifold_real
/-- The native metric-normal projection has positive complex orientation and near-isometry
bounds on a neighborhood of the zero section. (Ghys, Prop. 2.2) -/
theorem NativeControlBlock {d : Nat} {M : Type u}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ChartedSpace (ComplexModel d) M] [inst_5 : IsManifold (complexModel d) (WithTop.some Top.top) M]
  (f : Biholomorph d d M M) (hmetric : HermitianTangentMetricCore d M)
  (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric) :
  let _this : MetricSpace M := rankComparisonMetric (d := d);
  Nonempty M →
    let _realManifold : IsManifold (realModel d) (WithTop.some Top.top) M := complex_isManifold_real d M;
    let _originalAmbientMetric : MetricSpace M := inferInstance;
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
                    let _nativeTopology :
                      (p : M) → TopologicalSpace (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f) p) :=
                      fun (p : M) => L.identification.unstableTopology p;
                    let _nativeCharts :
                      (p : M) →
                        ChartedSpace (Fin (L.unstable p).rank → Real)
                          (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f) p) :=
                      fun (p : M) => L.identification.unstableCharts p;
                    ∀ (tubeDomain : M → Set (Prod (ComplexModel d) (ComplexModel d)))
                      (tubeLabels : (p : M) → TopologicalSpace.Opens (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem)
                      (hTubeLabel :
                        ∀ (p : M),
                          Membership.mem (tubeLabels p)
                            (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem))
                      (tubeImage : M → Set (ComplexModel d)),
                      (∀ (p : M), IsOpen (tubeImage p)) →
                        ∀
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
                                                  fderiv Real ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1)
                                                    z.2)
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
                                                  fderiv Real ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1)
                                                    z.2)
                                                z)
                                              (plaqueNormalSpace
                                                  ((fun
                                                        (z :
                                                          Prod
                                                            (coherentU.family (OfNat.ofNat 2)
                                                                    p).family.centerDomain.Elem
                                                            (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                      originalMetricChartTensor_g18 g
                                                        (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                                        ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1 z.2))
                                                    (Prod.mk
                                                      (Subtype.mk p
                                                        (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                      (OfNat.ofNat 0)))
                                                  ((fun
                                                        (z :
                                                          Prod
                                                            (coherentU.family (OfNat.ofNat 2)
                                                                    p).family.centerDomain.Elem
                                                            (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                      fderiv Real
                                                        ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1) z.2)
                                                    (Prod.mk
                                                      (Subtype.mk p
                                                        (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                      (OfNat.ofNat 0)))).subtypeL)
                                          (Prod.mk p_1.val z.1))
                                        z.2)))
                                (And (Eq (tubeInverse p p_1).target (tubeImage p))
                                  (And
                                    (ContDiffOn Real (OfNat.ofNat 1) (tubeInverse p p_1).toFun'
                                      (tubeInverse p p_1).source)
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
                                                          Prod
                                                            (coherentU.family (OfNat.ofNat 2)
                                                                    p).family.centerDomain.Elem
                                                            (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                      originalMetricChartTensor_g18 g
                                                        (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                                        ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1 z.2))
                                                    (Prod.mk
                                                      (Subtype.mk p
                                                        (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                                      (OfNat.ofNat 0)))
                                                  ((fun
                                                        (z :
                                                          Prod
                                                            (coherentU.family (OfNat.ofNat 2)
                                                                    p).family.centerDomain.Elem
                                                            (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                      fderiv Real
                                                        ((coherentU.coherence (OfNat.ofNat 2) p).coordinate z.1) z.2)
                                                    (Prod.mk
                                                      (Subtype.mk p
                                                        (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
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
                                                          Prod
                                                            (coherentU.family (OfNat.ofNat 2)
                                                                    p).family.centerDomain.Elem
                                                            (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)) =>
                                                      plaqueNormalFrame
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
                                                          z)
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
                                                                  ((coherentU.coherence (OfNat.ofNat 2) p).coordinate
                                                                    z.1 z.2))
                                                              (Prod.mk
                                                                (Subtype.mk p
                                                                  (coherentU.family (OfNat.ofNat 2)
                                                                        p).family.center_mem)
                                                                (OfNat.ofNat 0)))
                                                            ((fun
                                                                  (z :
                                                                    Prod
                                                                      (coherentU.family (OfNat.ofNat 2)
                                                                              p).family.centerDomain.Elem
                                                                      (Fin (coherentU.dimension (OfNat.ofNat 2) p) →
                                                                        Real)) =>
                                                                fderiv Real
                                                                  ((coherentU.coherence (OfNat.ofNat 2) p).coordinate
                                                                    z.1)
                                                                  z.2)
                                                              (Prod.mk
                                                                (Subtype.mk p
                                                                  (coherentU.family (OfNat.ofNat 2)
                                                                        p).family.center_mem)
                                                                (OfNat.ofNat 0)))).subtypeL)
                                                    (Prod.mk p_1.val z.1))
                                                  z.2)))))))) →
                            (∀ (p : M),
                                ContinuousOn
                                  (fun
                                      (z :
                                        Prod
                                          (Subtype
                                            fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                            Membership.mem (tubeLabels p) x)
                                          (ComplexModel d)) =>
                                    (tubeInverse p z.1).symm.toFun' z.2)
                                  (SProd.sprod univ (tubeImage p))) →
                              (∀ (p : M),
                                  ContinuousOn
                                    (fun
                                        (z :
                                          Prod
                                            (Subtype
                                              fun (x : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                              Membership.mem (tubeLabels p) x)
                                            (ComplexModel d)) =>
                                      fderiv Real (tubeInverse p z.1).symm.toFun' z.2)
                                    (SProd.sprod univ (tubeImage p))) →
                                (∀ (p : M),
                                    Membership.mem
                                      (tubeInverse p
                                          (Subtype.mk
                                            (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem)
                                            (hTubeLabel p))).source
                                      (OfNat.ofNat 0)) →
                                  ∀
                                    (coefficientLabels :
                                      (p : M) → Set (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem),
                                    (∀ (p : M),
                                        Membership.mem
                                          (nhds (Subtype.mk p (coherentU.family (OfNat.ofNat 2) p).family.center_mem))
                                          (coefficientLabels p)) →
                                      ∀ (coefficientRadius : M → Real),
                                        (∀ (p : M), LT.lt (OfNat.ofNat 0) (coefficientRadius p)) →
                                          let tubeChart : M → PartialEquiv M (ComplexModel d) := fun (p : M) =>
                                            extChartAt (realModel d)
                                              (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor;
                                          let tubeTr :
                                            M → Bundle.Trivialization (ComplexModel d) (Bundle.TotalSpace.proj (E := TangentSpace (realModel d))) :=
                                            fun (p : M) =>
                                            trivializationAt (ComplexModel d) (TangentSpace (realModel d))
                                              (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor;
                                          let tubeTensor :
                                            (p : M) →
                                              (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem →
                                                (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real) →
                                                  ContinuousLinearMap (RingHom.id Real) (ComplexModel d)
                                                    (ContinuousLinearMap (RingHom.id Real) (ComplexModel d) Real) :=
                                            fun (p : M)
                                              (q : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem)
                                              (v : Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real) =>
                                            originalMetricChartTensor_g18 g
                                              (coherentU.family (OfNat.ofNat 2) p).family.receivingAnchor
                                              ((coherentU.coherence (OfNat.ofNat 2) p).coordinate q v);
                                          let tubeDerivative :
                                            (p : M) →
                                              (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem →
                                                (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real) →
                                                  ContinuousLinearMap (RingHom.id Real)
                                                    (Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real)
                                                    (ComplexModel d) :=
                                            fun (p : M)
                                              (q : (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem)
                                              (v : Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real) =>
                                            fderiv Real ((coherentU.coherence (OfNat.ofNat 2) p).coordinate q) v;
                                          (∀ (p : M)
                                              (q :
                                                Subtype
                                                  fun
                                                    (x :
                                                      (coherentU.family (OfNat.ofNat 2) p).family.centerDomain.Elem) =>
                                                  Membership.mem (tubeLabels p) x),
                                              Membership.mem (coefficientLabels p) q.val →
                                                ∀ (u : Fin (coherentU.dimension (OfNat.ofNat 2) p) → Real),
                                                  LT.lt (norm u) (coefficientRadius p) →
                                                    Membership.mem (tubeInverse p q).source
                                                        (Prod.mk u (OfNat.ofNat 0)) →
                                                      HasFDerivAt
                                                        (fun (w : ComplexModel d) =>
                                                          (coherentU.coherence (OfNat.ofNat 2) p).coordinate q.val
                                                            ((tubeInverse p q).symm.toFun' w).1)
                                                        (plaqueMetricProjection (tubeTensor p q.val u)
                                                          (tubeDerivative p q.val u))
                                                        ((coherentU.coherence (OfNat.ofNat 2) p).coordinate q.val u)) →
                                            (∀ (p : M), Membership.mem (tubeChart p).source p) →
                                              (∀ (p : M), Membership.mem (tubeImage p) ((tubeChart p).toFun p)) →
                                                let tubeGoodLabels :
                                                  (p : M) →
                                                    Set
                                                      (Subtype
                                                        fun
                                                          (x :
                                                            (coherentU.family (OfNat.ofNat 2)
                                                                    p).family.centerDomain.Elem) =>
                                                        Membership.mem (tubeLabels p) x) :=
                                                  fun (p : M) =>
                                                  ofPred
                                                    fun
                                                      (q :
                                                        Subtype
                                                          fun
                                                            (x :
                                                              (coherentU.family (OfNat.ofNat 2)
                                                                      p).family.centerDomain.Elem) =>
                                                          Membership.mem (tubeLabels p) x) =>
                                                    Membership.mem (tubeInverse p q).source (OfNat.ofNat 0);
                                                (∀ (p : M)
                                                    (q :
                                                      Subtype
                                                        fun
                                                          (x :
                                                            (coherentU.family (OfNat.ofNat 2)
                                                                    p).family.centerDomain.Elem) =>
                                                        Membership.mem (tubeLabels p) x),
                                                    Membership.mem (tubeGoodLabels p) q →
                                                      Eq ((tubeInverse p q).symm.toFun' ((tubeChart p).toFun q.val.val))
                                                        (OfNat.ofNat 0)) →
                                                  ∀
                                                    (complexDist :
                                                      (x : M) → Submodule Complex (TangentSpace (complexModel d) x))
                                                    (complexBundle :
                                                      ContinuousComplexTangentSubbundle (complexModel d) M),
                                                    Eq complexBundle.toDistribution complexDist →
                                                      (∀ (x : M),
                                                          Eq
                                                            (Submodule.map (complexTangentToReal d x).toLinearMap
                                                              (Submodule.restrictScalars Real (complexDist x)))
                                                            (a.splitting.unstable.toDistribution x)) →
                                                        letI _complexTopology : TopologicalSpace
                                                          (Bundle.TotalSpace (ComplexModel 1)
                                                            (fun x : M => ↥(complexBundle.toDistribution x))) :=
                                                          TopologicalSpace.induced
                                                            (fun z => (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance;
                                                        ∀
                                                          (complexFrame :
                                                            M →
                                                              Bundle.Trivialization (ComplexModel 1) (Bundle.TotalSpace.proj (E := fun x : M => ↥(complexBundle.toDistribution x)))),
                                                          (∀ (p : M), Membership.mem (complexFrame p).baseSet p) →
                                                            ∀
                                                              (hComplexFrameLinear :
                                                                ∀ (p : M),
                                                                  Bundle.Trivialization.IsLinear Complex
                                                                    (complexFrame p))
                                                              (p : M) (ε : Real),
                                                              LT.lt (OfNat.ofNat 0) ε →
                                                                let _this :
                                                                  Bundle.Trivialization.IsLinear Complex
                                                                    (complexFrame p) :=
                                                                  hComplexFrameLinear p;
                                                                let frame :
                                                                  Bundle.Trivialization (ComplexModel 1) (Bundle.TotalSpace.proj (E := fun x : M => ↥(complexBundle.toDistribution x))) :=
                                                                  complexFrame p;
                                                                let tr :
                                                                  Bundle.Trivialization (ComplexModel d) (Bundle.TotalSpace.proj (E := TangentSpace (realModel d))) :=
                                                                  tubeTr p;
                                                                let τ :
                                                                  (Subtype
                                                                      fun
                                                                        (x :
                                                                          (coherentU.family (OfNat.ofNat 2)
                                                                                  p).family.centerDomain.Elem) =>
                                                                      Membership.mem (tubeLabels p) x) →
                                                                    M → M :=
                                                                  fun
                                                                    (q :
                                                                      Subtype
                                                                        fun
                                                                          (x :
                                                                            (coherentU.family (OfNat.ofNat 2)
                                                                                    p).family.centerDomain.Elem) =>
                                                                        Membership.mem (tubeLabels p) x)
                                                                    (x : M) =>
                                                                  ((coherentU.family (OfNat.ofNat 2) p).family.plaque
                                                                        q.val).param
                                                                    ((tubeInverse p q).symm.toFun'
                                                                        ((tubeChart p).toFun x)).1;
                                                                let V :
                                                                  (Subtype
                                                                      fun
                                                                        (x :
                                                                          (coherentU.family (OfNat.ofNat 2)
                                                                                  p).family.centerDomain.Elem) =>
                                                                      Membership.mem (tubeLabels p) x) →
                                                                    M →
                                                                      ContinuousLinearMap (RingHom.id Real)
                                                                        (ComplexModel d) (ComplexModel d) :=
                                                                  fun
                                                                    (q :
                                                                      Subtype
                                                                        fun
                                                                          (x :
                                                                            (coherentU.family (OfNat.ofNat 2)
                                                                                    p).family.centerDomain.Elem) =>
                                                                        Membership.mem (tubeLabels p) x)
                                                                    (x : M) =>
                                                                  fderiv Real
                                                                    (fun (w : ComplexModel d) =>
                                                                      (coherentU.coherence (OfNat.ofNat 2) p).coordinate
                                                                        q.val ((tubeInverse p q).symm.toFun' w).1)
                                                                    ((tubeChart p).toFun x);
                                                                Exists fun (A : Set M) =>
                                                                  And (IsOpen A)
                                                                    (And (Membership.mem A p)
                                                                      (And
                                                                        (LE.le A
                                                                          (Inter.inter (tubeChart p).source
                                                                            (preimage (tubeChart p).toFun
                                                                              (tubeImage p))))
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
                                                                                Exists
                                                                                  fun
                                                                                    (hxf :
                                                                                      Membership.mem frame.baseSet x) =>
                                                                                  Exists
                                                                                    fun
                                                                                      (hyf :
                                                                                        Membership.mem frame.baseSet
                                                                                          (τ q x)) =>
                                                                                    Exists
                                                                                      fun
                                                                                        (hx :
                                                                                          Membership.mem tr.baseSet
                                                                                            x) =>
                                                                                      Exists
                                                                                        fun
                                                                                          (hy :
                                                                                            Membership.mem tr.baseSet
                                                                                              (τ q x)) =>
                                                                                        Exists
                                                                                          fun
                                                                                            (C :
                                                                                              ContinuousLinearMap
                                                                                                (RingHom.id Real)
                                                                                                (ComplexModel
                                                                                                  (OfNat.ofNat 1))
                                                                                                (ComplexModel
                                                                                                  (OfNat.ofNat 1))) =>
                                                                                          And
                                                                                            (LT.lt (OfNat.ofNat 0)
                                                                                              C.det)
                                                                                            (And
                                                                                              (∀
                                                                                                (v :
                                                                                                  ComplexModel
                                                                                                    (OfNat.ofNat 1)),
                                                                                                Eq
                                                                                                  (DFunLike.coe
                                                                                                    (complexTangentToReal
                                                                                                      d (τ q x))
                                                                                                    (DFunLike.coe
                                                                                                        (Bundle.Trivialization.linearEquivAt
                                                                                                            Complex
                                                                                                            frame
                                                                                                            (τ q x)
                                                                                                            hyf).symm
                                                                                                        (DFunLike.coe C
                                                                                                          v)).val)
                                                                                                  (DFunLike.coe
                                                                                                    (Bundle.Trivialization.continuousLinearEquivAt
                                                                                                        Real tr (τ q x)
                                                                                                        hy).symm
                                                                                                    (DFunLike.coe
                                                                                                      (V q x)
                                                                                                      (DFunLike.coe
                                                                                                        (Bundle.Trivialization.continuousLinearEquivAt
                                                                                                          Real tr x hx)
                                                                                                        (DFunLike.coe
                                                                                                          (complexTangentToReal
                                                                                                            d x)
                                                                                                          (DFunLike.coe
                                                                                                              (Bundle.Trivialization.linearEquivAt
                                                                                                                  Complex
                                                                                                                  frame
                                                                                                                  x
                                                                                                                  hxf).symm
                                                                                                              v).val)))))
                                                                                              (∀
                                                                                                (v :
                                                                                                  Subtype
                                                                                                    fun
                                                                                                      (x_1 :
                                                                                                        TangentSpace
                                                                                                          (realModel d)
                                                                                                          x) =>
                                                                                                    Membership.mem
                                                                                                      (a.splitting.unstable.toDistribution
                                                                                                        x)
                                                                                                      x_1),
                                                                                                let av :
                                                                                                  TangentSpace
                                                                                                    (realModel d)
                                                                                                    (τ q x) :=
                                                                                                  DFunLike.coe
                                                                                                    (Bundle.Trivialization.continuousLinearEquivAt
                                                                                                        Real tr (τ q x)
                                                                                                        hy).symm
                                                                                                    (DFunLike.coe
                                                                                                      (V q x)
                                                                                                      (DFunLike.coe
                                                                                                        (Bundle.Trivialization.continuousLinearEquivAt
                                                                                                          Real tr x hx)
                                                                                                        v.val));
                                                                                                And
                                                                                                  (LE.le
                                                                                                    (HMul.hMul
                                                                                                      (HSub.hSub
                                                                                                        (OfNat.ofNat 1)
                                                                                                        ε)
                                                                                                      (DFunLike.coe
                                                                                                          (DFunLike.coe
                                                                                                            (g.inner x)
                                                                                                            v.val)
                                                                                                          v.val).sqrt)
                                                                                                    (DFunLike.coe
                                                                                                        (DFunLike.coe
                                                                                                          (g.inner
                                                                                                            (τ q x))
                                                                                                          av)
                                                                                                        av).sqrt)
                                                                                                  (LE.le
                                                                                                    (DFunLike.coe
                                                                                                        (DFunLike.coe
                                                                                                          (g.inner
                                                                                                            (τ q x))
                                                                                                          av)
                                                                                                        av).sqrt
                                                                                                    (HMul.hMul
                                                                                                      (HAdd.hAdd
                                                                                                        (OfNat.ofNat 1)
                                                                                                        ε)
                                                                                                      (DFunLike.coe
                                                                                                          (DFunLike.coe
                                                                                                            (g.inner x)
                                                                                                            v.val)
                                                                                                          v.val).sqrt))))))) := by
  intro this hM realManifold originalAmbientMetric g a hb ιs Ls rs ts cs ss Fs invS ιu Lu ru tu cu su Fu invU coherentU nativeNorm nativeSpace nativeFinite L nativeTopology nativeCharts tubeDomain tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverse hTubeInverseContinuous hTubeDerivativeContinuous hTubeZeroSource coefficientLabels hCoefficientLabels coefficientRadius hCoefficientRadius tubeChart tubeTr tubeTensor tubeDerivative hTubeZeroProjectionDerivative hTubeChartSource hTubeImageCenter tubeGoodLabels hTubeInverseAtZero complexDist complexBundle hComplexBundle hComplexReal complexFrame hComplexFrameCenter hComplexFrameLinear p ε hε
  let : TopologicalSpace (Bundle.TotalSpace (ComplexModel 1)
      (fun x : M ↦ ↥(complexBundle.toDistribution x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let := hComplexFrameLinear p
  let q₀ : tubeLabels p := ⟨⟨p,(coherentU.family 2 p).family.center_mem⟩,hTubeLabel p⟩
  have hcoef : q₀.val ∈ coefficientLabels p := mem_of_mem_nhds (hCoefficientLabels p)
  have hzero : ‖(0 : Fin (coherentU.dimension 2 p) → ℝ)‖ < coefficientRadius p :=
    by simpa only [norm_zero] using hCoefficientRadius p
  have hder := hTubeZeroProjectionDerivative p q₀ hcoef 0 hzero (hTubeZeroSource p)
  have hcoord : (coherentU.coherence 2 p).coordinate q₀.val 0 = tubeChart p p :=
    ((coherentU.coherence 2 p).coordinate_eq q₀.val
      (Metric.mem_ball_self (coherentU.family 2 p).family.radius_pos)).trans
        (congrArg (tubeChart p) ((coherentU.family 2 p).family.plaque q₀.val).centered)
  exact HPS.native_physical_projection_open_control_g18 g
    complexBundle.toDistribution 1 (complexFrame p) (coherentU.coherence 2 p)
    (fun x ↦ by rw [hComplexBundle]; exact hComplexReal x)
    (tubeLabels p) (tubeImage p) (hTubeImage p) (tubeInverse p)
    (fun q ↦ (hTubeInverse p q).2.1) (fun q ↦ (hTubeInverse p q).2.2.2.1)
    (fun q z hz ↦ ((hTubeInverse p q).2.2.2.2 z hz).1.2)
    (hTubeInverseContinuous p) (hTubeDerivativeContinuous p)
    q₀ (hComplexFrameCenter p) (hTubeChartSource p) (hTubeImageCenter p)
    (hTubeInverseAtZero p q₀ (hTubeZeroSource p))
    (by simpa only [tubeTensor,tubeDerivative,hcoord] using hder) ε hε
end
end HolomorphicAnosov.Ghys
