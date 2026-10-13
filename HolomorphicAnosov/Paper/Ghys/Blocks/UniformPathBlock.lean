import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! Uniform shrinking of the diameters of finitely many path segments gives a uniform bound on the
distance from the initial point to every point of the path under forward iteration. -/

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
theorem UniformPathBlock :
  ∀ {d : ℕ} {M : Type u} [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : CompactSpace M] [inst_4 : ChartedSpace (ComplexModel d) M] [inst_5 : IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M) (hmetric : HermitianTangentMetricCore d M) (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric),
  let this_1 : MetricSpace M := rankComparisonMetric (d := d);
  Nonempty M →
  let originalAmbientMetric : MetricSpace M := inferInstance;
  let g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d) fun (x : M) => TangentSpace (realModel d) x := StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth;
  ∀ (a : AnosovDatum f),
  a.metric = g →
  Nonempty (TensorAnosovBounds f.toReal a.splitting (StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth)) →
  ∀ (ιs : Type u) (Ls : ιs → Type u) (rs : ιs → ℕ) (ts : (i : ιs) → TopologicalSpace (Ls i)) (cs : (i : ιs) → ChartedSpace (Fin (rs i) → ℝ) (Ls i)) (ss : ∀ (i : ιs), IsManifold 𝓘(ℝ, Fin (rs i) → ℝ) ∞ (Ls i)) (Fs : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls rs),
  (∃ (β : Type u) (d_1 : β → ℕ) (T : β → Type u) (topT : (b : β) → TopologicalSpace (T b)), Nonempty (HPS.LaminationBoxes Fs β d_1 T)) →
  Nonempty (HPS.LeafDynamicalInvariance Fs f.toReal) →
  ∀ (familiesS : HPS.SelectedFiniteC1NativePlaqueFamilies Fs) (coherentS : HPS.SelectedFiniteOrderNativePlaqueFamilies Fs),
  HPS.SourceBoundDistanceOutput Fs familiesS coherentS f.toReal edist →
  ∀ (ιu : Type u) (Lu : ιu → Type u) (ru : ιu → ℕ) (tu : (i : ιu) → TopologicalSpace (Lu i)) (cu : (i : ιu) → ChartedSpace (Fin (ru i) → ℝ) (Lu i)) (su : ∀ (i : ιu), IsManifold 𝓘(ℝ, Fin (ru i) → ℝ) ∞ (Lu i)) (Fu : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu ru),
  (∃ (β : Type u) (d_1 : β → ℕ) (T : β → Type u) (topT : (b : β) → TopologicalSpace (T b)), Nonempty (HPS.LaminationBoxes Fu β d_1 T)) →
  Nonempty (HPS.LeafDynamicalInvariance Fu f.toReal) →
  ∀ (familiesU : HPS.SelectedFiniteC1NativePlaqueFamilies Fu) (coherentU : HPS.SelectedFiniteOrderNativePlaqueFamilies Fu) (L : RankOneNativeLeaves f a.splitting) (labelU : M → ιu) (discU : (x : M) → TopologicalSpace.Opens (Fin (ru (labelU x)) → ℝ)) (mapU : (x : M) → ↥(discU x) → M) (stagesU : HPS.NativeSourcePlaqueStages (fun (i : ιu) => (Fu.leaf i).inclusion) labelU f.toReal.symm discU mapU) (AU : HPS.DistanceLeafIdentification Fu f.toReal.symm edist),
  AU.label = labelU →
  (∀ (p₀ : M), let Φ : HPS.FiniteC1NativePlaqueFamily Fu p₀ (familiesU.dimension p₀) := familiesU.family p₀; Nonempty (HPS.SelectedFamilyGermRestriction (L := Lu) labelU discU mapU stagesU.center (familiesU.dimension p₀) Φ.family.centerDomain (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesU.dimension p₀) → ℝ) Φ.family.radius) (Metric.isOpen_ball)) (fun (z : Φ.family.centerDomain.Elem × ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesU.dimension p₀) → ℝ) Φ.family.radius) (Metric.isOpen_ball))) => (Φ.family.plaque z.1).param z.2.val) (Subtype.mk (0) (Metric.mem_ball_self Φ.family.radius_pos))) ∧ ∀ (p : Φ.family.centerDomain.Elem), Φ.label p = labelU p.val) →
  (∀ (N : ℕ) (p₀ : M), let Φ : HPS.FiniteC1NativePlaqueFamily Fu p₀ (coherentU.dimension N p₀) := coherentU.family N p₀; Nonempty (HPS.SelectedFamilyGermRestriction (L := Lu) labelU discU mapU stagesU.center (coherentU.dimension N p₀) Φ.family.centerDomain (TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (coherentU.dimension N p₀) → ℝ) Φ.family.radius) (Metric.isOpen_ball)) (fun (z : Φ.family.centerDomain.Elem × ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (coherentU.dimension N p₀) → ℝ) Φ.family.radius) (Metric.isOpen_ball))) => (Φ.family.plaque z.1).param z.2.val) (Subtype.mk (0) (Metric.mem_ball_self Φ.family.radius_pos))) ∧ ∀ (p : Φ.family.centerDomain.Elem), Φ.label p = labelU p.val) →
  ∀ (tubeLabels : (p : M) → TopologicalSpace.Opens (coherentU.family (2) p).family.centerDomain.Elem),
  (∀ (p : M), Subtype.mk p (coherentU.family (2) p).family.center_mem ∈ tubeLabels p) →
  ∀ (tubeImage : M → Set (ComplexModel d)),
  (∀ (p : M), IsOpen (tubeImage p)) →
  ∀ (tubeInverse : (p : M) → ↥(tubeLabels p) → OpenPartialHomeomorph ((Fin (coherentU.dimension (2) p) → ℝ) × ↥(plaqueNormalSpace ((fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => originalMetricChartTensor_g18 g (coherentU.family (2) p).family.receivingAnchor ((coherentU.coherence (2) p).coordinate z.1 z.2)) (Subtype.mk p (coherentU.family (2) p).family.center_mem, 0)) ((fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => fderiv ℝ ((coherentU.coherence (2) p).coordinate z.1) z.2) (Subtype.mk p (coherentU.family (2) p).family.center_mem, 0)))) (ComplexModel d)),
  (∀ (p : M), ContinuousOn (fun (z : ↥(tubeLabels p) × ComplexModel d) => (tubeInverse p z.1).symm.toFun' z.2) (univ ×ˢ tubeImage p)) →
  ∀ (coefficientLabels : (p : M) → Set (coherentU.family (2) p).family.centerDomain.Elem),
  (∀ (p : M), coefficientLabels p ∈ 𝓝 (Subtype.mk p (coherentU.family (2) p).family.center_mem)) →
  ∀ (fixedTubeLabels : (p : M) → Set (coherentU.family (2) p).family.centerDomain.Elem),
  (∀ (p : M), fixedTubeLabels p ∈ 𝓝 (Subtype.mk p (coherentU.family (2) p).family.center_mem)) →
  let tubeChart : M →
  PartialEquiv M (ComplexModel d) := fun (p : M) => extChartAt (realModel d) (coherentU.family (2) p).family.receivingAnchor;
  let tubeTensor : (p : M) →
  (coherentU.family (2) p).family.centerDomain.Elem →
  (Fin (coherentU.dimension (2) p) → ℝ) →
  ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ := fun (p : M) (q : (coherentU.family (2) p).family.centerDomain.Elem) (v : Fin (coherentU.dimension (2) p) → ℝ) => originalMetricChartTensor_g18 g (coherentU.family (2) p).family.receivingAnchor ((coherentU.coherence (2) p).coordinate q v);
  let tubeDerivative : (p : M) →
  (coherentU.family (2) p).family.centerDomain.Elem →
  (Fin (coherentU.dimension (2) p) → ℝ) →
  (Fin (coherentU.dimension (2) p) → ℝ) →L[ℝ] ComplexModel d := fun (p : M) (q : (coherentU.family (2) p).family.centerDomain.Elem) (v : Fin (coherentU.dimension (2) p) → ℝ) => fderiv ℝ ((coherentU.coherence (2) p).coordinate q) v;
  let tubeNormalSpace : M →
  Submodule ℝ (ComplexModel d) := fun (p : M) => plaqueNormalSpace (tubeTensor p (Subtype.mk p (coherentU.family (2) p).family.center_mem) (0)) (tubeDerivative p (Subtype.mk p (coherentU.family (2) p).family.center_mem) (0));
  let tubeNormal : (p : M) →
  (coherentU.family (2) p).family.centerDomain.Elem →
  (Fin (coherentU.dimension (2) p) → ℝ) →
  ↥(tubeNormalSpace p) →L[ℝ] ComplexModel d := fun (p : M) (q : (coherentU.family (2) p).family.centerDomain.Elem) (v : Fin (coherentU.dimension (2) p) → ℝ) => plaqueNormalFrame (tubeTensor p q v) (tubeDerivative p q v) (tubeNormalSpace p).subtypeL;
  (∀ (p : M), have D : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ) → (Fin (coherentU.dimension (2) p) → ℝ) →L[ℝ] ComplexModel d := fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => fderiv ℝ ((coherentU.coherence (2) p).coordinate z.1) z.2; have b : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ) → ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ := fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => originalMetricChartTensor_g18 g (coherentU.family (2) p).family.receivingAnchor ((coherentU.coherence (2) p).coordinate z.1 z.2); let K : Submodule ℝ (ComplexModel d) := plaqueNormalSpace (b (Subtype.mk p (coherentU.family (2) p).family.center_mem, 0)) (D (Subtype.mk p (coherentU.family (2) p).family.center_mem, 0)); have N : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ) → ↥K →L[ℝ] ComplexModel d := fun (z : (coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) => plaqueNormalFrame (b z) (D z) K.subtypeL; have size : ((coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) × ↥K → ℝ := fun (z : ((coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) × ↥K) => √(DFunLike.coe (DFunLike.coe (b z.1) (DFunLike.coe (N z.1) z.2)) (DFunLike.coe (N z.1) z.2)); ContinuousAt size ((Subtype.mk p (coherentU.family (2) p).family.center_mem, 0), 0) ∧ size ((Subtype.mk p (coherentU.family (2) p).family.center_mem, 0), 0) = 0) →
  (∀ (p : M), (tubeChart p).toFun p ∈ tubeImage p) →
  let tubeNormalSize : (p : M) →
  ((coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) × ↥(tubeNormalSpace p) →
  ℝ := fun (p : M) (z : ((coherentU.family (2) p).family.centerDomain.Elem × (Fin (coherentU.dimension (2) p) → ℝ)) × ↥(tubeNormalSpace p)) => √(DFunLike.coe (DFunLike.coe (tubeTensor p z.1.1 z.1.2) (DFunLike.coe (tubeNormal p z.1.1 z.1.2) z.2)) (DFunLike.coe (tubeNormal p z.1.1 z.1.2) z.2));
  ∀ (speedCore : (p : M) → Set (coherentU.family (2) p).family.centerDomain.Elem),
  (∀ (p : M), speedCore p ∈ 𝓝 (Subtype.mk p (coherentU.family (2) p).family.center_mem)) →
  let speedCover : M →
  Set M := fun (p : M) => Subtype.val '' interior (speedCore p ∩ (fixedTubeLabels p ∩ coefficientLabels p));
  (∀ (p : M), IsOpen (speedCover p)) →
  (∀ (p : M), p ∈ speedCover p) →
  let this_2 : ChartedSpace (Fin (L.stableDimension + 2) → ℝ) M := L.realAmbientCharts;
  ∀ (b : M → L.foliation.boxIndex) (hboxPoint : ∀ (x : M), x ∈ (L.foliation.box (b x)).image),
  let c : M →
  FoliationCoordinateDisk L.stableDimension × FoliationCoordinateDisk (2) := fun (p : M) => DFunLike.coe (L.foliation.box (b p)).chart.symm (Subtype.mk p (hboxPoint p));
  (∀ (p : M), (DFunLike.coe (L.foliation.box (b p)).chart (c p)).val = p) →
  ∀ (R : M → ℝ),
  (∀ (p : M), 0 < R p) →
  (∀ (p : M), R p < (familiesS.family p).family.radius) →
  ∀ (T : M → TopologicalSpace.Opens (FoliationCoordinateDisk (2))) (hcenter : ∀ (p : M) (t : ↥(T p)), (DFunLike.coe (L.identification.F.box (b p)).chart ((c p).1, t.val)).val ∈ (familiesS.family p).family.centerDomain) (hproductBox : ∀ (p : M) (p_1 : ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesS.dimension p) → ℝ) (R p)) Metric.isOpen_ball) × ↥(T p)), (fun (p_2 : ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesS.dimension p) → ℝ) (R p)) Metric.isOpen_ball) × ↥(T p)) => ((familiesS.family p).family.plaque (Subtype.mk (DFunLike.coe (L.identification.F.box (b p)).chart ((c p).1, p_2.2.val)).val (hcenter p p_2.2))).param p_2.1.val) p_1 ∈ (L.identification.F.box (b p)).image),
  (∀ (p : M), IsOpenEmbedding fun (p_1 : ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesS.dimension p) → ℝ) (R p)) Metric.isOpen_ball) × ↥(T p)) => ((familiesS.family p).family.plaque (Subtype.mk (DFunLike.coe (L.identification.F.box (b p)).chart ((c p).1, p_1.2.val)).val (hcenter p p_1.2))).param p_1.1.val) →
  (∀ (p : M) (p_1 : ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesS.dimension p) → ℝ) (R p)) Metric.isOpen_ball) × ↥(T p)), (DFunLike.coe (L.identification.F.box (b p)).chart.symm (Subtype.mk ((fun (p_2 : ↥(TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesS.dimension p) → ℝ) (R p)) Metric.isOpen_ball) × ↥(T p)) => ((familiesS.family p).family.plaque (Subtype.mk (DFunLike.coe (L.identification.F.box (b p)).chart ((c p).1, p_2.2.val)).val (hcenter p p_2.2))).param p_2.1.val) p_1) (hproductBox p p_1))).2 = p_1.2.val) →
  let U : (p : M) →
  TopologicalSpace.Opens (Fin (familiesS.dimension p) → ℝ) := fun (p : M) => TopologicalSpace.Opens.mk (Metric.ball (0 : Fin (familiesS.dimension p) → ℝ) (R p)) Metric.isOpen_ball;
  let J : (p : M) →
  ↥(U p) × ↥(T p) →
  M := fun (p : M) (z : ↥(U p) × ↥(T p)) => ((familiesS.family p).family.plaque (Subtype.mk (DFunLike.coe (L.foliation.box (b p)).chart ((c p).1, z.2.val)).val (hcenter p z.2))).param z.1.val;
  ∀ (hJ : ∀ (p : M), IsOpenEmbedding (J p)),
  (∀ (p : M), p ∈ range (J p)) →
  ∀ (q : Quotient L.foliation.stablePartition) (x y : IntrinsicFoliationLeaf L.foliation.stablePartition q) (γ : Path x y) (e : PathHolonomyRepresentative L.foliation γ (0) (1)) (h : OpenPartialHomeomorph (L.U (DFunLike.coe γ (0)).val) (L.U (DFunLike.coe γ (1)).val)),
  let this_3 : TopologicalSpace (IntrinsicFoliationLeaf L.foliation.stablePartition q) := L.foliation.stableTopology q;
  let this_4 : TopologicalSpace (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f) (DFunLike.coe γ (0)).val) := L.identification.unstableTopology (DFunLike.coe γ (0)).val;
  let this_5 : TopologicalSpace (UnstableAsymptoticLeaf (Diffeomorph.toHomeomorph f) (DFunLike.coe γ (1)).val) := L.identification.unstableTopology (DFunLike.coe γ (1)).val;
  ∀ (hprefix : (r : unitInterval.Elem) → PathHolonomyRepresentative L.foliation γ (0) r) (W₀ : Set (L.foliation.ULeaf (DFunLike.coe γ (0)).val)),
  L.foliation.uPoint (DFunLike.coe γ (0)).val ∈ W₀ →
  (∀ (r : unitInterval.Elem), W₀ ⊆ (hprefix r).map.source) →
  ContinuousOn (fun (p : unitInterval.Elem × L.foliation.ULeaf (DFunLike.coe γ (0)).val) => ((hprefix p.1).map.toFun' p.2).val) (univ ×ˢ W₀) →
  (hprefix (0)).map.toFun' =ᶠ[𝓝 (L.foliation.uPoint (DFunLike.coe γ (0)).val)] id →
  ∀ (Vzero : Set (L.foliation.ULeaf (DFunLike.coe γ (0)).val)),
  let H₀ : unitInterval.Elem × W₀.Elem →
  M := fun (p : unitInterval.Elem × W₀.Elem) => ((hprefix p.1).map.toFun' p.2.val).val;
  Continuous H₀ →
  ∀ (n : ℕ) (t : Fin (n + 1) → unitInterval.Elem),
  t (0) = 0 →
  t (Fin.last n) = 1 →
  Monotone t →
  ∀ (assigned : Fin n → M) (Nfam : Set W₀.Elem),
  (∀ (j : Fin n), ∀ p ∈ Nfam, ∀ r ∈ Icc (t j.castSucc) (t j.succ), H₀ (r, p) ∈ range (J (assigned j))) →
  let N₀ : Set (L.foliation.ULeaf (DFunLike.coe γ (0)).val) := Subtype.val '' Nfam ∩ Vzero;
  N₀ ⊆ W₀ →
  ∀ (W : Set (L.U (DFunLike.coe γ (0)).val)),
  (∀ (r : unitInterval.Elem), ∀ z ∈ W, DFunLike.coe (L.unstableClass (DFunLike.coe γ (0)).val).symm z ∈ (hprefix r).map.source) →
  IsCompact W →
  let H : unitInterval.Elem × L.U (DFunLike.coe γ (0)).val →
  M := fun (p : unitInterval.Elem × L.U (DFunLike.coe γ (0)).val) => ((hprefix p.1).map.toFun' (DFunLike.coe (L.unstableClass (DFunLike.coe γ (0)).val).symm p.2)).val;
  ContinuousOn H (univ ×ˢ W) →
  ∀ (hSubpaths : ∀ (j : Fin n), ∀ z ∈ W, ∀ r ∈ Icc (t j.castSucc) (t j.succ), H (r, z) ∈ range (J (assigned j))),
  (∀ (r : unitInterval.Elem), ∀ z ∈ W, @Setoid.r _ L.foliation.stablePartition (DFunLike.coe (L.unstableClass (DFunLike.coe γ (0)).val).symm z).val (H (r, z))) →
  let I : Fin n →
  Set unitInterval.Elem := fun (j : Fin n) => Icc (t j.castSucc) (t j.succ);
  let Hseg : (j : Fin n) →
  (I j).Elem × W.Elem →
  M := fun (j : Fin n) (z : (I j).Elem × W.Elem) => H (z.1.val, z.2.val);
  (∀ (j : Fin n), Continuous (Hseg j)) →
  let eprod : (p : M) →
  ↥(U p) × ↥(T p) ≃ₜ (range (J p)).Elem := fun (p : M) => (IsOpenEmbedding.isEmbedding (hJ p)).toHomeomorph;
  let Q : (j : Fin n) →
  (I j).Elem × W.Elem →
  ↥(U (assigned j)) × ↥(T (assigned j)) := fun (j : Fin n) (z : (I j).Elem × W.Elem) => DFunLike.coe (eprod (assigned j)).symm (Subtype.mk (Hseg j z) (hSubpaths j z.2.val z.2.property z.1.val z.1.property));
  (∀ (j : Fin n), Continuous (Q j)) →
  (∀ (j : Fin n) (z : (I j).Elem × W.Elem), J (assigned j) (Q j z) = Hseg j z) →
  let Cseg : (j : Fin n) →
  (I j).Elem × W.Elem →
  (familiesS.family (assigned j)).family.centerDomain.Elem := fun (j : Fin n) (z : (I j).Elem × W.Elem) => Subtype.mk (DFunLike.coe (L.foliation.box (b (assigned j))).chart ((c (assigned j)).1, (Q j z).2.val)).val (hcenter (assigned j) (Q j z).2);
  (∀ (j : Fin n), Continuous (Cseg j)) →
  let Kseg : (j : Fin n) →
  Set (familiesS.family (assigned j)).family.centerDomain.Elem := fun (j : Fin n) => range (Cseg j);
  (∀ (j : Fin n), IsCompact (Kseg j)) →
  ∀ (hboxseg : ∀ (j : Fin n) (z : (I j).Elem × W.Elem), Hseg j z ∈ (L.foliation.box (b (assigned j))).image),
  (∀ (j : Fin n) (z : (I j).Elem × W.Elem), (DFunLike.coe (L.foliation.box (b (assigned j))).chart.symm (Subtype.mk (Hseg j z) (hboxseg j z))).2 = (Q j z).2.val) →
  (∀ (j : Fin n) (z : W.Elem) (r r' : (I j).Elem), Cseg j (r, z) = Cseg j (r', z)) →
  let this_6 : Bundle.RiemannianBundle fun (p : M) => TangentSpace (realModel d) p := Bundle.RiemannianBundle.mk a.metric.toRiemannianMetric;
  ∀ (m : MetricSpace M),
  (∀ (x y : M), riemannianEDist (realModel d) x y < ⊤ → ENNReal.ofReal (m.dist x y) = riemannianEDist (realModel d) x y) →
  let this : MetricSpace M := originalAmbientMetric;
  (∀ (j : Fin n) (ε : ℝ), 0 < ε → ∀ᶠ (k : ℕ) in atTop, ∀ (z : (I j).Elem × W.Elem), m.dist ((DFunLike.coe f)^[k] (Hseg j z)) ((DFunLike.coe f)^[k] (Cseg j z).val) < ε) →
  (∀ (j : Fin n) (ε : ℝ), 0 < ε → ∀ᶠ (k : ℕ) in atTop, ∀ (z : W.Elem) (r r' : (I j).Elem), m.dist ((DFunLike.coe f)^[k] (Hseg j (r, z))) ((DFunLike.coe f)^[k] (Hseg j (r', z))) < ε) →
  (∀ (r : unitInterval.Elem), ∃ (j : Fin n), r ∈ I j) →
  ∀ (ε : ℝ),
  0 < ε →
  ∀ᶠ (k : ℕ) in atTop,
  ∀ (z : W.Elem) (r : unitInterval.Elem),
  m.dist ((DFunLike.coe f)^[k] (H (0, z.val))) ((DFunLike.coe f)^[k] (H (r, z.val))) < ε := by
  intro d M inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 f hmetric hmetric_smooth this hM originalAmbientMetric g a hag hb ιs Ls rs ts cs ss Fs boxesS invS familiesS coherentS extraS ιu Lu ru tu cu su Fu boxesU invU familiesU coherentU L labelU discU mapU stagesU AU hAUlabel hfamilyU hcoherentU tubeLabels hTubeLabel tubeImage hTubeImage tubeInverse hTubeInverseContinuous coefficientLabels hCoefficientLabels fixedTubeLabels hFixedTubeLabels tubeChart tubeTensor tubeDerivative tubeNormalSpace tubeNormal hTubeNormalSizeContinuous hTubeImageCenter tubeNormalSize speedCore hSpeedCoreCenter speedCover hSpeedCoverOpen hSpeedCoverCenter this b hboxPoint c hc R hR hRF T hcenter hproductBox hproductOpen hproductCoord U J hJ hpJ q x y γ e h this this this hprefix W₀ hxW₀ hprefixSource hprefixContinuous hzero Vzero H₀ hH₀ n t ht0 ht1 ht assigned Nfam hsegments N₀ hN₀sub W hCommonSource hWcompact H hH hSubpaths hStable I Hseg hHseg eprod Q hQ hQval Cseg hCseg Kseg hKseg hboxseg hQcoord hCseg_const this m hm this hshrink hdiam hcoverTime ε hε
  let τ := ε / ((n : ℝ) + 1)
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hτ : 0 < τ := div_pos hε hden
  have hτε : ((n : ℝ) + 1) * τ = ε := by
    dsimp [τ]
    field_simp
  filter_upwards [Filter.eventually_all.mpr (fun j : Fin n ↦ hdiam j τ hτ)] with k hk
  intro z r
  have hchain (i : Fin (n+1)) :
      m.dist ((f^[k]) (H (0,z.val))) ((f^[k]) (H (t i,z.val))) ≤ (i.val : ℝ) * τ := by
    induction i using Fin.induction with
    | zero =>
      simp only [ht0,Fin.val_zero,Nat.cast_zero,zero_mul]
      exact (m.dist_self _).le
    | succ j ih =>
      have hjt := ht (Fin.castSucc_le_succ j)
      have hd := hk j z ⟨t j.castSucc,le_rfl,hjt⟩ ⟨t j.succ,hjt,le_rfl⟩
      change m.dist ((f^[k]) (H (t j.castSucc,z.val)))
        ((f^[k]) (H (t j.succ,z.val))) < τ at hd
      calc
        _ ≤ m.dist ((f^[k]) (H (0,z.val))) ((f^[k]) (H (t j.castSucc,z.val))) +
            m.dist ((f^[k]) (H (t j.castSucc,z.val))) ((f^[k]) (H (t j.succ,z.val))) :=
          m.dist_triangle _ _ _
        _ ≤ (j.val : ℝ) * τ + τ := add_le_add ih hd.le
        _ = (j.succ.val : ℝ) * τ := by
          simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
          ring
  obtain ⟨j,hr⟩ := hcoverTime r
  have hjt := ht (Fin.castSucc_le_succ j)
  have hd := hk j z ⟨t j.castSucc,le_rfl,hjt⟩ ⟨r,hr⟩
  change m.dist ((f^[k]) (H (t j.castSucc,z.val))) ((f^[k]) (H (r,z.val))) < τ at hd
  have hc := hchain j.castSucc
  have hh := m.dist_triangle ((f^[k]) (H (0,z.val)))
    ((f^[k]) (H (t j.castSucc,z.val))) ((f^[k]) (H (r,z.val)))
  have hj : (j.val : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
  have hmul := mul_le_mul_of_nonneg_right hj hτ.le
  simp only [Fin.val_castSucc] at hc
  nlinarith


end
end HolomorphicAnosov.Ghys
