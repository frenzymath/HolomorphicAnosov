import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ManifoldInverse
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import HolomorphicAnosov.Geometry.AmbientOpNormEventuallyLt
import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import Mathlib.Topology.Semicontinuity.Basic
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSmoothInverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Convex.PathConnected
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundleLocalRankG10
import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergySplitNormContinuityG10
import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergyUniformComparisonG10
import HolomorphicAnosov.Dynamics.Anosov.ExplicitMetricUniformComparisonG10
import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergyContinuousRestrictedNorm
import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergySplitNorm
import HolomorphicAnosov.Dynamics.Anosov.NativeFibreChartExpressionTransport
import HolomorphicAnosov.Dynamics.Anosov.NativeFibreIteratedJetTransport
import HolomorphicAnosov.Dynamics.Anosov.FiniteWeightedEnergy
import HolomorphicAnosov.Dynamics.Anosov.FiniteC1NativePlaqueFamily
import HolomorphicAnosov.Dynamics.Anosov.FiniteOrderNativePlaqueCoherence
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphConstruction
import HolomorphicAnosov.Paper.HPS.LocalStrongGraphs
import HolomorphicAnosov.Geometry.UniformExponentialLift
import HolomorphicAnosov.Dynamics.Anosov.SourceBoundTransportedPlaqueStages
import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataG8
import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataTensorToBundle
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Prod
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeInverseForward
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import HolomorphicAnosov.Dynamics.Anosov.VerticalJetTransport

/-! Shared HPS graph-coordinate estimates. These proved helpers originated in
G14's global-lamination development and are shared with G18's intrinsic
Euclidean completion, with one canonical declaration of each construction. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped ContDiff Manifold Bundle Uniformity
namespace HolomorphicAnosov.HPS

theorem lipschitz_of_gauge_bound
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (νV : V → ℝ) (νW : W → ℝ)
    (hV : ∀ v, νV v = ‖v‖) (hW : ∀ w, νW w = ‖w‖)
    (G : V → W) (η : NNReal)
    (h : ∀ v w, νW (G v - G w) ≤ (η : ℝ) * νV (v - w)) :
    LipschitzWith η G := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro v w
  simpa only [hV, hW] using h v w

theorem derivative_conjugate
    {V W E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : V ≃L[ℝ] E) (R : W ≃L[ℝ] E) (G : E → E)
    (T : E →L[ℝ] E) (D : V →L[ℝ] W)
    (hT : ∀ v, R (D v) = T (L v)) (hG : HasFDerivAt G T 0) :
    HasFDerivAt (fun v ↦ R.symm (G (L v))) D 0 := by
  have h := R.symm.hasFDerivAt.comp 0
    ((by simpa only [map_zero] using hG : HasFDerivAt G T (L 0)).comp 0
      L.hasFDerivAt)
  have hD : R.symm.toContinuousLinearMap.comp
      (T.comp L.toContinuousLinearMap) = D := by
    ext v
    apply R.injective
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using (hT v).symm
  simpa only [hD, Function.comp_def] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

-- Conversion from the native subbundle topology to the graph supplier's sigma carrier.
noncomputable abbrev subbundleSigmaTopology (P : ContinuousRealTangentSubbundle 𝓘(ℝ, E) M) :
    TopologicalSpace (Sigma fun p ↦ P.toDistribution p) :=
  TopologicalSpace.induced
    (fun z ↦ (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance

noncomputable def sigmaSubbundleHomeomorph
    (P : ContinuousRealTangentSubbundle 𝓘(ℝ, E) M) (r : ℕ) :
    letI := subbundleSigmaTopology P
    letI : TopologicalSpace
        (Bundle.TotalSpace (Fin r → ℝ) (fun p ↦ P.toDistribution p)) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
    (Sigma fun p ↦ P.toDistribution p) ≃ₜ
      Bundle.TotalSpace (Fin r → ℝ) (fun p ↦ P.toDistribution p) := by
  letI := subbundleSigmaTopology P
  letI : TopologicalSpace
      (Bundle.TotalSpace (Fin r → ℝ) (fun p ↦ P.toDistribution p)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
  exact {
    toFun := fun z ↦ ⟨z.1, z.2⟩
    invFun := fun z ↦ ⟨z.proj, z.snd⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_induced_rng.mpr continuous_induced_dom
    continuous_invFun := continuous_induced_rng.mpr continuous_induced_dom }

/-- Install a definite norm on a finite-dimensional real vector space while retaining
its original topology. Both norm topologies are the canonical finite-dimensional module
 topology, so the topology replacement is exact. -/
noncomputable abbrev finiteDimensionalRenorm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ν : V → ℝ) (hν : ∀ v, 0 ≤ ν v) (hzero : ∀ v, ν v = 0 ↔ v = 0)
    (hadd : ∀ v w, ν (v + w) ≤ ν v + ν w)
    (hsmul : ∀ (c : ℝ) v, ν (c • v) = ‖c‖ * ν v) : NormedAddCommGroup V := by
  let originalModule : Module ℝ V := inferInstance
  have : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  have hOld := eq_moduleTopology ℝ V
  letI : Norm V := ⟨ν⟩
  let core : NormedSpace.Core ℝ V := {
    norm_nonneg := hν
    norm_smul := hsmul
    norm_triangle := hadd
    norm_eq_zero_iff := hzero }
  have htop : (inferInstance : TopologicalSpace V) =
      (PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore).toUniformSpace.toTopologicalSpace := by
    let := NormedAddCommGroup.ofCore core
    let : Module ℝ V := originalModule
    let := NormedSpace.ofCore core
    have : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
    exact hOld.trans (eq_moduleTopology ℝ V).symm
  exact NormedAddCommGroup.ofCoreReplaceTopology core htop


noncomputable def adaptedSubbundleFiniteRankNormedAtlas
    (P : ContinuousRealTangentSubbundle 𝓘(ℝ, E) M)
    (ν : ∀ p, P.toDistribution p → ℝ)
    (hν : ∀ p v, 0 ≤ ν p v)
    (hzero : ∀ p v, ν p v = 0 ↔ v = 0)
    (hadd : ∀ p v w, ν p (v + w) ≤ ν p v + ν p w)
    (hsmul : ∀ p (c : ℝ) v, ν p (c • v) = ‖c‖ * ν p v)
    (hnorm : letI := subbundleSigmaTopology P
      Continuous (fun z : Sigma fun p ↦ P.toDistribution p ↦ ν z.1 z.2)) :
    letI groups (p : M) := finiteDimensionalRenorm (ν p) (hν p) (hzero p) (hadd p) (hsmul p)
    letI spaces (p : M) : @NormedSpace ℝ (P.toDistribution p) _
        (groups p).toSeminormedAddCommGroup :=
      @NormedSpace.mk ℝ (P.toDistribution p) _ (groups p).toSeminormedAddCommGroup
        inferInstance (fun c v ↦ (hsmul p c v).le)
    letI := subbundleSigmaTopology P
    @FiniteRankNormedAtlas M _ (fun p ↦ P.toDistribution p) groups spaces _ := by
  classical
  letI groups (p : M) := finiteDimensionalRenorm (ν p) (hν p) (hzero p) (hadd p) (hsmul p)
  letI spaces (p : M) : @NormedSpace ℝ (P.toDistribution p) _
      (groups p).toSeminormedAddCommGroup :=
    @NormedSpace.mk ℝ (P.toDistribution p) _ (groups p).toSeminormedAddCommGroup
      inferInstance (fun c v ↦ (hsmul p c v).le)
  letI := subbundleSigmaTopology P
  choose r e he hlin using P.locally_trivial
  letI (i : M) : TopologicalSpace
      (Bundle.TotalSpace (Fin (r i) → ℝ) (fun p ↦ P.toDistribution p)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
  letI (i : M) := hlin i
  let c (i : M) : FiniteRankBundleChart (r i)
      (fun z : Sigma fun p ↦ P.toDistribution p ↦ z.1) :=
    ((e i).compHomeomorph (sigmaSubbundleHomeomorph P (r i))).transFiberHomeomorph
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (r i))).symm.toHomeomorph
  let k (i p : M) (hp : p ∈ (c i).baseSet) :
      P.toDistribution p ≃L[ℝ] FiniteFiberModel (r i) :=
    ((e i).linearEquivAt ℝ p hp).toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (r i))).symm
  have hc (i p : M) (hp : p ∈ (c i).baseSet) (v : P.toDistribution p) :
      c i ⟨p, v⟩ = (p, k i p hp v) := by
    apply Prod.ext
    · exact (c i).coe_fst (by exact (c i).mem_source.mpr hp)
    · rfl
  refine {
    rank := r
    chart := c
    mem_baseSet := he
    rank_eq := ?_
    coordinates := k
    chart_apply := hc
    fibre_inducing := ?_
    continuous_norm := hnorm
    continuous_transition := ?_ }
  · intro i p hp
    have hi := (k i p hp).finrank_eq
    have hp' := (k p p (he p)).finrank_eq
    simpa only [FiniteFiberModel, finrank_euclideanSpace, Fintype.card_fin] using hp'.symm.trans hi
  · intro p
    have hcomp : IsInducing (fun v : P.toDistribution p ↦
        (⟨p, v.val⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
      (FiberBundle.totalSpaceMk_isInducing E (TangentSpace 𝓘(ℝ, E)) p).comp
        IsInducing.subtypeVal
    exact (IsInducing.induced
      (fun z : Sigma fun p ↦ P.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) M))).of_comp_iff.mp hcomp
  · intro i j
    apply continuous_clm_apply.mpr
    intro v
    have hin : Continuous (fun p : {p // p ∈ (c i).baseSet ∩ (c j).baseSet} ↦
        (p.val, v)) := continuous_subtype_val.prodMk continuous_const
    have hmid := (c i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous hin
      (fun p ↦ (c i).mem_target.mpr p.property.1)
    have hmid_eq (p : {p // p ∈ (c i).baseSet ∩ (c j).baseSet}) :
        (c i).toOpenPartialHomeomorph.symm (p.val, v) =
          (⟨p.val, (k i p.val p.property.1).symm v⟩ : Sigma fun p ↦ P.toDistribution p) := by
      apply ((c i).toOpenPartialHomeomorph.symm_apply_eq
        ((c i).mem_source.mpr p.property.1)
        ((c i).mem_target.mpr p.property.1)).mpr
      change (p.val, v) = c i ⟨p.val, (k i p.val p.property.1).symm v⟩
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (hc i p.val p.property.1 ((k i p.val p.property.1).symm v)).symm
    have hout : Continuous (fun p : {p // p ∈ (c i).baseSet ∩ (c j).baseSet} ↦
        c j ((c i).toOpenPartialHomeomorph.symm (p.val, v))) :=
      (c j).toOpenPartialHomeomorph.continuousOn.comp_continuous hmid (fun p ↦ by
        rw [hmid_eq]
        exact (c j).mem_source.mpr p.property.2)
    apply hout.snd.congr
    intro p
    rw [hmid_eq, hc]
    rfl


end HolomorphicAnosov.HPS

open Set _root_.Topology
set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov.HPS
variable {A : Type*} [TopologicalSpace A] {V W : A → Type*}
  [∀ p, NormedAddCommGroup (V p)] [∀ p, NormedSpace ℝ (V p)]
  [∀ p, NormedAddCommGroup (W p)] [∀ p, NormedSpace ℝ (W p)]
  [TopologicalSpace (Sigma V)] [TopologicalSpace (Sigma W)]

noncomputable abbrev productSigmaTopology : TopologicalSpace (Sigma fun p ↦ V p × W p) :=
  TopologicalSpace.induced
    (fun z ↦ ((⟨z.1, z.2.1⟩ : Sigma V), (⟨z.1, z.2.2⟩ : Sigma W))) inferInstance

noncomputable def productFiniteRankNormedAtlas
    (e : FiniteRankNormedAtlas (E := V)) (f : FiniteRankNormedAtlas (E := W)) :
    letI := productSigmaTopology (V := V) (W := W)
    FiniteRankNormedAtlas (E := fun p ↦ V p × W p) := by
  classical
  letI := productSigmaTopology (V := V) (W := W)
  let r (i : A) := e.rank i + f.rank i
  let U (i : A) := (e.chart i).baseSet ∩ (f.chart i).baseSet
  let a (i : A) : (FiniteFiberModel (e.rank i) × FiniteFiberModel (f.rank i)) ≃L[ℝ]
      FiniteFiberModel (r i) := ContinuousLinearEquiv.ofFinrankEq (by
        simp [FiniteFiberModel, r, Module.finrank_prod])
  let k (i p : A) (hp : p ∈ U i) : (V p × W p) ≃L[ℝ] FiniteFiberModel (r i) :=
    ((e.coordinates i p hp.1).prodCongr (f.coordinates i p hp.2)).trans (a i)
  let forward (i : A) (z : Sigma fun p ↦ V p × W p) : A × FiniteFiberModel (r i) :=
    (z.1, a i (((e.chart i) ⟨z.1, z.2.1⟩).2, ((f.chart i) ⟨z.1, z.2.2⟩).2))
  let backward (i : A) (z : A × FiniteFiberModel (r i)) : Sigma fun p ↦ V p × W p :=
    if hp : z.1 ∈ U i then ⟨z.1, (k i z.1 hp).symm z.2⟩ else ⟨z.1, 0⟩
  have hforward (i p : A) (hp : p ∈ U i) (v : V p × W p) :
      forward i ⟨p, v⟩ = (p, k i p hp v) := by
    dsimp [forward, k]
    rw [e.chart_apply i p hp.1, f.chart_apply i p hp.2]
  have hbackward (i : A) (z : A × FiniteFiberModel (r i)) (hz : z.1 ∈ U i) :
      backward i z = ⟨z.1, (k i z.1 hz).symm z.2⟩ := by simp only [backward, dite_eq_left hz]
  have hpair : Continuous (fun z : Sigma fun p ↦ V p × W p ↦
      ((⟨z.1, z.2.1⟩ : Sigma V), (⟨z.1, z.2.2⟩ : Sigma W))) :=
    continuous_induced_dom
  have hfirst : Continuous (fun z : Sigma fun p ↦ V p × W p ↦
      (⟨z.1, z.2.1⟩ : Sigma V)) := hpair.fst
  have hsecond : Continuous (fun z : Sigma fun p ↦ V p × W p ↦
      (⟨z.1, z.2.2⟩ : Sigma W)) := hpair.snd
  have hbase : Continuous (fun z : Sigma fun p ↦ V p × W p ↦ z.1) := by
    have hproj : Continuous (fun z : Sigma V ↦ z.1) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (((e.chart z.1).continuousAt ((e.chart z.1).mem_source.mpr
        (e.mem_baseSet z.1))).fst).congr_of_eventuallyEq (by
          filter_upwards [(e.chart z.1).open_source.mem_nhds
            ((e.chart z.1).mem_source.mpr (e.mem_baseSet z.1))] with w hw
          exact ((e.chart z.1).coe_fst hw).symm)
    exact hproj.comp hfirst
  let c (i : A) : FiniteRankBundleChart (r i) (fun z : Sigma fun p ↦ V p × W p ↦ z.1) := {
    toFun := forward i
    invFun := backward i
    source := {z | z.1 ∈ U i}
    target := U i ×ˢ Set.univ
    map_source' := fun z hz ↦ ⟨hz, mem_univ _⟩
    map_target' := fun z hz ↦ by rw [hbackward i z hz.1]; exact hz.1
    left_inv' := fun z hz ↦ by
      rw [hforward i z.1 hz z.2]
      rw [hbackward i (z.1, k i z.1 hz z.2) hz]
      simp
    right_inv' := fun z hz ↦ by
      rw [hbackward i z hz.1, hforward i z.1 hz.1]
      simp
    open_source := ((e.chart i).open_baseSet.inter (f.chart i).open_baseSet).preimage hbase
    open_target := ((e.chart i).open_baseSet.inter (f.chart i).open_baseSet).prod isOpen_univ
    continuousOn_toFun := by
      have he : ContinuousOn (fun z : Sigma fun p ↦ V p × W p ↦
          e.chart i ⟨z.1, z.2.1⟩) {z | z.1 ∈ U i} :=
        (e.chart i).toOpenPartialHomeomorph.continuousOn.comp hfirst.continuousOn
        (fun z hz ↦ (e.chart i).mem_source.mpr hz.1)
      have hf : ContinuousOn (fun z : Sigma fun p ↦ V p × W p ↦
          f.chart i ⟨z.1, z.2.2⟩) {z | z.1 ∈ U i} :=
        (f.chart i).toOpenPartialHomeomorph.continuousOn.comp hsecond.continuousOn
        (fun z hz ↦ (f.chart i).mem_source.mpr hz.2)
      exact hbase.continuousOn.prodMk ((a i).continuous.comp_continuousOn (he.snd.prodMk hf.snd))
    continuousOn_invFun := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      apply continuous_induced_rng.mpr
      have hleft (z : U i ×ˢ (Set.univ : Set (FiniteFiberModel (r i)))) :
          (⟨(backward i z).1, (backward i z).2.1⟩ : Sigma V) =
            (e.chart i).toOpenPartialHomeomorph.symm (z.val.1, ((a i).symm z.val.2).1) := by
        rw [hbackward i z z.property.1]
        symm
        apply ((e.chart i).toOpenPartialHomeomorph.symm_apply_eq
          ((e.chart i).mem_source.mpr z.property.1.1)
          ((e.chart i).mem_target.mpr z.property.1.1)).mpr
        change _ = e.chart i _
        rw [e.chart_apply i z.val.1 z.property.1.1]
        simp [k]
      have hright (z : U i ×ˢ (Set.univ : Set (FiniteFiberModel (r i)))) :
          (⟨(backward i z).1, (backward i z).2.2⟩ : Sigma W) =
            (f.chart i).toOpenPartialHomeomorph.symm (z.val.1, ((a i).symm z.val.2).2) := by
        rw [hbackward i z z.property.1]
        symm
        apply ((f.chart i).toOpenPartialHomeomorph.symm_apply_eq
          ((f.chart i).mem_source.mpr z.property.1.2)
          ((f.chart i).mem_target.mpr z.property.1.2)).mpr
        change _ = f.chart i _
        rw [f.chart_apply i z.val.1 z.property.1.2]
        simp [k]
      have he : Continuous (fun z : U i ×ˢ (Set.univ : Set (FiniteFiberModel (r i))) ↦
          (e.chart i).toOpenPartialHomeomorph.symm (z.val.1, ((a i).symm z.val.2).1)) :=
        (e.chart i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        (continuous_subtype_val.fst.prodMk
          (((a i).symm.continuous.comp continuous_subtype_val.snd).fst))
        (fun z ↦ (e.chart i).mem_target.mpr z.property.1.1)
      have hf : Continuous (fun z : U i ×ˢ (Set.univ : Set (FiniteFiberModel (r i))) ↦
          (f.chart i).toOpenPartialHomeomorph.symm (z.val.1, ((a i).symm z.val.2).2)) :=
        (f.chart i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        (continuous_subtype_val.fst.prodMk
          (((a i).symm.continuous.comp continuous_subtype_val.snd).snd))
        (fun z ↦ (f.chart i).mem_target.mpr z.property.1.2)
      exact (he.congr (fun z ↦ (hleft z).symm)).prodMk
        (hf.congr (fun z ↦ (hright z).symm))
    baseSet := U i
    open_baseSet := (e.chart i).open_baseSet.inter (f.chart i).open_baseSet
    source_eq := rfl
    target_eq := rfl
    proj_toFun := fun _ _ ↦ rfl }
  refine {
    rank := r
    chart := c
    mem_baseSet := fun i ↦ ⟨e.mem_baseSet i, f.mem_baseSet i⟩
    rank_eq := fun i p hp ↦ congrArg₂ (· + ·) (e.rank_eq i p hp.1) (f.rank_eq i p hp.2)
    coordinates := k
    chart_apply := hforward
    fibre_inducing := ?_
    continuous_norm := ?_
    continuous_transition := ?_ }
  · intro p
    exact (IsInducing.induced _).of_comp_iff.mp
      ((e.fibre_inducing p).prodMap (f.fibre_inducing p))
  · exact (e.continuous_norm.comp hfirst).max (f.continuous_norm.comp hsecond)
  · intro i j
    have he := (e.continuous_transition i j).comp
      (continuous_subtype_val.subtype_mk
        (fun p : {p // p ∈ U i ∩ U j} ↦ ⟨p.property.1.1, p.property.2.1⟩))
    have hf := (f.continuous_transition i j).comp
      (continuous_subtype_val.subtype_mk
        (fun p : {p // p ∈ U i ∩ U j} ↦ ⟨p.property.1.2, p.property.2.2⟩))
    have hout := ((continuous_const (y := (a j).toContinuousLinearMap)).clm_comp
      (he.prod_mapL ℝ hf)).clm_comp
        (continuous_const (y := (a i).symm.toContinuousLinearMap))
    apply hout.congr
    intro p
    ext v
    rfl

noncomputable def splitFiniteRankNormedAtlas
    (e : FiniteRankNormedAtlas (E := V)) (f : FiniteRankNormedAtlas (E := W)) :
    letI := productSigmaTopology (V := V) (W := W)
    SplitFiniteRankNormedAtlas (E₁ := V) (E₂ := W) :=
  letI := productSigmaTopology (V := V) (W := W)
  { first := e
    second := f
    total := productFiniteRankNormedAtlas e f
    split_inducing := IsInducing.induced _ }

end HolomorphicAnosov.HPS

namespace HolomorphicAnosov.HPS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [Bundle.RiemannianBundle (fun p : M ↦ TangentSpace 𝓘(ℝ, E) p)]
  {V : M → Type*} [∀ p, NormedAddCommGroup (V p)] [∀ p, NormedSpace ℝ (V p)]
  [TopologicalSpace (Sigma V)]

omit [Bundle.RiemannianBundle (fun p : M ↦ TangentSpace 𝓘(ℝ, E) p)] in
theorem nativeCoordinateCoefficient_continuous
    (av : FiniteRankNormedAtlas (E := V))
    (L : ∀ p, V p ≃L[ℝ] TangentSpace 𝓘(ℝ, E) p)
    (hL : Continuous (fun z : Sigma V ↦
      (⟨z.1, L z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hLi : Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦
      (⟨z.proj, (L z.proj).symm z.snd⟩ : Sigma V)))
    {B : Type*} [TopologicalSpace B] (q : B → M) (hq : Continuous q)
    (i s : M) (hi : ∀ b, q b ∈ (av.chart i).baseSet)
    (hs : ∀ b, q b ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).baseSet) :
    (Continuous (fun b ↦
      (((av.coordinates i (q b) (hi b)).symm.trans (L (q b))).trans
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).continuousLinearEquivAt
          ℝ (q b) (hs b))).toContinuousLinearMap)) ∧
    (Continuous (fun b ↦
      (((av.coordinates i (q b) (hi b)).symm.trans (L (q b))).trans
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).continuousLinearEquivAt
          ℝ (q b) (hs b))).symm.toContinuousLinearMap)) := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
  constructor
  · apply continuous_clm_apply.mpr
    intro x
    have hf := (atlas_frame_continuous av i).comp
      ((hq.subtype_mk hi).prodMk (continuous_const (y := x)))
    have ht := (e.continuousOn.comp_continuous (hL.comp hf)
      (fun b ↦ e.mem_source.mpr (hs b))).snd
    apply ht.congr
    intro b
    symm
    change (e.continuousLinearEquivAt ℝ (q b) (hs b))
      (L (q b) ((av.coordinates i (q b) (hi b)).symm x)) = _
    rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq _ (hs b)]
    exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e (hs b) _
  · apply continuous_clm_apply.mpr
    intro x
    have hf := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (hq.prodMk (continuous_const (y := x)))
      (fun b ↦ e.mem_target.mpr (hs b))
    have he : Continuous (fun b ↦
        (⟨q b, (e.continuousLinearEquivAt ℝ (q b) (hs b)).symm x⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
      apply hf.congr
      intro b
      exact e.symm_apply_eq_mk_continuousLinearEquivAt_symm (q b) (hs b) x
    have ht : Continuous (fun b ↦ ((av.chart i)
        (⟨q b, (L (q b)).symm
          ((e.continuousLinearEquivAt ℝ (q b) (hs b)).symm x)⟩ : Sigma V)).2) :=
      ((av.chart i).toOpenPartialHomeomorph.continuousOn.comp_continuous (hLi.comp he)
        (fun b ↦ (av.chart i).mem_source.mpr (hi b))).snd
    apply ht.congr
    intro b
    rw [av.chart_apply i (q b) (hi b)]
    rfl

theorem nativeJointFiberContDiff
    (av : FiniteRankNormedAtlas (E := V))
    (f : M → M) (hf : Continuous f)
    (L : ∀ p, V p ≃L[ℝ] TangentSpace 𝓘(ℝ, E) p)
    (hL : Continuous (fun z : Sigma V ↦
      (⟨z.1, L z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hLi : Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦
      (⟨z.proj, (L z.proj).symm z.snd⟩ : Sigma V)))
    (G : ∀ p, TangentSpace 𝓘(ℝ, E) p → TangentSpace 𝓘(ℝ, E) (f p))
    (hG : ExponentialLift.HasContinuousVerticalJets univ f ⊤ (fun p ↦ G p.1))
    (r : ℕ) :
    JointFiberContDiff av av f r (fun p v ↦ (L (f p)).symm (G p (L p v))) := by
  have hGr (p : M) : ContDiff ℝ r (G p) := by
    have hc := (hG.1 ⟨p, mem_univ p⟩).mono (by simp :
      (Set.univ : Set E) ⊆ (tangentSpaceCastModel 𝓘(ℝ, E) p).symm ⁻¹' univ)
    have hcE : ContDiff ℝ r (fun u : E ↦
        tangentSpaceCastModel 𝓘(ℝ, E) (f p)
          (G p ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm u))) :=
      (contDiffOn_univ.mp hc).of_le (by simp)
    have ht := (tangentSpaceCastModel 𝓘(ℝ, E) (f p)).symm.contDiff.comp
      (hcE.comp (tangentSpaceCastModel 𝓘(ℝ, E) p).contDiff)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using ht
  constructor
  · intro p
    exact (L (f p)).symm.contDiff.comp ((hGr p).comp (L p).contDiff)
  · intro i j m hm z hz
    let s := z.1
    let t := f z.1
    let es := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    let et := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
    let U : Set M := ((av.chart i).baseSet ∩ f ⁻¹' (av.chart j).baseSet) ∩
      (es.baseSet ∩ f ⁻¹' et.baseSet)
    have hUopen : IsOpen U :=
      ((av.chart i).open_baseSet.inter ((av.chart j).open_baseSet.preimage hf)).inter
        (es.open_baseSet.inter (et.open_baseSet.preimage hf))
    have hzU : z.1 ∈ U := ⟨hz.1,
      mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1,
      mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (f z.1)⟩
    let C (p : U) := ((av.coordinates i p p.property.1.1).symm.trans (L p)).trans
      (es.continuousLinearEquivAt ℝ p p.property.2.1)
    let D (p : U) := ((av.coordinates j (f p) p.property.1.2).symm.trans (L (f p))).trans
      (et.continuousLinearEquivAt ℝ (f p) p.property.2.2)
    have hC : Continuous (fun p : U ↦ (C p).toContinuousLinearMap) :=
      (nativeCoordinateCoefficient_continuous av L hL hLi Subtype.val continuous_subtype_val
        i s (fun p ↦ p.property.1.1) (fun p ↦ p.property.2.1)).1
    have hD : Continuous (fun p : U ↦ (D p).symm.toContinuousLinearMap) :=
      (nativeCoordinateCoefficient_continuous av L hL hLi (fun p : U ↦ f p)
        (hf.comp continuous_subtype_val) j t
        (fun p ↦ p.property.1.2) (fun p ↦ p.property.2.2)).2
    let g (p : U) := ExponentialLift.fibreExpression univ f (fun p ↦ G p.1)
      s t ⟨p, mem_univ p⟩
    have hg (p : U) : ContDiff ℝ r (g p) :=
      (et.continuousLinearMapAt ℝ (f p)).contDiff.comp
        ((hGr p).comp (es.symmL ℝ p).contDiff)
    have hjet : Continuous (fun w : U × E ↦ iteratedFDeriv ℝ m (g w.1) w.2) := by
      exact (hG.2 s t m le_top).comp_continuous
        (((continuous_subtype_val.comp continuous_fst).subtype_mk (fun _ ↦ mem_univ _)).prodMk
          continuous_snd)
        (fun w ↦ ⟨w.1.property.2.1, w.1.property.2.2, mem_univ _⟩)
    have htransport := VerticalJetTransport.continuousOn_jet_linear_transport univ r m hm
      g (fun p _ ↦ hg p) (fun p ↦ (C p).toContinuousLinearMap)
      (fun p ↦ (D p).symm.toContinuousLinearMap) hC.continuousOn hD.continuousOn
      hjet.continuousOn
    have htransportContinuous : Continuous (fun w : U × FiniteFiberModel (av.rank i) ↦
        iteratedFDeriv ℝ m (fun x ↦ (D w.1).symm (g w.1 (C w.1 x))) w.2) := by
      simpa only [univ_prod_univ, continuousOn_univ,
        ContinuousLinearEquiv.coe_coe] using htransport
    have hlocal : ContinuousOn
        (fun w : M × FiniteFiberModel (av.rank i) ↦ FibreJet m
          (fibreChartExpression av av f (fun p v ↦ (L (f p)).symm (G p (L p v)))
            i j w.1) w.2) (U ×ˢ univ) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hp : Continuous (fun w : (U ×ˢ (univ : Set (FiniteFiberModel (av.rank i)))) ↦
          ((⟨w.val.1, w.property.1⟩ : U), w.val.2)) :=
        ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun w ↦ w.property.1)).prodMk
          (continuous_snd.comp continuous_subtype_val)
      have hc := htransportContinuous.comp hp
      apply hc.congr
      intro w
      change iteratedFDeriv ℝ m _ w.val.2 = iteratedFDeriv ℝ m _ w.val.2
      congr 1
      exact (NativeFibreChartJetTransport.fibreChartExpression_eq_tangentExpression av f L G
        i j s t w.val.1 w.property.1.1.1 w.property.1.1.2
          w.property.1.2.1 w.property.1.2.2).symm
    exact (hlocal.continuousAt ((hUopen.prod isOpen_univ).mem_nhds
      ⟨hzU, mem_univ z.2⟩)).continuousWithinAt

end HolomorphicAnosov.HPS



/-! Shared atlas, graph, and exponential-coordinate lemmas for HPS global continuation. -/

set_option linter.style.haveILetI false
open scoped ContDiff Manifold _root_.Topology Bundle ENNReal
open TopologicalSpace Set

universe u
namespace HolomorphicAnosov.HPS

theorem exponential_uniform_small
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [EMetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : M) (v : TangentSpace 𝓘(ℝ, E) p),
      ExponentialLift.metricNorm g p v < δ →
        edist p (ExponentialLift.riemannianExp g p v) < ε := by
  let B : Opens (M × M) := ⟨{z | edist z.1 z.2 < ε},
    isOpen_lt (continuous_fst.edist continuous_snd) continuous_const⟩
  obtain ⟨δ, hδ, _, h⟩ := ExponentialLift.centered_radius g univ isCompact_univ
    id continuous_id B (fun p _ ↦ by simpa [B] using hε) 1 zero_lt_one
  exact ⟨δ, hδ, fun p v hv ↦ (h p (mem_univ p) v hv).2⟩

theorem exponential_edist_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [EMetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : ℕ → M) (v : ∀ n, TangentSpace 𝓘(ℝ, E) (p n))
    (hv : Tendsto (fun n ↦ ExponentialLift.metricNorm g (p n) (v n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ edist (p n) (ExponentialLift.riemannianExp g (p n) (v n)))
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := exponential_uniform_small g ε hε
  filter_upwards [hv.eventually (gt_mem_nhds hδ)] with n hn
  exact (hsmall (p n) (v n) hn).le


theorem exponential_trapped_orbit_asymptotic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [EMetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {Q : Type*} (base : Q → M) (vec : ∀ x, TangentSpace 𝓘(ℝ, E) (base x))
    (weight : Q → ℝ) (step : Q → Q) (f : M → M)
    (hbase : ∀ x, base (step x) = f (base x))
    (hexp : ∀ x, ExponentialLift.riemannianExp g (base (step x)) (vec (step x)) =
      f (ExponentialLift.riemannianExp g (base x) (vec x)))
    (c q : ℝ) (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ x, ExponentialLift.metricNorm g (base x) (vec x) ≤ c * weight x)
    (hstep : ∀ x, weight (step x) ≤ q * weight x) (x : Q) :
    Tendsto (fun n ↦ edist (f^[n] (base x))
      (f^[n] (ExponentialLift.riemannianExp g (base x) (vec x)))) atTop (𝓝 0) := by
  have hweights (n : ℕ) : weight (step^[n] x) ≤ q ^ n * weight x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hstep _).trans ((mul_le_mul_of_nonneg_left ih hq0).trans_eq (by ring))
  have hnorm : Tendsto (fun n ↦ ExponentialLift.metricNorm g
      (base (step^[n] x)) (vec (step^[n] x))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ Real.sqrt_nonneg _) (fun n ↦
      (hbound _).trans (mul_le_mul_of_nonneg_left (hweights n) hc.le))
    simpa using (tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (weight x)))
  have he := exponential_edist_tendsto_zero g (fun n ↦ base (step^[n] x))
    (fun n ↦ vec (step^[n] x)) hnorm
  have hb (n : ℕ) : base (step^[n] x) = f^[n] (base x) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', hbase, ih]
  have hx (n : ℕ) : ExponentialLift.riemannianExp g (base (step^[n] x)) (vec (step^[n] x)) =
      f^[n] (ExponentialLift.riemannianExp g (base x) (vec x)) := by
    exact (show Function.Semiconj
      (fun x ↦ ExponentialLift.riemannianExp g (base x) (vec x)) step f from hexp).iterate_right n x
  simpa only [hb, hx] using he


theorem exponential_trapped_orbit_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [EMetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {Q : Type*} (base : Q → M) (vec : ∀ x, TangentSpace 𝓘(ℝ, E) (base x))
    (weight : Q → ℝ) (step : Q → Q) (f : M → M)
    (hbase : ∀ x, base (step x) = f (base x))
    (hexp : ∀ x, ExponentialLift.riemannianExp g (base (step x)) (vec (step x)) =
      f (ExponentialLift.riemannianExp g (base x) (vec x)))
    (c q : ℝ) (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ x, ExponentialLift.metricNorm g (base x) (vec x) ≤ c * weight x)
    (hstep : ∀ x, weight (step x) ≤ q * weight x)
    (B : ℝ) (ε : ENNReal) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : Q, weight x ≤ B →
      edist (f^[n] (base x))
        (f^[n] (ExponentialLift.riemannianExp g (base x) (vec x))) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := exponential_uniform_small g ε hε
  have ht : Tendsto (fun n : ℕ ↦ c * (q ^ n * B)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const B))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn x hx ↦ ?_⟩
  have hweights (n : ℕ) : weight (step^[n] x) ≤ q ^ n * weight x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hstep _).trans ((mul_le_mul_of_nonneg_left ih hq0).trans_eq (by ring))
  have he := hsmall (base (step^[n] x)) (vec (step^[n] x))
    (((hbound _).trans (mul_le_mul_of_nonneg_left
      ((hweights n).trans (mul_le_mul_of_nonneg_left hx (pow_nonneg hq0 n))) hc.le)).trans_lt
        (hN n hn))
  have hb (n : ℕ) : base (step^[n] x) = f^[n] (base x) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', hbase, ih]
  have hx (n : ℕ) : ExponentialLift.riemannianExp g (base (step^[n] x)) (vec (step^[n] x)) =
      f^[n] (ExponentialLift.riemannianExp g (base x) (vec x)) := by
    exact (show Function.Semiconj
      (fun x ↦ ExponentialLift.riemannianExp g (base x) (vec x)) step f from hexp).iterate_right n x
  simpa only [hb, hx] using he


theorem atlas_projection_continuous
    {A : Type*} [TopologicalSpace A] {V : A → Type*}
    [∀ p, NormedAddCommGroup (V p)] [∀ p, NormedSpace ℝ (V p)]
    [TopologicalSpace (Sigma V)] (e : FiniteRankNormedAtlas (E := V)) :
    Continuous (fun z : Sigma V ↦ z.1) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let c := e.chart z.1
  have hz : z ∈ c.source := c.mem_source.mpr (e.mem_baseSet z.1)
  have hc := c.toOpenPartialHomeomorph.continuousAt hz
  apply hc.fst.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hz] with w hw
  exact (c.proj_toFun w hw).symm

theorem jointFiberContDiff_total_continuous
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {V : A → Type*} {W : B → Type*}
    [∀ p, NormedAddCommGroup (V p)] [∀ p, NormedSpace ℝ (V p)]
    [∀ p, NormedAddCommGroup (W p)] [∀ p, NormedSpace ℝ (W p)]
    [TopologicalSpace (Sigma V)] [TopologicalSpace (Sigma W)]
    (e : FiniteRankNormedAtlas (E := V)) (d : FiniteRankNormedAtlas (E := W))
    (b : A → B) (hb : Continuous b) (r : ℕ)
    (g : ∀ p, V p → W (b p)) (hg : JointFiberContDiff e d b r g) :
    Continuous (fun z : Sigma V ↦ (⟨b z.1, g z.1 z.2⟩ : Sigma W)) := by
  have hp := atlas_projection_continuous e
  apply continuous_iff_continuousAt.mpr
  intro z
  let i := z.1
  let j := b z.1
  have hz : z ∈ (e.chart i).source := (e.chart i).mem_source.mpr (e.mem_baseSet i)
  have he := (e.chart i).toOpenPartialHomeomorph.continuousAt hz
  have hbase : ContinuousAt (fun z : Sigma V ↦ b z.1) z := (hb.comp hp).continuousAt
  apply (d.chart j).continuousAt_of_comp_left hbase (d.mem_baseSet j)
  have h0 := hg.2 i j 0 (Nat.zero_le r)
  have hval : ContinuousOn (fun w : A × FiniteFiberModel (e.rank i) ↦
      fibreChartExpression e d b g i j w.1 w.2)
      (((e.chart i).baseSet ∩ b ⁻¹' (d.chart j).baseSet) ×ˢ univ) := by
    have hc := (continuous_eval_const (0 : Fin 0 → FiniteFiberModel (e.rank i))).comp_continuousOn h0
    simpa only [FibreJet, Function.comp_def, iteratedFDeriv_zero_apply] using hc
  have hvalAt := hval.continuousAt
    ((((e.chart i).open_baseSet.inter ((d.chart j).open_baseSet.preimage hb)).prod isOpen_univ).mem_nhds
      (show (z.1, (e.chart i z).2) ∈
        ((e.chart i).baseSet ∩ b ⁻¹' (d.chart j).baseSet) ×ˢ univ from
          ⟨⟨e.mem_baseSet i, d.mem_baseSet j⟩, mem_univ _⟩))
  have hsecond : ContinuousAt (fun w : Sigma V ↦
      fibreChartExpression e d b g i j w.1 (e.chart i w).2) z :=
    ContinuousAt.comp (f := fun w : Sigma V ↦ (w.1, (e.chart i w).2))
      hvalAt (hp.continuousAt.prodMk he.snd)
  apply (hbase.prodMk hsecond).congr_of_eventuallyEq
  have hrec := (hb.comp hp).continuousAt.preimage_mem_nhds
    ((d.chart j).open_baseSet.mem_nhds (d.mem_baseSet j))
  filter_upwards [(e.chart i).open_source.mem_nhds hz, hrec] with w hw hbw
  have heq : (e.chart i).toOpenPartialHomeomorph.symm (w.1, (e.chart i w).2) = w := by
    have hf := (e.chart i).proj_toFun w hw
    have hpair : (w.1, (e.chart i w).2) = e.chart i w := by
      apply Prod.ext
      · exact hf.symm
      · rfl
    rw [hpair]
    exact (e.chart i).toOpenPartialHomeomorph.left_inv hw
  change (d.chart j) ⟨b w.1, g w.1 w.2⟩ = (b w.1, _)
  apply Prod.ext
  · exact (d.chart j).proj_toFun _ ((d.chart j).mem_source.mpr hbw)
  · exact congrArg (fun a : Sigma V ↦ ((d.chart j) ⟨b a.1, g a.1 a.2⟩).2) heq.symm


theorem uniform_small_on_diagonal
    {M : Type*} [EMetricSpace M] [CompactSpace M]
    (B : Opens (M × M)) (hdiag : ∀ p, (p, p) ∈ B)
    (weight : B → ℝ) (hw : Continuous weight)
    (hzero : ∀ p, weight ⟨(p, p), hdiag p⟩ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ENNReal, 0 < ε ∧ ∀ p q, edist p q < ε →
      ∃ h : (p, q) ∈ B, weight ⟨(p, q), h⟩ < δ := by
  let V : Set (M × M) := Subtype.val '' {z : B | weight z < δ}
  have hVopen : IsOpen V := B.isOpen.isOpenMap_subtype_val _
    (isOpen_lt hw continuous_const)
  have hVdiag (p : M) : (p, p) ∈ V :=
    ⟨⟨(p, p), hdiag p⟩, by change weight ⟨(p, p), hdiag p⟩ < δ; rw [hzero]; exact hδ, rfl⟩
  have hVuniform : V ∈ 𝓤 M := by
    rw [compactSpace_uniformity, Filter.mem_iSup]
    exact fun p ↦ hVopen.mem_nhds (hVdiag p)
  obtain ⟨ε, hε, hεV⟩ := uniformity_basis_edist.mem_iff.mp hVuniform
  refine ⟨ε, hε, ?_⟩
  intro p q hpq
  obtain ⟨z, hz, heq⟩ := hεV (show (p, q) ∈ {z | edist z.1 z.2 < ε} from hpq)
  refine ⟨heq ▸ z.property, ?_⟩
  have hzEq : z = ⟨(p, q), heq ▸ z.property⟩ := Subtype.ext heq
  simpa only [← hzEq] using (show weight z < δ from hz)

theorem uniform_exponential_logarithm_small
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [EMetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (ν : ∀ p : M, TangentSpace 𝓘(ℝ, E) p → ℝ)
    (hν : Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦ ν z.proj z.snd))
    (hν0 : ∀ p, ν p 0 = 0) :
    ∃ (L : ∀ p : M, M → TangentSpace 𝓘(ℝ, E) p) (ρ : ℝ) (B : Opens (M × M)),
      0 < ρ ∧ (∀ p, (p, p) ∈ B ∧ L p p = 0) ∧
      (∀ p v, ExponentialLift.metricNorm g p v < ρ →
        (p, ExponentialLift.riemannianExp g p v) ∈ B ∧
          L p (ExponentialLift.riemannianExp g p v) = v) ∧
      (∀ p q, (p, q) ∈ B → ExponentialLift.metricNorm g p (L p q) < ρ ∧
        ExponentialLift.riemannianExp g p (L p q) = q) ∧
      (∀ p v, ExponentialLift.metricNorm g p v < ρ →
        (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ ExponentialLift.riemannianExpDomain g) ∧
      (∀ p, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun q ↦ tangentSpaceCastModel 𝓘(ℝ, E) p (L p q)) {q | (p, q) ∈ B}) ∧
      ∀ δ : ℝ, 0 < δ → ∃ ε : ENNReal, 0 < ε ∧
        ∀ p q, edist p q < ε → ν p (L p q) < δ ∧
          ExponentialLift.riemannianExp g p (L p q) = q := by
  obtain ⟨U, ρ, R, O, B, L, Φ, hU, hρ, hR, hRρ, hO, hOD,
    hΦ, hΦinv, hB, hExpLog, hLogExp, hdiag, hrest⟩ :=
    ExponentialLift.uniform_exponential_lift_on_compact_set g univ isCompact_univ
      id (⊤ : ℕ∞) (by simp) contMDiff_id (fun _ _ ↦ mem_univ _) 1
  refine ⟨L, ρ, B, hρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p ↦ ⟨(hdiag p (hU (mem_univ p))).2.1,
      (hdiag p (hU (mem_univ p))).2.2.1⟩
  · intro p v hv
    have hz : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O := by
      change (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ (O : Set _)
      rw [hO]
      exact ⟨hU (mem_univ p), hv⟩
    refine ⟨?_, hLogExp p v hz⟩
    change (p, ExponentialLift.riemannianExp g p v) ∈ (B : Set _)
    rw [hB]
    exact ⟨⟨p, v⟩, hz, rfl⟩
  · intro p q hpq
    have hz := (Φ.symm ⟨(p, q), hpq⟩).property
    change ((Φ.symm ⟨(p, q), hpq⟩ : O) : TangentBundle 𝓘(ℝ, E) M) ∈ (O : Set _) at hz
    rw [hO, hΦinv] at hz
    exact ⟨hz.2, hExpLog p q hpq⟩
  · intro p v hv
    apply hOD
    rw [hO]
    exact ⟨hU (mem_univ p), hv⟩
  · exact fun p ↦ ExponentialLift.inverse_fibre_contMDiffOn O B Φ L hΦinv p
  intro δ hδ
  let weight (z : B) := ν z.val.1 (L z.val.1 z.val.2)
  have hw : Continuous weight := by
    have hc := hν.comp (continuous_subtype_val.comp Φ.symm.continuous)
    apply hc.congr
    intro z
    change ν (Φ.symm z).val.proj (Φ.symm z).val.snd = _
    rw [hΦinv z]
  have hd (p : M) : (p, p) ∈ B := (hdiag p (hU (mem_univ p))).2.1
  have hw0 (p : M) : weight ⟨(p, p), hd p⟩ = 0 := by
    change ν p (L p p) = 0
    rw [(hdiag p (hU (mem_univ p))).2.2.1, hν0]
  obtain ⟨ε, hε, hsmall⟩ := uniform_small_on_diagonal B hd weight hw hw0 δ hδ
  refine ⟨ε, hε, ?_⟩
  intro p q hpq
  obtain ⟨hpqB, hwq⟩ := hsmall p q hpq
  exact ⟨hwq, hExpLog p q hpqB⟩


noncomputable def exponential_fibre_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (ρ : ℝ) (B : Opens (M × M)) (L : M → TangentSpace 𝓘(ℝ, E) p)
    (hforward : ∀ v, ExponentialLift.metricNorm g p v < ρ →
      (p, ExponentialLift.riemannianExp g p v) ∈ B ∧
        L (ExponentialLift.riemannianExp g p v) = v)
    (hbackward : ∀ q, (p, q) ∈ B → ExponentialLift.metricNorm g p (L q) < ρ ∧
      ExponentialLift.riemannianExp g p (L q) = q)
    (hdomain : ∀ v, ExponentialLift.metricNorm g p v < ρ →
      (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ ExponentialLift.riemannianExpDomain g)
    (hlog : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun q ↦ tangentSpaceCastModel 𝓘(ℝ, E) p (L q)) {q | (p, q) ∈ B}) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞ where
  toFun := fun w ↦ ExponentialLift.riemannianExp g p
    ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm w)
  invFun := fun q ↦ tangentSpaceCastModel 𝓘(ℝ, E) p (L q)
  source := {w | ExponentialLift.metricNorm g p
    ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm w) < ρ}
  target := {q | (p, q) ∈ B}
  map_source' := fun w hw ↦ (hforward _ hw).1
  map_target' := by
    intro q hq
    simpa only [mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply] using (hbackward q hq).1
  left_inv' := by
    intro w hw
    rw [(hforward _ hw).2, ContinuousLinearEquiv.apply_symm_apply]
  right_inv' := by
    intro q hq
    rw [ContinuousLinearEquiv.symm_apply_apply, (hbackward q hq).2]
  open_source := isOpen_lt
    ((ExponentialLift.continuous_metricNorm g).comp
      (ExponentialLift.fixed_fibre_contMDiff p).continuous) continuous_const
  open_target := B.isOpen.preimage (continuous_const.prodMk continuous_id)
  contMDiffOn_toFun := (riemannian_exponential_local_addition g).2.2.1.comp
    (ExponentialLift.fixed_fibre_contMDiff p).contMDiffOn (fun w hw ↦ hdomain _ hw)
  contMDiffOn_invFun := hlog


noncomputable def graphStraighteningDiffeomorph
    {V W E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (V × W) ≃L[ℝ] E) (g : V → W) (n : ℕ∞ω) (hg : ContDiff ℝ n g) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n where
  toFun := fun z ↦ e ((e.symm z).1, (e.symm z).2 - g (e.symm z).1)
  invFun := fun z ↦ e ((e.symm z).1, (e.symm z).2 + g (e.symm z).1)
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  contMDiff_toFun := (e.contDiff.comp
    (e.symm.contDiff.fst.prodMk (e.symm.contDiff.snd.sub (hg.comp e.symm.contDiff.fst)))).contMDiff
  contMDiff_invFun := (e.contDiff.comp
    (e.symm.contDiff.fst.prodMk (e.symm.contDiff.snd.add (hg.comp e.symm.contDiff.fst)))).contMDiff

theorem graph_param_immersion
    {V W E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (n : ℕ∞ω) [IsManifold 𝓘(ℝ, E) n M]
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M n)
    (e : (V × W) ≃L[ℝ] E) (g : V → W) (hg : ContDiff ℝ n g)
    (y : V) (hy : e (y, g y) ∈ φ.source) :
    Manifold.IsImmersionAt 𝓘(ℝ, V) 𝓘(ℝ, E) n (fun v ↦ φ (e (v, g v))) y := by
  let U : Set V := {v | e (v, g v) ∈ φ.source}
  have hU : IsOpen U := φ.open_source.preimage
    (e.continuous.comp (continuous_id.prodMk hg.continuous))
  let a := OpenPartialHomeomorph.ofSet U hU
  let s := graphStraighteningDiffeomorph e g n hg
  let b := (φ.symm.trans s.toPartialDiffeomorph).toOpenPartialHomeomorph
  apply Manifold.IsImmersionAt.mk_of_charts e a b
  · exact hy
  · exact ⟨φ.map_source hy, mem_univ _⟩
  · apply a.mem_maximalAtlas_of_contMDiffOn
    · exact contMDiffOn_id
    · exact contMDiffOn_id
  · apply b.mem_maximalAtlas_of_contMDiffOn
    · exact (φ.symm.trans s.toPartialDiffeomorph).contMDiffOn_toFun
    · exact (φ.symm.trans s.toPartialDiffeomorph).contMDiffOn_invFun
  · intro v hv
    exact ⟨φ.map_source hv, mem_univ _⟩
  · intro v hv
    change s (φ.symm (φ (e (v, g v)))) = e (v, 0)
    have hv' : e (v, g v) ∈ φ.source := by
      simpa only [a, U, OpenPartialHomeomorph.extend_target, mfld_simps] using hv
    have hφ : φ.symm.toPartialEquiv (φ.toPartialEquiv (e (v, g v))) = e (v, g v) :=
      φ.left_inv hv'
    rw [hφ]
    change e ((e.symm (e (v, g v))).1,
      (e.symm (e (v, g v))).2 - g (e.symm (e (v, g v))).1) = e (v, 0)
    simp


theorem exponential_fibreMap_mfderiv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [Bundle.RiemannianBundle (fun p : M ↦ TangentSpace 𝓘(ℝ, E) p)]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (ψ : V → TangentSpace 𝓘(ℝ, E) p) (hψ0 : ψ 0 = 0)
    (A : V →L[ℝ] E)
    (hψ : HasFDerivAt (fun v ↦ tangentSpaceCastModel 𝓘(ℝ, E) p (ψ v)) A 0)
    (v : V) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E)
      (fun v ↦ ExponentialLift.riemannianExp g p (ψ v)) 0 v = A v := by
  let F : V → E := fun v ↦ tangentSpaceCastModel 𝓘(ℝ, E) p (ψ v)
  let ep : E → M := fun w ↦ ExponentialLift.riemannianExp g p
    ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm w)
  have hF0 : F 0 = 0 := by simp only [F, hψ0, map_zero]
  have hep : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ep (F 0) := by
    rw [hF0]
    exact (riemannianExponential_fibre_contMDiffAt_zero g p).mdifferentiableAt (by simp)
  have hc := mfderiv_comp_apply (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    (f := F) (g := ep) 0 hep hψ.differentiableAt.mdifferentiableAt v
  rw [mfderiv_eq_fderiv, hψ.fderiv, hF0] at hc
  have hexp := (riemannian_exponential_local_addition g).2.2.2.2.1 p (A v)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 (A v) = A v at hexp
  exact hc.trans hexp

theorem mfderiv_range_le_of_local_factorization
    {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (f : V → M) (g : W → M) (k : V → W) (x : V)
    (hg : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, E) g (k x))
    (hk : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) k x)
    (heq : f =ᶠ[𝓝 x] g ∘ k) :
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x).range ≤
      (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) g (k x)).range := by
  rintro w ⟨v, rfl⟩
  refine ⟨mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) k x v, ?_⟩
  have hsame := congrArg
    (fun A : TangentSpace 𝓘(ℝ, V) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (f x) ↦ A v)
    (heq.mfderiv_eq (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)))
  change mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v =
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (g ∘ k) x v at hsame
  exact (hsame.trans (mfderiv_comp_apply x hg hk v)).symm


theorem local_factorization_open_chart
    {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (f : V → M) (g : W → M) (k : V → W) (x : V)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (hf : Manifold.IsImmersionAt 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f x)
    (hg : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, E) g (k x))
    (hk : ContDiffAt ℝ 1 k x) (heq : f =ᶠ[𝓝 x] g ∘ k) :
    ∃ e : OpenPartialHomeomorph V W, x ∈ e.source ∧ (e : V → W) = k := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hfactor (v : V) : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v =
      mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) g (k x) (fderiv ℝ k x v) := by
    have hsame := congrArg
      (fun A : TangentSpace 𝓘(ℝ, V) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (f x) ↦ A v)
      (heq.mfderiv_eq (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)))
    change mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v =
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (g ∘ k) x v at hsame
    have hcomp := mfderiv_comp_apply x hg
      (hk.differentiableAt (by simp)).mdifferentiableAt v
    rw [mfderiv_eq_fderiv] at hcomp
    exact hsame.trans hcomp
  have hinj : Function.Injective (fderiv ℝ k x) := by
    intro v w hvw
    apply hf.mfderiv_injective (by simp)
    exact (hfactor v).trans ((congrArg (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) g (k x)) hvw).trans
      (hfactor w).symm)
  let D : V ≃L[ℝ] W :=
    (LinearMap.linearEquivOfInjective (fderiv ℝ k x).toLinearMap hinj hdim).toContinuousLinearEquiv
  have hd : HasFDerivAt k D.toContinuousLinearMap x :=
    (hk.differentiableAt (by simp)).hasFDerivAt
  exact ⟨hk.toOpenPartialHomeomorph k hd (by simp),
    hk.mem_toOpenPartialHomeomorph_source hd (by simp), rfl⟩

theorem local_factorization_open_chart_restrict
    {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (f : V → M) (g : W → M) (k : V → W) (x : V)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (hf : Manifold.IsImmersionAt 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f x)
    (hg : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, E) g (k x))
    (hk : ContDiffAt ℝ 1 k x) (heq : f =ᶠ[𝓝 x] g ∘ k)
    (U : Set V) (hU : IsOpen U) (hxU : x ∈ U)
    (Z : Set W) (hZ : IsOpen Z) (hxZ : k x ∈ Z) :
    ∃ e : OpenPartialHomeomorph V W, x ∈ e.source ∧ (e : V → W) = k ∧
      e.source ⊆ U ∧ e.target ⊆ Z ∧ ∀ v ∈ e.source, f v = g (e v) := by
  obtain ⟨e, hx, he⟩ := local_factorization_open_chart f g k x hdim hf hg hk heq
  have hgood : {v | v ∈ U ∧ k v ∈ Z ∧ f v = g (k v)} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hxU, hk.continuousAt.preimage_mem_nhds (hZ.mem_nhds hxZ), heq]
      with v hv hvZ hvEq
    exact ⟨hv, hvZ, hvEq⟩
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hgood
  let e' := e.restrOpen O hO
  have he' : (e' : V → W) = k := he
  refine ⟨e', ⟨hx, hxO⟩, he', ?_, ?_, ?_⟩
  · intro v hv
    exact (hOsub hv.2).1
  · intro w hw
    have h := (hOsub (e'.map_target hw).2).2.1
    have hw' : k (e'.symm w) = w := by rw [← he']; exact e'.right_inv hw
    exact hw' ▸ h
  · intro v hv
    rw [he']
    exact (hOsub hv.2).2.2


theorem gauge_sublevel_convex
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ν : V → ℝ) (hadd : ∀ x y, ν (x + y) ≤ ν x + ν y)
    (hsmul : ∀ (a : ℝ) (x : V), ν (a • x) = ‖a‖ * ν x) (r : ℝ) : Convex ℝ {x | ν x < r} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    simpa only [hb1, zero_smul, one_smul, zero_add] using hy
  by_cases hb0 : b = 0
  · subst b
    have ha1 : a = 1 := by linarith
    simpa only [ha1, zero_smul, one_smul, add_zero] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have h := hadd (a • x) (b • y)
  rw [hsmul, hsmul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] at h
  exact h.trans_lt ((add_lt_add (mul_lt_mul_of_pos_left hx ha')
    (mul_lt_mul_of_pos_left hy hb')).trans_eq (by rw [← add_mul, hab, one_mul]))

theorem locallyConstant_comp_on_convex
    {V M A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace M] (r : M → A) (hr : IsLocallyConstant r)
    (U : Set V) (hU : Convex ℝ U) (F : U → M) (hF : Continuous F)
    (x y : U) : r (F x) = r (F y) := by
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU.isPreconnected
  exact (hr.comp_continuous hF).apply_eq_of_preconnectedSpace x y

theorem uniformly_asymptotic_locally_close
    {M V : Type*} [EMetricSpace M] [TopologicalSpace V]
    (f : M → M) (hf : Continuous f) (p : M) (F : V → M) (hF : Continuous F)
    (huniform : ∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x : V,
      edist (f^[n] p) (f^[n] (F x)) < ε)
    (x₀ : V) (ε : ENNReal) (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ n : ℕ, edist (f^[n] (F x₀)) (f^[n] (F x)) < ε := by
  obtain ⟨N, hN⟩ := huniform (ε / 2) (ENNReal.half_pos hε.ne')
  have hfinite : ∀ᶠ x in 𝓝 x₀, ∀ n ∈ Finset.range N,
      edist (f^[n] (F x₀)) (f^[n] (F x)) < ε := by
    apply (eventually_all_finset (Finset.range N)).mpr
    intro n _
    have hcont := ((continuous_const (y := f^[n] (F x₀))).edist ((hf.iterate n).comp hF)).continuousAt (x := x₀)
    have hevent := hcont.eventually (gt_mem_nhds (by simpa only [Function.comp_apply, edist_self] using hε))
    exact hevent
  filter_upwards [hfinite] with x hx n
  by_cases hn : n < N
  · exact hx n (Finset.mem_range.mpr hn)
  · apply (edist_triangle _ (f^[n] p) _).trans_lt
    rw [edist_comm (f^[n] (F x₀))]
    exact (ENNReal.add_lt_add (hN n (Nat.le_of_not_gt hn) x₀)
      (hN n (Nat.le_of_not_gt hn) x)).trans_eq (ENNReal.add_halves ε)


theorem exponential_fibreMap_contMDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [Bundle.RiemannianBundle (fun p : M ↦ TangentSpace 𝓘(ℝ, E) p)]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (ψ : V → TangentSpace 𝓘(ℝ, E) p) (n : ℕ∞ω) (hn : n ≤ (∞ : ℕ∞ω))
    (hψ : ContDiff ℝ n ψ) (U : Set V)
    (hU : ∀ v ∈ U, (⟨p, ψ v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈
      ExponentialLift.riemannianExpDomain g) :
    ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) n
      (fun v ↦ ExponentialLift.riemannianExp g p (ψ v)) U := by
  have hcast := (tangentSpaceCastModel 𝓘(ℝ, E) p).contDiff.comp hψ
  have hins := ((ExponentialLift.fixed_fibre_contMDiff p).of_le hn).comp
    hcast.contMDiff
  have hi : ContMDiff 𝓘(ℝ, V) (𝓘(ℝ, E)).tangent n
      (fun v ↦ (⟨p, ψ v⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hins
  exact ((riemannian_exponential_local_addition g).2.2.1.of_le hn).comp hi.contMDiffOn hU


def transportedPlaque {M : Type*} (f : M ≃ M) (P : M → Set M)
    (p : M) (n : ℕ) : Set M := (f^[n]) ⁻¹' P (f^[n] p)

theorem transportedPlaque_increasing {M : Type*} (f : M ≃ M) (P : M → Set M)
    (hP : ∀ p, f '' P p ⊆ P (f p)) (p : M) (n : ℕ) :
    transportedPlaque f P p n ⊆ transportedPlaque f P p (n + 1) := by
  intro q hq
  change f^[n + 1] q ∈ P (f^[n + 1] p)
  simp only [Function.iterate_succ_apply']
  exact hP (f^[n] p) (mem_image_of_mem f hq)

theorem transportedPlaque_image {M : Type*} (f : M ≃ M) (P : M → Set M)
    (p : M) (n : ℕ) :
    transportedPlaque f P p n = (f.symm^[n]) '' P (f^[n] p) := by
  ext q
  constructor
  · intro hq
    refine ⟨f^[n] q, hq, ?_⟩
    exact (f.left_inv.iterate n) q
  · rintro ⟨q, hq, rfl⟩
    change f^[n] (f.symm^[n] q) ∈ P (f^[n] p)
    have heq : (f : M → M)^[n] ((f.symm : M → M)^[n] q) = q :=
      (f.right_inv.iterate n) q
    rwa [heq]


def orbitAsymptoticSetoid {M : Type*} [EMetricSpace M] (f : M → M) : Setoid M where
  r p q := Tendsto (fun n : ℕ ↦ edist (f^[n] p) (f^[n] q)) atTop (𝓝 0)
  iseqv := {
    refl := fun p ↦ by simpa only [edist_self] using (tendsto_const_nhds (x := (0 : ENNReal)))
    symm := fun {p q} h ↦ by simpa only [edist_comm] using h
    trans := fun {p q r} hpq hqr ↦ by
      have hh := hpq.add hqr
      rw [zero_add] at hh
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
        (fun _ ↦ bot_le) (fun n ↦ edist_triangle (f^[n] p) (f^[n] q) (f^[n] r)) }

theorem orbitAsymptotic_shift {M : Type*} [EMetricSpace M] (f : M → M)
    (p q : M) (N : ℕ) :
    (orbitAsymptoticSetoid f).r (f^[N] p) (f^[N] q) ↔ (orbitAsymptoticSetoid f).r p q := by
  change Tendsto (fun n : ℕ ↦ edist (f^[n] (f^[N] p)) (f^[n] (f^[N] q))) atTop (𝓝 0) ↔
    Tendsto (fun n : ℕ ↦ edist (f^[n] p) (f^[n] q)) atTop (𝓝 0)
  simpa only [Function.iterate_add_apply] using
    (tendsto_add_atTop_iff_nat N (f := fun n : ℕ ↦ edist (f^[n] p) (f^[n] q)))

theorem asymptotic_eventually_close {M : Type*} [EMetricSpace M]
    (f : M → M) (p q : M) (ε : ENNReal) (hε : 0 < ε)
    (h : Tendsto (fun n : ℕ ↦ edist (f^[n] p) (f^[n] q)) atTop (𝓝 0)) :
    ∃ N : ℕ, ∀ n : ℕ, edist (f^[n] (f^[N] p)) (f^[n] (f^[N] q)) < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds hε))
  refine ⟨N, fun n ↦ ?_⟩
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
  exact hN (n + N) (Nat.le_add_left N n)


theorem invariant_iterate_value {M A : Type*} (f : M → M) (r : M → A)
    (hr : ∀ p, r (f p) = r p) (p : M) (n : ℕ) : r (f^[n] p) = r p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hr, ih]


theorem graph_norm
    {U V : Type*} [NormedAddCommGroup U] [NormedAddCommGroup V]
    (t : V → U) (ht : LipschitzWith 1 t) (ht0 : t 0 = 0) (y : V) :
    ‖(t y, y)‖ = ‖y‖ := by
  rw [Prod.norm_def, max_eq_right]
  have h := ht.dist_le_mul y 0
  simpa only [ht0, dist_zero_right, NNReal.coe_one, one_mul] using h

theorem stable_graph_image_norm
    {U V U' V' : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    (T₁ : U →L[ℝ] U') (T₂ : V →L[ℝ] V') (G : U × V → U' × V')
    (t : V → U) (t' : V' → U')
    (ht : LipschitzWith 1 t) (ht0 : t 0 = 0)
    (ht' : LipschitzWith 1 t') (ht'0 : t' 0 = 0)
    (hgraph : ∀ y, (G (t y, y)).1 = t' (G (t y, y)).2)
    (hG0 : G 0 = 0) (η : NNReal)
    (hG : LipschitzWith η (fun z ↦ G z - (T₁ z.1, T₂ z.2)))
    (k : ℝ) (hk : ‖T₂‖ ≤ k) (y : V) :
    ‖G (t y, y)‖ ≤ (k + η) * ‖(t y, y)‖ := by
  have hR0 : G 0 - (T₁ (0 : U × V).1, T₂ (0 : U × V).2) = 0 := by
    simp [hG0]
  have hR := hG.dist_le_mul (t y, y) 0
  rw [hR0, dist_zero_right, dist_zero_right] at hR
  have hsecond : ‖(G (t y, y)).2 - T₂ y‖ ≤ (η : ℝ) * ‖(t y, y)‖ :=
    (norm_snd_le (G (t y, y) - (T₁ (t y), T₂ y))).trans hR
  have hg : ‖G (t y, y)‖ = ‖(G (t y, y)).2‖ := by
    conv_lhs => rw [← Prod.eta (G (t y, y)), hgraph]
    exact graph_norm t' ht' ht'0 _
  rw [hg, graph_norm t ht ht0 y] at *
  calc
    ‖(G (t y, y)).2‖ ≤ ‖T₂ y‖ + ‖(G (t y, y)).2 - T₂ y‖ :=
      by simpa only [norm_sub_rev] using norm_le_insert (T₂ y) (G (t y, y)).2
    _ ≤ k * ‖y‖ + (η : ℝ) * ‖y‖ :=
      add_le_add ((T₂.le_opNorm y).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _)))
        hsecond
    _ = (k + η) * ‖y‖ := (add_mul _ _ _).symm

theorem unstable_graph_preimage_norm
    {U V U' V' : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    (T₁ : U ≃L[ℝ] U') (T₂ : V →L[ℝ] V') (G : U × V → U' × V')
    (s : U → V) (hs : LipschitzWith 1 s) (hs0 : s 0 = 0)
    (hG0 : G 0 = 0) (η : NNReal)
    (hG : LipschitzWith η (fun z ↦ G z - (T₁ z.1, T₂ z.2)))
    (a : ℝ) (ha : 0 ≤ a) (hTa : ‖T₁.symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : a * (η : ℝ) < 1) (x : U) :
    ‖(x, s x)‖ ≤ (a / (1 - a * η)) * ‖G (x, s x)‖ := by
  have hx : ‖(x, s x)‖ = ‖x‖ := by
    rw [Prod.norm_def, max_eq_left]
    have h := hs.dist_le_mul x 0
    simpa only [hs0, dist_zero_right, NNReal.coe_one, one_mul] using h
  have hR0 : G 0 - (T₁ (0 : U × V).1, T₂ (0 : U × V).2) = 0 := by
    simp [hG0]
  have hR := hG.dist_le_mul (x, s x) 0
  rw [hR0, dist_zero_right, dist_zero_right] at hR
  have hfirst : ‖(G (x, s x)).1 - T₁ x‖ ≤ (η : ℝ) * ‖(x, s x)‖ :=
    (norm_fst_le (G (x, s x) - (T₁ x, T₂ (s x)))).trans hR
  have hinv : ‖x‖ ≤ a * ‖T₁ x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      (T₁.symm.toContinuousLinearMap.le_opNorm (T₁ x)).trans
        (mul_le_mul_of_nonneg_right hTa (norm_nonneg _))
  have hT : ‖T₁ x‖ ≤ ‖G (x, s x)‖ + (η : ℝ) * ‖(x, s x)‖ :=
    (norm_le_insert (G (x, s x)).1 (T₁ x)).trans
      (add_le_add (norm_fst_le _) hfirst)
  rw [hx] at hfirst hT ⊢
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 - a * (η : ℝ))).mpr
  have hb := mul_le_mul_of_nonneg_left hT ha
  nlinarith

end HolomorphicAnosov.HPS
