import HolomorphicAnosov.Dynamics.Anosov.LocalStrongPlaqueConstruction
import HolomorphicAnosov.Dynamics.Anosov.SelectedPartitionProducts
import HolomorphicAnosov.Geometry.AdaptedNativeProductRealBoxes
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaques
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaquesGeometry
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Dynamics.Anosov.NativeBoxesTopologyGeneratedG18
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
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Dynamics.Anosov.DistanceLeafRange
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathMap
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathSpeedIntegrable
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathLength
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothRiemannianEDistLePath
import HolomorphicAnosov.Geometry.Riemannian.RiemannianEDistLePiecewiseSmooth
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import HolomorphicAnosov.Geometry.Riemannian.ConnectedSmoothPathExists
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorMetric
import HolomorphicAnosov.Dynamics.Anosov.FiniteC1NativePlaqueExport
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetricInner
import HolomorphicAnosov.Paper.Zhang.StableFoliationsTensorBoundsOfExactPairing
import HolomorphicAnosov.Geometry.ComplexSubbundleChart
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgradeOfComplexTangent
import HolomorphicAnosov.Geometry.ComplexDerivativeRangeOfRealCharts
import HolomorphicAnosov.Dynamics.Anosov.NativeProductBoxDimension
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Basic
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseSplitting

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped ContDiff Manifold
namespace HolomorphicAnosov.HPS
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]
variable {D : RealTangentDistribution 𝓘(ℝ, E) M}
variable {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
variable {F : LeafPartition D ι L r}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- In a native product box, at most countably many plaques belong to a fixed intrinsic leaf. -/
theorem NativeProductBox.countable_labels
    {d : ℕ} {T : Type u} [TopologicalSpace T]
    (B : NativeProductBox F d T) (i : ι) : {t | B.label t = i}.Countable := by
  let := (F.leaf i).countable
  let Z := {t : T // B.label t = i}
  let p : Z → B.disc → L i := fun t v ↦ t.property ▸ (B.chart t.val v).val
  have hinc (t : Z) (v : B.disc) :
      (F.leaf i).inclusion (p t v) = (B.box (v,t.val)).val := by
    have hc (j : ι) (h : B.label t.val = j) :
        (F.leaf j).inclusion (h ▸ (B.chart t.val v).val) =
        (F.leaf (B.label t.val)).inclusion (B.chart t.val v) := by
      subst j
      rfl
    exact (hc i t.property).trans (B.factorization t.val v).symm
  have hopen (t : Z) : IsOpen (Set.range (p t)) := by
    have hh (j : ι) (h : B.label t.val = j) :
        IsOpen (Set.range (fun v : B.disc ↦ (h ▸ (B.chart t.val v).val : L j))) := by
      subst j
      have he : Set.range (fun v : B.disc ↦ (B.chart t.val v).val) =
          (B.plaque t.val : Set (L (B.label t.val))) := by
        ext x
        constructor
        · rintro ⟨v, rfl⟩
          exact (B.chart t.val v).property
        · intro hx
          exact ⟨(B.chart t.val).symm ⟨x,hx⟩,
            congrArg Subtype.val ((B.chart t.val).apply_symm_apply ⟨x,hx⟩)⟩
      rw [he]
      exact (B.plaque t.val).isOpen
    exact hh i t.property
  have hne (t : Z) : (Set.range (p t)).Nonempty := by
    obtain ⟨v,hv⟩ := B.disc_connected.nonempty
    exact ⟨p t ⟨v,hv⟩, ⟨⟨v,hv⟩,rfl⟩⟩
  have hd : Pairwise (fun t t' : Z ↦ Disjoint (Set.range (p t)) (Set.range (p t'))) := by
    intro t t' hne
    apply Set.disjoint_left.mpr
    rintro x ⟨v,hv⟩ ⟨v',hv'⟩
    apply hne
    apply Subtype.ext
    have hh := congrArg (F.leaf i).inclusion (hv.trans hv'.symm)
    rw [hinc,hinc] at hh
    exact congrArg Prod.snd (B.box.injective (Subtype.ext hh))
  have : Countable Z := hd.countable_of_isOpen_disjoint hopen hne
  exact @Set.to_countable _ _ (show Countable Z from inferInstance)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A map from a locally connected space into a native lamination leaf is intrinsically continuous
whenever its composition with the ambient inclusion is continuous. -/
theorem LaminationBoxes.continuous_of_inclusion_comp
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) (i : ι)
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (g : X → L i) (hg : Continuous ((F.leaf i).inclusion ∘ g)) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨b,hb⟩ := boxes.cover ((F.leaf i).inclusion (g a))
  let B := boxes.boxes b
  have hn : ((F.leaf i).inclusion ∘ g) ⁻¹' (B.ambient : Set M) ∈ 𝓝 a :=
    (B.ambient.isOpen.preimage hg).mem_nhds hb
  obtain ⟨V, ⟨hV,haV,hcV⟩,hsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis a).mem_iff.mp hn
  let : PreconnectedSpace V := Subtype.preconnectedSpace hcV.isPreconnected
  let u : V → B.ambient := fun z ↦ ⟨(F.leaf i).inclusion (g z.val), hsub z.property⟩
  have hu : Continuous u := (hg.comp continuous_subtype_val).subtype_mk _
  let coords : V → B.disc × T b := fun z ↦ B.box.symm (u z)
  have hcoords : Continuous coords := B.box.symm.continuous.comp hu
  have hr : Set.range (fun z : V ↦ (coords z).2) ⊆ {t | B.label t = i} := by
    rintro t ⟨z,rfl⟩
    apply F.disjoint _ i ((B.chart (coords z).2 (coords z).1).val) (g z.val)
    rw [← B.factorization,Prod.mk.eta]
    exact congrArg Subtype.val (B.box.apply_symm_apply (u z))
  let tr : V → B.transverseDisc := fun z ↦ B.transverse_chart (coords z).2
  have htr : Continuous tr := B.transverse_chart.continuous.comp (continuous_snd.comp hcoords)
  have htrange : Set.range tr ⊆ B.transverse_chart '' {t | B.label t = i} := by
    rintro _ ⟨z,rfl⟩
    exact ⟨(coords z).2,hr ⟨z,rfl⟩,rfl⟩
  have hconst := ((B.countable_labels i).image B.transverse_chart).isTotallyDisconnected
    (Set.range tr) htrange (isPreconnected_range htr)
  let aV : V := ⟨a,haV⟩
  have hz (z : V) : (coords z).2 = (coords aV).2 :=
    B.transverse_chart.injective (hconst ⟨z,rfl⟩ ⟨aV,rfl⟩)
  have hlabel := hr ⟨aV,rfl⟩
  have hplaque (t : T b) (j : ι) (ht : B.label t = j) :
      Continuous (fun v : B.disc ↦ (ht ▸ (B.chart t v).val : L j)) := by
    subst j
    exact continuous_subtype_val.comp (B.chart t).continuous
  have hfactor (t : T b) (j : ι) (ht : B.label t = j) (v : B.disc) :
      (F.leaf j).inclusion (ht ▸ (B.chart t v).val) = (B.box (v,t)).val := by
    subst j
    exact (B.factorization t v).symm
  have hc : Continuous (fun z : V ↦ g z.val) := by
    convert (hplaque (coords aV).2 i hlabel).comp (continuous_fst.comp hcoords) using 1
    funext z
    apply (F.leaf i).injective
    dsimp only [Function.comp_apply]
    rw [hfactor,← hz z,Prod.mk.eta]
    exact (congrArg Subtype.val (B.box.apply_symm_apply (u z))).symm
  exact hV.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hc.continuousAt (x := aV))

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A map from a locally connected manifold into a native lamination leaf is smooth whenever its
composition with the ambient inclusion is smooth. -/
theorem LaminationBoxes.contMDiff_of_inclusion_comp
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) (i : ι)
    {G X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace X] [ChartedSpace G X] [LocallyConnectedSpace X]
    (g : X → L i)
    (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) ∞ ((F.leaf i).inclusion ∘ g)) :
    ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) ∞ g := by
  apply (ContMDiff.iff_comp_isImmersion (F.leaf i).immersion).mpr
  exact ⟨boxes.continuous_of_inclusion_comp i g hg.continuous,hg⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A smooth map between native leaves of the same distribution that preserves ambient points is a
local diffeomorphism. -/
theorem NativeLeaf.lift_isLocalDiffeomorph
    {L₀ L₁ : Type u} {r₀ r₁ : ℕ}
    [TopologicalSpace L₀] [ChartedSpace (Fin r₀ → ℝ) L₀]
    [IsManifold 𝓘(ℝ,Fin r₀ → ℝ) ∞ L₀]
    [TopologicalSpace L₁] [ChartedSpace (Fin r₁ → ℝ) L₁]
    [IsManifold 𝓘(ℝ,Fin r₁ → ℝ) ∞ L₁]
    (A : NativeLeaf (r := r₀) D L₀) (B : NativeLeaf (r := r₁) D L₁)
    (g : L₀ → L₁) (hg : ContMDiff 𝓘(ℝ,Fin r₀ → ℝ) 𝓘(ℝ,Fin r₁ → ℝ) ∞ g)
    (hcomm : ∀ x, B.inclusion (g x) = A.inclusion x) :
    IsLocalDiffeomorph 𝓘(ℝ,Fin r₀ → ℝ) 𝓘(ℝ,Fin r₁ → ℝ) ∞ g := by
  intro x
  have heq : B.inclusion ∘ g = A.inclusion := funext hcomm
  have hder := mfderiv_comp x
    (B.immersion.contMDiff.mdifferentiable (by simp) (g x))
    (hg.mdifferentiable (by simp) x)
  rw [heq] at hder
  have hA := A.immersion.mfderiv_injective (by simp) x
  have hB := B.immersion.mfderiv_injective (by simp) (g x)
  have hrange :
      (mfderiv 𝓘(ℝ,Fin r₀ → ℝ) 𝓘(ℝ,E) A.inclusion x).range =
      (mfderiv 𝓘(ℝ,Fin r₁ → ℝ) 𝓘(ℝ,E) B.inclusion (g x)).range := by
    rw [A.tangent,B.tangent,hcomm]
  have hbij : Function.Bijective
      (mfderiv 𝓘(ℝ,Fin r₀ → ℝ) 𝓘(ℝ,Fin r₁ → ℝ) g x) := by
    constructor
    · intro v w hvw
      apply hA
      rw [hder]
      exact congrArg (mfderiv 𝓘(ℝ,Fin r₁ → ℝ) 𝓘(ℝ,E) B.inclusion (g x)) hvw
    · intro v
      have hv : mfderiv 𝓘(ℝ,Fin r₁ → ℝ) 𝓘(ℝ,E) B.inclusion (g x) v ∈
          (mfderiv 𝓘(ℝ,Fin r₀ → ℝ) 𝓘(ℝ,E) A.inclusion x).range := by
        rw [hrange]
        exact ⟨v,rfl⟩
      obtain ⟨w,hw⟩ := hv
      refine ⟨w,hB ?_⟩
      rw [hder] at hw
      exact hw
  let a := (LinearEquiv.ofBijective
    (mfderiv 𝓘(ℝ,Fin r₀ → ℝ) 𝓘(ℝ,Fin r₁ → ℝ) g x).toLinearMap hbij).toContinuousLinearEquiv
  obtain ⟨e,hx,_,he⟩ := W07ManifoldInverseFunction.exists_partialDiffeomorph
    isOpen_univ (Set.mem_univ x) hg.contMDiffOn a (by rfl)
  exact ⟨e,hx,he⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- An immersed leaf partition refining a native lamination of the same distribution has leaves
diffeomorphic to the lamination leaves by maps preserving ambient points. -/
theorem LeafPartition.diffeomorph_of_refines
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T)
    {κ : Type u} {K : κ → Type u} {q : κ → ℕ}
    [∀ k, TopologicalSpace (K k)] [∀ k, ChartedSpace (Fin (q k) → ℝ) (K k)]
    [∀ k, IsManifold 𝓘(ℝ,Fin (q k) → ℝ) ∞ (K k)]
    (A : LeafPartition D κ K q)
    (hrefines : ∀ k, ∃ i, Set.range (A.leaf k).inclusion ⊆ Set.range (F.leaf i).inclusion)
    (k₀ : κ) :
    ∃ i, ∃ e : Diffeomorph 𝓘(ℝ,Fin (q k₀) → ℝ) 𝓘(ℝ,Fin (r i) → ℝ) (K k₀) (L i) ∞,
      ∀ x, (F.leaf i).inclusion (e x) = (A.leaf k₀).inclusion x := by
  classical
  choose σ hσ using hrefines
  let i := σ k₀
  let J := {k : κ // σ k = i}
  have hin (k : J) (x : K k.val) : ∃ y : L i,
      (F.leaf i).inclusion y = (A.leaf k.val).inclusion x := by
    have h := hσ k.val (Set.mem_range_self x)
    rw [k.property] at h
    exact h
  choose g hcomm using hin
  have hsmooth (k : J) : ContMDiff 𝓘(ℝ,Fin (q k.val) → ℝ) 𝓘(ℝ,Fin (r i) → ℝ) ∞ (g k) := by
    let : LocallyConnectedSpace (K k.val) := ChartedSpace.locallyConnectedSpace
      (Fin (q k.val) → ℝ) (K k.val)
    apply boxes.contMDiff_of_inclusion_comp i (g k)
    have he : (F.leaf i).inclusion ∘ g k = (A.leaf k.val).inclusion := funext (hcomm k)
    rw [he]
    exact (A.leaf k.val).immersion.contMDiff
  have hlocal (k : J) : IsLocalDiffeomorph 𝓘(ℝ,Fin (q k.val) → ℝ)
      𝓘(ℝ,Fin (r i) → ℝ) ∞ (g k) :=
    (A.leaf k.val).lift_isLocalDiffeomorph (F.leaf i) (g k) (hsmooth k) (hcomm k)
  have hcover (x : L i) : ∃ k : J, x ∈ Set.range (g k) := by
    obtain ⟨k,z,hz⟩ := A.cover ((F.leaf i).inclusion x)
    obtain ⟨w,hw⟩ := hσ k (Set.mem_range_self z)
    have hk : σ k = i := F.disjoint _ _ w x (hw.trans hz)
    refine ⟨⟨k,hk⟩,z,?_⟩
    apply (F.leaf i).injective
    exact (hcomm ⟨k,hk⟩ z).trans hz
  have hne (k : J) : (Set.range (g k)).Nonempty := by
    let := (A.leaf k.val).connected
    exact Set.range_nonempty _
  have hd : Pairwise (fun k l : J ↦ Disjoint (Set.range (g k)) (Set.range (g l))) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    rintro x ⟨v,hv⟩ ⟨w,hw⟩
    apply hkl
    apply Subtype.ext
    apply A.disjoint _ _ v w
    exact (hcomm k v).symm.trans ((congrArg (F.leaf i).inclusion (hv.trans hw.symm)).trans (hcomm l w))
  have hUnion : ⋃ k : J, Set.range (g k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k,hk⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨k,hk⟩
  let := (F.leaf i).connected
  have : Subsingleton J := subsingleton_of_disjoint_isOpen_iUnion_eq_univ
    hne hd (fun k ↦ (hlocal k).isOpen_range) hUnion
  let j₀ : J := ⟨k₀,rfl⟩
  have hsurj : Function.Surjective (g j₀) := by
    intro x
    obtain ⟨k,hk⟩ := hcover x
    have he : k = j₀ := Subsingleton.elim _ _
    subst k
    exact hk
  have hinj : Function.Injective (g j₀) := by
    intro x y hxy
    apply (A.leaf k₀).injective
    exact (hcomm j₀ x).symm.trans ((congrArg (F.leaf i).inclusion hxy).trans (hcomm j₀ y))
  exact ⟨i,(hlocal j₀).diffeomorphOfBijective ⟨hinj,hsurj⟩,hcomm j₀⟩

end HolomorphicAnosov.HPS




namespace HolomorphicAnosov.HPS
open Set
open scoped ContDiff Manifold
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ,E) ∞ M]
variable {D : RealTangentDistribution 𝓘(ℝ,E) M}
variable {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ,Fin (r i) → ℝ) ∞ (L i)]
variable {F : LeafPartition D ι L r}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A smooth full-rank parametrization contained in a native leaf of the same dimension lifts to a
local diffeomorphism into that leaf. (HPS, (5.5)) -/
theorem LaminationBoxes.lift_parametrization
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) (i : ι)
    {G X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace X] [ChartedSpace G X] [IsManifold 𝓘(ℝ,G) ∞ X]
    (hdim : Module.finrank ℝ G = r i)
    (a : X → M) (ha : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) ∞ a)
    (hder : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) a x))
    (hmem : Set.range a ⊆ Set.range (F.leaf i).inclusion) :
    ∃ g : X → L i, IsLocalDiffeomorph 𝓘(ℝ,G)
      𝓘(ℝ,Fin (r i) → ℝ) ∞ g ∧ ∀ x, (F.leaf i).inclusion (g x) = a x := by
  classical
  have hex (x : X) : ∃ y, (F.leaf i).inclusion y = a x := hmem (Set.mem_range_self x)
  choose g hcomm using hex
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace G X
  have heq : (F.leaf i).inclusion ∘ g = a := funext hcomm
  have hg := boxes.contMDiff_of_inclusion_comp i g (by rw [heq]; exact ha)
  refine ⟨g, ?_, hcomm⟩
  intro x
  have hc := mfderiv_comp x
    ((F.leaf i).immersion.contMDiff.mdifferentiable (by simp) (g x))
    (hg.mdifferentiable (by simp) x)
  rw [heq] at hc
  have hinj : Function.Injective
      (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) g x) := by
    intro v w hvw
    apply hder x
    rw [hc]
    exact congrArg (mfderiv 𝓘(ℝ,Fin (r i) → ℝ) 𝓘(ℝ,E) (F.leaf i).inclusion (g x)) hvw
  have hbij : Function.Bijective
      (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) g x) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by change Module.finrank ℝ G = Module.finrank ℝ (Fin (r i) → ℝ); simpa using hdim)).mp hinj⟩
  let A := (LinearEquiv.ofBijective
    (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) g x).toLinearMap hbij).toContinuousLinearEquiv
  obtain ⟨e,hx,_,he⟩ := W07ManifoldInverseFunction.exists_partialDiffeomorph
    isOpen_univ (Set.mem_univ x) hg.contMDiffOn A (by rfl)
  exact ⟨e,hx,he⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- An injective smooth full-rank parametrization contained in a native leaf of the same dimension
parametrizes an intrinsically open plaque by a diffeomorphism. -/
theorem LaminationBoxes.native_chart_of_parametrization
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) (i : ι)
    {G X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace X] [ChartedSpace G X] [IsManifold 𝓘(ℝ,G) ∞ X]
    (hdim : Module.finrank ℝ G = r i)
    (a : X → M) (ha : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) ∞ a)
    (hinj : Function.Injective a)
    (hder : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) a x))
    (hmem : Set.range a ⊆ Set.range (F.leaf i).inclusion) :
    ∃ V : TopologicalSpace.Opens (L i),
      ∃ c : Diffeomorph 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) X V ∞,
        ∀ x, (F.leaf i).inclusion (c x) = a x := by
  classical
  obtain ⟨g,hlocal,hcomm⟩ := boxes.lift_parametrization i hdim a ha hder hmem
  let V : TopologicalSpace.Opens (L i) := ⟨Set.range g,hlocal.isOpen_range⟩
  let g' : X → V := fun x ↦ ⟨g x,Set.mem_range_self x⟩
  have hg' : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) ∞ g' :=
    (ContMDiff.subtypeVal_comp_iff V g').mp hlocal.contMDiff
  have hbij : Function.Bijective g' := by
    constructor
    · intro x y hxy
      apply hinj
      rw [← hcomm x,← hcomm y]
      exact congrArg (F.leaf i).inclusion (congrArg Subtype.val hxy)
    · rintro ⟨y,x,hx⟩
      exact ⟨x,Subtype.ext hx⟩
  have hlocal' : IsLocalDiffeomorph 𝓘(ℝ,G)
      𝓘(ℝ,Fin (r i) → ℝ) ∞ g' := by
    intro x
    have hc := mfderiv_comp x
      ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiable (by simp) (g' x))
      (hg'.mdifferentiable (by simp) x)
    have hc' : Subtype.val ∘ g' = g := rfl
    rw [hc'] at hc
    have hginj : Function.Injective
        (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) g x) :=
      (hlocal.mfderivToContinuousLinearEquiv (by simp) x).injective
    have hdi : Function.Injective
        (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) g' x) := by
      intro v w hvw
      apply hginj
      rw [hc]
      exact congrArg (mfderiv 𝓘(ℝ,Fin (r i) → ℝ) 𝓘(ℝ,Fin (r i) → ℝ)
        (Subtype.val : V → L i) (g' x)) hvw
    let A := (LinearEquiv.ofBijective
      (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) g' x).toLinearMap
      ⟨hdi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by change Module.finrank ℝ G = Module.finrank ℝ (Fin (r i) → ℝ); simpa using hdim)).mp hdi⟩).toContinuousLinearEquiv
    obtain ⟨e,hx,_,he⟩ := W07ManifoldInverseFunction.exists_partialDiffeomorph
      isOpen_univ (Set.mem_univ x) hg'.contMDiffOn A (by rfl)
    exact ⟨e,hx,he⟩
  exact ⟨V,hlocal'.diffeomorphOfBijective hbij,hcomm⟩

end HolomorphicAnosov.HPS


noncomputable section
open scoped ContDiff Manifold
open TopologicalSpace

namespace HolomorphicAnosov

/-- Compatible diffeomorphisms on increasing open domains exhausting the source and target extend to
a global diffeomorphism. (Smale, Thm 4.1, pp.105–106) -/
theorem diffeomorph_of_exhausting_open_charts
    {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (U : ℕ → Opens M) (V : ℕ → Opens N)
    (e : ∀ n, Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) (U n) (V n) ∞)
    (hU : Monotone U)
    (hcoverU : ∀ x : M, ∃ n, x ∈ U n)
    (hcoverV : ∀ y : N, ∃ n, y ∈ V n)
    (hcompat : ∀ n m (hnm : n ≤ m) (x : U n),
      (e n x : N) = (e m ⟨x, hU hnm x.property⟩ : N)) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞,
      ∀ n (x : U n), D x = (e n x : N) := by
  classical
  let index (x : M) := (hcoverU x).choose
  have hindex (x : M) : x ∈ U (index x) := (hcoverU x).choose_spec
  let f (x : M) : N := e (index x) ⟨x, hindex x⟩
  have hf (n : ℕ) (x : U n) : f x = (e n x : N) := by
    change (e (index x) ⟨x, hindex x⟩ : N) = _
    rw [hcompat (index x) (max (index x) n) (le_max_left _ _),
      hcompat n (max (index x) n) (le_max_right _ _)]
  have hinj : Function.Injective f := by
    intro x y hxy
    let n := max (index x) (index y)
    have hx : x ∈ U n := hU (le_max_left _ _) (hindex x)
    have hy : y ∈ U n := hU (le_max_right _ _) (hindex y)
    have h : e n ⟨x, hx⟩ = e n ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [← hf n ⟨x, hx⟩, ← hf n ⟨y, hy⟩] using hxy
    exact congrArg Subtype.val ((e n).injective h)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨n, hn⟩ := hcoverV y
    refine ⟨(e n).symm ⟨y, hn⟩, ?_⟩
    rw [hf]
    exact congrArg Subtype.val ((e n).apply_symm_apply ⟨y, hn⟩)
  let D := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hD (n : ℕ) (x : U n) : D x = (e n x : N) := hf n x
  have hInv (n : ℕ) (y : V n) : D.symm y = ((e n).symm y : M) := by
    apply D.injective
    rw [D.apply_symm_apply, hD]
    exact (congrArg Subtype.val ((e n).apply_symm_apply y)).symm
  refine ⟨{ toEquiv := D, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }, hD⟩
  · intro x
    obtain ⟨n, hn⟩ := hcoverU x
    apply (contMDiffAt_subtype_iff (x := (⟨x, hn⟩ : U n))).mp
    have he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞
        (fun z : U n ↦ (e n z : N)) :=
      contMDiff_subtype_val.comp (e n).contMDiff
    have heq : (fun z : U n ↦ D z) = (fun z : U n ↦ (e n z : N)) := funext (hD n)
    rw [heq]
    exact he.contMDiffAt
  · intro y
    obtain ⟨n, hn⟩ := hcoverV y
    apply (contMDiffAt_subtype_iff (x := (⟨y, hn⟩ : V n))).mp
    have he : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞
        (fun z : V n ↦ ((e n).symm z : M)) :=
      contMDiff_subtype_val.comp (e n).symm.contMDiff
    have heq : (fun z : V n ↦ D.symm z) =
        (fun z : V n ↦ ((e n).symm z : M)) := funext (hInv n)
    rw [heq]
    exact he.contMDiffAt

/-- The restriction of a diffeomorphism to the preimage of an open target set. -/
def diffeomorphPreimageOpens
    {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) (V : Opens N) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F)
      (⟨D ⁻¹' (V : Set N), V.isOpen.preimage D.continuous⟩ : Opens M) V ∞ where
  toEquiv :=
    { toFun := fun x ↦ ⟨D x, x.property⟩
      invFun := fun y ↦ ⟨D.symm y, by simp⟩
      left_inv := fun x ↦ Subtype.ext (D.symm_apply_apply x)
      right_inv := fun y ↦ Subtype.ext (D.apply_symm_apply y) }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    exact D.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact D.symm.contMDiff.comp contMDiff_subtype_val

/-- Compatible local charts with uniformly contracting nonstationary coordinates and images
exhausting the leaf give a global Euclidean parametrization. (Smale, Thm 4.1, pp.105–106) -/
theorem diffeomorph_of_dependent_contracting_continuation
    {E F L : Type*} {Vf : ℕ → Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [∀ n, NormedAddCommGroup (Vf n)] [∀ n, NormedSpace ℝ (Vf n)]
    [TopologicalSpace L] [ChartedSpace F L]
    (A : ∀ n, Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Vf n) E (Vf n) ∞)
    (r q : ℝ) (hr : 0 < r) (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ n x, ‖A (n+1) x‖ ≤ q * ‖A n x‖)
    (V : ℕ → Opens L)
    (e : ∀ n, Diffeomorph 𝓘(ℝ, Vf n) 𝓘(ℝ, F)
      (⟨Metric.ball (0 : Vf n) r, Metric.isOpen_ball⟩ : Opens (Vf n)) (V n) ∞)
    (hcover : ∀ y : L, ∃ n, y ∈ V n)
    (hcompat : ∀ n m, n ≤ m → ∀ x (hn : A n x ∈ Metric.ball 0 r)
      (hm : A m x ∈ Metric.ball 0 r),
      (e n ⟨A n x, hn⟩ : L) = (e m ⟨A m x, hm⟩ : L)) :
    Nonempty (Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E L ∞) := by
  let B (n : ℕ) : Opens (Vf n) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  let U (n : ℕ) : Opens E := ⟨A n ⁻¹' (B n : Set (Vf n)), (B n).isOpen.preimage (A n).continuous⟩
  let charts (n : ℕ) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) (U n) (V n) ∞ :=
    (diffeomorphPreimageOpens (A n) (B n)).trans (e n)
  have hU : Monotone U := by
    apply monotone_nat_of_le_succ
    intro n x hx
    change A (n+1) x ∈ Metric.ball 0 r
    rw [Metric.mem_ball, dist_zero_right]
    change A n x ∈ Metric.ball 0 r at hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact lt_of_le_of_lt ((hstep n x).trans
      (mul_le_of_le_one_left (norm_nonneg _) hq1.le)) hx
  have hbound : ∀ n x, ‖A n x‖ ≤ q^n * ‖A 0 x‖ := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        ‖A (n+1) x‖ ≤ q * ‖A n x‖ := hstep n x
        _ ≤ q * (q^n * ‖A 0 x‖) := mul_le_mul_of_nonneg_left ih hq
        _ = q^(n+1) * ‖A 0 x‖ := by rw [pow_succ]; ring
  have hcoverU : ∀ x : E, ∃ n, x ∈ U n := by
    intro x
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const ‖A 0 x‖
    simp only [zero_mul] at ht
    have he : ∀ᶠ n : ℕ in Filter.atTop, q^n * ‖A 0 x‖ < r :=
      (Filter.Tendsto.eventually_lt_const hr ht)
    obtain ⟨n, hn⟩ := he.exists
    refine ⟨n, ?_⟩
    change A n x ∈ Metric.ball 0 r
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hbound n x) hn
  obtain ⟨D, hD⟩ := diffeomorph_of_exhausting_open_charts U V charts hU hcoverU hcover
    (by intro n m hnm x; exact hcompat n m hnm x x.property (hU hnm x.property))
  exact ⟨D⟩

/-- Local charts with uniformly contracting coordinates and images exhausting the leaf give a global
Euclidean parametrization when consecutive charts agree. -/
theorem diffeomorph_of_dependent_contracting_one_step_continuation
    {E F L : Type*} {Vf : ℕ → Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [∀ n, NormedAddCommGroup (Vf n)] [∀ n, NormedSpace ℝ (Vf n)]
    [TopologicalSpace L] [ChartedSpace F L]
    (A : ∀ n, Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Vf n) E (Vf n) ∞)
    (r q : ℝ) (hr : 0 < r) (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ n x, ‖A (n+1) x‖ ≤ q * ‖A n x‖)
    (V : ℕ → Opens L)
    (e : ∀ n, Diffeomorph 𝓘(ℝ, Vf n) 𝓘(ℝ, F)
      (⟨Metric.ball (0 : Vf n) r, Metric.isOpen_ball⟩ : Opens (Vf n)) (V n) ∞)
    (hcover : ∀ y : L, ∃ n, y ∈ V n)
    (hcompat : ∀ n x (hn : A n x ∈ Metric.ball 0 r)
      (hn' : A (n+1) x ∈ Metric.ball 0 r),
      (e n ⟨A n x, hn⟩ : L) = (e (n+1) ⟨A (n+1) x, hn'⟩ : L)) :
    Nonempty (Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E L ∞) := by
  have hremain (n m : ℕ) (hnm : n ≤ m) (x : E)
      (hn : A n x ∈ Metric.ball 0 r) : A m x ∈ Metric.ball 0 r := by
    induction m, hnm using Nat.le_induction with
    | base => exact hn
    | succ m hnm ih =>
      rw [Metric.mem_ball, dist_zero_right] at ih ⊢
      exact lt_of_le_of_lt ((hstep m x).trans
        (mul_le_of_le_one_left (norm_nonneg _) hq1.le)) ih
  apply diffeomorph_of_dependent_contracting_continuation A r q hr hq hq1 hstep V e hcover
  intro n m hnm x hn hm
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have hm' := hremain n m hnm x hn
    exact (ih hm').trans (hcompat m x hm' hm)

/-- Local charts with uniformly contracting coordinates and images exhausting the leaf give a global
Euclidean parametrization when their ambient inclusions obey the one-step dynamical equation. -/
theorem diffeomorph_of_dependent_dynamical_continuation
    {E F L M : Type*} {Vf : ℕ → Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [∀ n, NormedAddCommGroup (Vf n)] [∀ n, NormedSpace ℝ (Vf n)]
    [TopologicalSpace L] [ChartedSpace F L]
    (inc : L → M) (hinj : Function.Injective inc) (g : M ≃ M)
    (A : ∀ n, Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Vf n) E (Vf n) ∞)
    (r q : ℝ) (hr : 0 < r) (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ n x, ‖A (n+1) x‖ ≤ q * ‖A n x‖)
    (V : ℕ → Opens L)
    (e : ∀ n, Diffeomorph 𝓘(ℝ, Vf n) 𝓘(ℝ, F)
      (⟨Metric.ball (0 : Vf n) r, Metric.isOpen_ball⟩ : Opens (Vf n)) (V n) ∞)
    (hcover : ∀ y : L, ∃ n, y ∈ V n)
    (plaque : ∀ n, Vf n → M)
    (hfactor : ∀ n (v : Metric.ball (0 : Vf n) r),
      inc (e n v) = (g.symm : M → M)^[n] (plaque n v))
    (hreturn : ∀ n x, A n x ∈ Metric.ball 0 r →
      plaque (n+1) (A (n+1) x) = g (plaque n (A n x))) :
    Nonempty (Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E L ∞) := by
  apply diffeomorph_of_dependent_contracting_one_step_continuation A r q hr hq hq1 hstep V e hcover
  intro n x hn hn'
  apply hinj
  rw [hfactor, hfactor, hreturn n x hn, Function.iterate_succ_apply, g.symm_apply_apply]

end HolomorphicAnosov

namespace HolomorphicAnosov.HPS
open Set TopologicalSpace
open scoped ContDiff Manifold
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ,E) ∞ M]
variable {D : RealTangentDistribution 𝓘(ℝ,E) M}
variable {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ,Fin (r i) → ℝ) ∞ (L i)]
variable {F : LeafPartition D ι L r}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Compatible smooth full-rank parametrizations covering a native leaf, with contracting
diffeomorphisms between their parameter fibres, give a global Euclidean model of the leaf. -/
theorem LaminationBoxes.euclidean_of_contracting_parametrizations
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) (i : ι)
    {Vf : ℕ → Type*} [∀ n, NormedAddCommGroup (Vf n)]
    [∀ n, NormedSpace ℝ (Vf n)] [∀ n, FiniteDimensional ℝ (Vf n)]
    (hdim : ∀ n, Module.finrank ℝ (Vf n) = r i)
    (R : ∀ n, Diffeomorph 𝓘(ℝ,Vf n) 𝓘(ℝ,Vf (n+1)) (Vf n) (Vf (n+1)) ∞)
    (ρ q : ℝ) (hρ : 0 < ρ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ n x, ‖R n x‖ ≤ q * ‖x‖)
    (a : ∀ n, (⟨Metric.ball (0 : Vf n) ρ,Metric.isOpen_ball⟩ : Opens (Vf n)) → M)
    (ha : ∀ n, ContMDiff 𝓘(ℝ,Vf n) 𝓘(ℝ,E) ∞ (a n))
    (hinj : ∀ n, Function.Injective (a n))
    (hder : ∀ n x, Function.Injective (mfderiv 𝓘(ℝ,Vf n) 𝓘(ℝ,E) (a n) x))
    (hmem : ∀ n, Set.range (a n) ⊆ Set.range (F.leaf i).inclusion)
    (hcover : ∀ y : L i, ∃ n, (F.leaf i).inclusion y ∈ Set.range (a n))
    (hcompat : ∀ n (x : Metric.ball (0 : Vf n) ρ)
      (hx : R n x ∈ Metric.ball (0 : Vf (n+1)) ρ),
      a (n+1) ⟨R n x,hx⟩ = a n x) :
    Nonempty (Diffeomorph 𝓘(ℝ,Vf 0) 𝓘(ℝ,Fin (r i) → ℝ) (Vf 0) (L i) ∞) := by
  classical
  have hchart (n : ℕ) := boxes.native_chart_of_parametrization i (hdim n)
    (a n) (ha n) (hinj n) (hder n) (hmem n)
  choose W c hc using hchart
  let A : ∀ n, Diffeomorph 𝓘(ℝ,Vf 0) 𝓘(ℝ,Vf n) (Vf 0) (Vf n) ∞ :=
    fun n ↦ Nat.rec (Diffeomorph.refl 𝓘(ℝ,Vf 0) (Vf 0) ∞) (fun n A ↦ A.trans (R n)) n
  have hstep (n : ℕ) (x : Vf 0) : ‖A (n+1) x‖ ≤ q * ‖A n x‖ :=
    hcontract n (A n x)
  apply diffeomorph_of_dependent_contracting_one_step_continuation A ρ q hρ hq hq1 hstep W c
  · intro y
    obtain ⟨n,x,hx⟩ := hcover y
    have hy : (c n x : L i) = y := (F.leaf i).injective ((hc n x).trans hx)
    exact ⟨n,hy ▸ (c n x).property⟩
  · intro n x hn hn'
    apply (F.leaf i).injective
    rw [hc,hc]
    exact (hcompat n ⟨A n x,hn⟩ hn').symm
end HolomorphicAnosov.HPS


noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology
namespace HolomorphicAnosov

/-- A smooth immersion is an immersion at every lower regularity. -/
theorem immersion_at_lower_regularity
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [TopologicalSpace Y] [ChartedSpace G Y]
    [IsManifold 𝓘(ℝ,E) ∞ X] [IsManifold 𝓘(ℝ,G) ∞ Y]
    {f : X → Y} (hf : Manifold.IsImmersion 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ f)
    {n : ℕ∞ω} (hn : n ≤ ∞) : Manifold.IsImmersion 𝓘(ℝ,E) 𝓘(ℝ,G) n f := by
  refine ⟨hf.complement,inferInstance,inferInstance,?_⟩
  intro x
  let h := hf.isImmersionOfComplement_complement x
  exact Manifold.IsImmersionAtOfComplement.mk_of_charts h.equiv h.domChart h.codChart
    h.mem_domChart_source h.mem_codChart_source
    (IsManifold.maximalAtlas_subset_of_le hn h.domChart_mem_maximalAtlas)
    (IsManifold.maximalAtlas_subset_of_le hn h.codChart_mem_maximalAtlas)
    h.source_subset_preimage_source h.writtenInCharts

/-- A continuously differentiable section of a map between manifolds of equal dimension is smooth at
each point whose image lies in a region where the map is smooth. -/
theorem contMDiffAt_section_of_smoothOn_equal_dimension
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [TopologicalSpace Y] [ChartedSpace G Y]
    [IsManifold 𝓘(ℝ,E) ∞ X] [IsManifold 𝓘(ℝ,G) ∞ Y]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ G)
    (U : Set Y) (hU : IsOpen U)
    (b : Y → X) (hb : ContMDiffOn 𝓘(ℝ,G) 𝓘(ℝ,E) ∞ b U)
    (g : X → Y) (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,G) 1 g)
    (x : X) (hmem : g x ∈ U)
    (hsection : ∀ x, b (g x) = x) : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ g x := by
  have heq : b ∘ g = id := funext hsection
  have hc := mfderiv_comp x ((hb.contMDiffAt (hU.mem_nhds hmem)).mdifferentiableAt (by simp))
    (hg.mdifferentiable (by simp) x)
  rw [heq,mfderiv_id] at hc
  have hsurj : Function.Surjective (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) b (g x)) := by
    intro v
    exact ⟨mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x v, congrArg (fun L ↦ L v) hc.symm⟩
  have hdim' : Module.finrank ℝ (TangentSpace 𝓘(ℝ,G) (g x)) =
      Module.finrank ℝ (TangentSpace 𝓘(ℝ,E) (b (g x))) := by
    change Module.finrank ℝ G = Module.finrank ℝ E
    exact hdim.symm
  have hbij : Function.Bijective (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) b (g x)) := ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mpr hsurj,hsurj⟩
  let A := (LinearEquiv.ofBijective (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) b (g x)).toLinearMap hbij).toContinuousLinearEquiv
  obtain ⟨p,hpx,_,he⟩ := W07ManifoldInverseFunction.exists_partialDiffeomorph
    hU hmem hb A (by rfl)
  have htarget : x ∈ p.target := by
    rw [← hsection x,he hpx]
    exact p.map_source hpx
  have hev : g =ᶠ[𝓝 x] p.symm := by
    filter_upwards [hg.continuous.continuousAt.preimage_mem_nhds
      (p.open_source.mem_nhds hpx)] with y hy
    have hpy : p (g y) = y := (he hy).symm.trans (hsection y)
    exact (p.left_inv hy).symm.trans (congrArg p.symm hpy)
  exact (p.symm.contMDiffOn.contMDiffAt (p.open_target.mem_nhds htarget)).congr_of_eventuallyEq hev
end HolomorphicAnosov

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold

/-- A C¹ graph carried into a smooth graph by an ambient diffeomorphism is smooth at points mapping
into the smooth region, when the parameter dimensions agree. -/
theorem contDiffAt_graph_of_smooth_image
    {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (hdim : Module.finrank ℝ F = Module.finrank ℝ H)
    (D : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G × H) (E × F) (G × H) ∞)
    (s : F → E) (hs : ContDiff ℝ 1 s)
    (t : H → G) (U : Set H) (hU : IsOpen U) (ht : ContDiffOn ℝ ∞ t U)
    (hgraph : ∀ y, D (s y,y) = (t (D (s y,y)).2,(D (s y,y)).2))
    (x : F) (hx : (D (s x,x)).2 ∈ U) : ContDiffAt ℝ ∞ s x := by
  let R : F → H := fun y ↦ (D (s y,y)).2
  let b : H → F := fun z ↦ (D.symm (t z,z)).2
  have hback (y : F) : D.symm (t (R y),R y) = (s y,y) := by
    change D.symm (t (D (s y,y)).2,(D (s y,y)).2) = _
    rw [← hgraph,D.symm_apply_apply]
  have hR : ContDiff ℝ 1 R :=
    (((contMDiff_iff_contDiff.mp D.contMDiff).of_le (by simp)).comp
      (hs.prodMk contDiff_id)).snd
  have hb : ContDiffOn ℝ ∞ b U :=
    ((contMDiff_iff_contDiff.mp D.symm.contMDiff).comp_contDiffOn
      (ht.prodMk contDiffOn_id)).snd
  have hsec := contMDiffAt_section_of_smoothOn_equal_dimension hdim U hU b
    hb.contMDiffOn R hR.contMDiff x hx (fun y ↦ congrArg Prod.snd (hback y))
  have hRsmooth : ContDiffAt ℝ ∞ R x := contMDiffAt_iff_contDiffAt.mp hsec
  have hcompsmooth : ContDiffAt ℝ ∞ (fun y ↦ D.symm (t (R y),R y)) x :=
    (contMDiff_iff_contDiff.mp D.symm.contMDiff).contDiffAt.comp x
      (((ht.contDiffAt (hU.mem_nhds hx)).comp x hRsmooth).prodMk hRsmooth)
  have heq : (fun y ↦ (D.symm (t (R y),R y)).1) = s := by
    funext y
    exact congrArg Prod.fst (hback y)
  rw [← heq]
  exact hcompsmooth.fst
end HolomorphicAnosov

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold

/-- Contracting invariant C¹ graphs are smooth on their whole fibres if they are smooth on a common
ball. -/
theorem contDiff_invariant_graph_of_contracting_smooth_discs
    {U V : ℕ → Type*}
    [∀ n, NormedAddCommGroup (U n)] [∀ n, NormedSpace ℝ (U n)]
    [∀ n, NormedAddCommGroup (V n)] [∀ n, NormedSpace ℝ (V n)]
    [∀ n, FiniteDimensional ℝ (V n)]
    (hdim : ∀ n, Module.finrank ℝ (V 0) = Module.finrank ℝ (V n))
    (D : ∀ n, Diffeomorph 𝓘(ℝ,U n × V n) 𝓘(ℝ,U (n+1) × V (n+1))
      (U n × V n) (U (n+1) × V (n+1)) ∞)
    (s : ∀ n, V n → U n) (hs : ContDiff ℝ 1 (s 0))
    (hgraph : ∀ n x, D n (s n x,x) =
      (s (n+1) (D n (s n x,x)).2,(D n (s n x,x)).2))
    (ρ q : ℝ) (hρ : 0 < ρ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ n x, ‖(D n (s n x,x)).2‖ ≤ q * ‖x‖)
    (hlocal : ∀ n, ContDiffOn ℝ ∞ (s n) (Metric.ball 0 ρ)) :
    ContDiff ℝ ∞ (s 0) := by
  let A : ∀ n, Diffeomorph 𝓘(ℝ,U 0 × V 0) 𝓘(ℝ,U n × V n)
      (U 0 × V 0) (U n × V n) ∞ :=
    fun n ↦ Nat.rec (Diffeomorph.refl 𝓘(ℝ,U 0 × V 0) (U 0 × V 0) ∞)
      (fun n A ↦ A.trans (D n)) n
  have hAgraph : ∀ n x, A n (s 0 x,x) =
      (s n (A n (s 0 x,x)).2,(A n (s 0 x,x)).2) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      have h := hgraph n (A n (s 0 x,x)).2
      rw [← ih x] at h
      exact h
  have hbound : ∀ n x, ‖(A n (s 0 x,x)).2‖ ≤ q^n * ‖x‖ := by
    intro n
    induction n with
    | zero => intro x; simp [A]
    | succ n ih =>
      intro x
      have h := hcontract n (A n (s 0 x,x)).2
      rw [← hAgraph n x] at h
      calc
        ‖(A (n+1) (s 0 x,x)).2‖ ≤ q * ‖(A n (s 0 x,x)).2‖ := h
        _ ≤ q * (q^n * ‖x‖) := mul_le_mul_of_nonneg_left (ih x) hq
        _ = q^(n+1) * ‖x‖ := by rw [pow_succ]; ring
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const ‖x‖
  simp only [zero_mul] at ht
  obtain ⟨n,hn⟩ := (Filter.Tendsto.eventually_lt_const hρ ht).exists
  apply contDiffAt_graph_of_smooth_image (hdim n) (A n) (s 0) hs (s n)
    (Metric.ball 0 ρ) Metric.isOpen_ball (hlocal n) (hAgraph n) x
  rw [Metric.mem_ball,dist_zero_right]
  exact (hbound n x).trans_lt hn
end HolomorphicAnosov


noncomputable section
open scoped ContDiff Manifold
open Set
namespace HolomorphicAnosov

/-- An ambient diffeomorphism carrying one smooth graph onto another induces a diffeomorphism
between their parameter spaces. (HPS, pp.61–63; Smale, Thm 4.1, pp.105–106) -/
theorem diffeomorph_of_graph_invariance
    {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E' × F') (E × F) (E' × F') ∞)
    (s : E → F) (t : E' → F') (hs : ContDiff ℝ ∞ s) (ht : ContDiff ℝ ∞ t)
    (hgraph : D '' range (fun x ↦ (x, s x)) = range (fun y ↦ (y, t y))) :
    ∃ R : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') E E' ∞,
      (∀ x, D (x, s x) = (R x, t (R x))) ∧
      (∀ y, D.symm (y, t y) = (R.symm y, s (R.symm y))) := by
  have hforward (x : E) : D (x, s x) = ((D (x, s x)).1, t (D (x, s x)).1) := by
    have hx : D (x, s x) ∈ range (fun y ↦ (y, t y)) := by
      rw [← hgraph]
      exact mem_image_of_mem D (mem_range_self x)
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
  have hbackward (y : E') : D.symm (y, t y) =
      ((D.symm (y, t y)).1, s (D.symm (y, t y)).1) := by
    have hy : (y, t y) ∈ D '' range (fun x ↦ (x, s x)) := by
      rw [hgraph]
      exact mem_range_self y
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hy
    rw [← hx, D.symm_apply_apply]
  let R : E ≃ E' :=
    { toFun := fun x ↦ (D (x, s x)).1
      invFun := fun y ↦ (D.symm (y, t y)).1
      left_inv := fun x ↦ by
        dsimp only
        rw [← hforward x, D.symm_apply_apply]
      right_inv := fun y ↦ by
        dsimp only
        rw [← hbackward y, D.apply_symm_apply] }
  refine ⟨{ toEquiv := R, contMDiff_toFun := ?_, contMDiff_invFun := ?_ },
    hforward, hbackward⟩
  · apply ContDiff.contMDiff
    exact ((contMDiff_iff_contDiff.mp D.contMDiff).comp (contDiff_id.prodMk hs)).fst
  · apply ContDiff.contMDiff
    exact ((contMDiff_iff_contDiff.mp D.symm.contMDiff).comp (contDiff_id.prodMk ht)).fst

/-- An ambient diffeomorphism whose preimage of a smooth vertical graph is another smooth vertical
graph induces a diffeomorphism between their parameter spaces. -/
theorem diffeomorph_of_vertical_graph_invariance
    {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E' × F') (E × F) (E' × F') ∞)
    (s : F → E) (t : F' → E') (hs : ContDiff ℝ ∞ s) (ht : ContDiff ℝ ∞ t)
    (hgraph : D ⁻¹' range (fun y ↦ (t y, y)) = range (fun x ↦ (s x, x))) :
    ∃ R : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F') F F' ∞,
      (∀ x, D (s x, x) = (t (R x), R x)) ∧
      (∀ y, D.symm (t y, y) = (s (R.symm y), R.symm y)) := by
  have himage : D '' range (fun x ↦ (s x, x)) = range (fun y ↦ (t y, y)) := by
    rw [← hgraph]
    exact Set.image_preimage_eq _ D.surjective
  have hforward (x : F) : D (s x, x) = (t (D (s x, x)).2, (D (s x, x)).2) := by
    have hx : D (s x, x) ∈ range (fun y ↦ (t y, y)) := by
      rw [← himage]
      exact mem_image_of_mem D (mem_range_self x)
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
  have hbackward (y : F') : D.symm (t y, y) =
      (s (D.symm (t y, y)).2, (D.symm (t y, y)).2) := by
    have hy : (t y, y) ∈ D '' range (fun x ↦ (s x, x)) := by
      rw [himage]
      exact mem_range_self y
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hy
    rw [← hx, D.symm_apply_apply]
  let R : F ≃ F' :=
    { toFun := fun x ↦ (D (s x, x)).2
      invFun := fun y ↦ (D.symm (t y, y)).2
      left_inv := fun x ↦ by
        dsimp only
        rw [← hforward x, D.symm_apply_apply]
      right_inv := fun y ↦ by
        dsimp only
        rw [← hbackward y, D.apply_symm_apply] }
  refine ⟨{ toEquiv := R, contMDiff_toFun := ?_, contMDiff_invFun := ?_ },
    hforward, hbackward⟩
  · apply ContDiff.contMDiff
    exact ((contMDiff_iff_contDiff.mp D.contMDiff).comp (hs.prodMk contDiff_id)).snd
  · apply ContDiff.contMDiff
    exact ((contMDiff_iff_contDiff.mp D.symm.contMDiff).comp (ht.prodMk contDiff_id)).snd

/-- A vertical graph return satisfies `‖R x‖ ≤ (k + ε) * ‖x‖` when its vertical linear part has norm
at most `k`, its remainder is `ε`-Lipschitz, and the source graph is 1-Lipschitz through zero. -/
theorem vertical_graph_return_contraction
    {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (D : E × F → E' × F') (T₁ : E →L[ℝ] E') (T₂ : F →L[ℝ] F')
    (k ε : NNReal) (hk : ‖T₂‖ ≤ k)
    (hR : LipschitzWith ε (fun z ↦ D z - (T₁ z.1, T₂ z.2)))
    (hzero : D 0 = 0)
    (s : F → E) (t : F' → E') (hszero : s 0 = 0) (hs : LipschitzWith 1 s)
    (R : F → F') (heq : ∀ x, D (s x, x) = (t (R x), R x)) :
    ∀ x, ‖R x‖ ≤ ((k : ℝ) + ε) * ‖x‖ := by
  intro x
  have hx : ‖s x‖ ≤ ‖x‖ := by
    simpa [hszero] using hs.norm_sub_le x 0
  have hb := parameter_graph_vertical_estimate T₁ T₂ D k ε hk hR (s x) 0 x 0
  simpa only [heq x, show (0, 0) = (0 : E × F) from rfl,
    hzero, Prod.snd_zero, sub_zero, max_eq_right hx, add_mul] using hb

end HolomorphicAnosov

namespace HolomorphicAnosov.HPS
open Set TopologicalSpace
open scoped ContDiff Manifold
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ,E) ∞ M]
variable {D₀ : RealTangentDistribution 𝓘(ℝ,E) M}
variable {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ,Fin (r i) → ℝ) ∞ (L i)]
variable {F : LeafPartition D₀ ι L r}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Invariant cutoff graphs with contracting returns, smoothness on a common disc, and compatible
plaques covering a native leaf give a global Euclidean model of that leaf. -/
theorem LaminationBoxes.euclidean_of_cutoff_graphs
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) (i : ι)
    {U V : ℕ → Type*}
    [∀ n, NormedAddCommGroup (U n)] [∀ n, NormedSpace ℝ (U n)]
    [∀ n, NormedAddCommGroup (V n)] [∀ n, NormedSpace ℝ (V n)]
    [∀ n, FiniteDimensional ℝ (V n)]
    (hdim : ∀ n, Module.finrank ℝ (V n) = r i)
    (D : ∀ n, Diffeomorph 𝓘(ℝ,U n × V n) 𝓘(ℝ,U (n+1) × V (n+1))
      (U n × V n) (U (n+1) × V (n+1)) ∞)
    (s : ∀ n, V n → U n) (hs : ∀ n, ContDiff ℝ 1 (s n))
    (hgraph : ∀ n, D n ⁻¹' Set.range (fun v ↦ (s (n+1) v,v)) =
      Set.range (fun v ↦ (s n v,v)))
    (ρ q : ℝ) (hρ : 0 < ρ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ n x, ‖(D n (s n x,x)).2‖ ≤ q * ‖x‖)
    (hlocal : ∀ n, ContDiffOn ℝ ∞ (s n) (Metric.ball 0 ρ))
    (a : ∀ n, (⟨Metric.ball (0 : V n) ρ,Metric.isOpen_ball⟩ : Opens (V n)) → M)
    (ha : ∀ n, ContMDiff 𝓘(ℝ,V n) 𝓘(ℝ,E) ∞ (a n))
    (hinj : ∀ n, Function.Injective (a n))
    (hder : ∀ n x, Function.Injective (mfderiv 𝓘(ℝ,V n) 𝓘(ℝ,E) (a n) x))
    (hmem : ∀ n, Set.range (a n) ⊆ Set.range (F.leaf i).inclusion)
    (hcover : ∀ y : L i, ∃ n, (F.leaf i).inclusion y ∈ Set.range (a n))
    (hcompat : ∀ n (x : Metric.ball (0 : V n) ρ)
      (hx : (D n (s n x,x)).2 ∈ Metric.ball (0 : V (n+1)) ρ),
      a (n+1) ⟨(D n (s n x,x)).2,hx⟩ = a n x) :
    Nonempty (Diffeomorph 𝓘(ℝ,Fin (r i) → ℝ) 𝓘(ℝ,Fin (r i) → ℝ)
      (Fin (r i) → ℝ) (L i) ∞) := by
  have hforward (n : ℕ) (x : V n) : D n (s n x,x) =
      (s (n+1) (D n (s n x,x)).2,(D n (s n x,x)).2) := by
    have hx : D n (s n x,x) ∈ Set.range (fun v ↦ (s (n+1) v,v)) := by
      change (s n x,x) ∈ (D n) ⁻¹' Set.range (fun v ↦ (s (n+1) v,v))
      rw [hgraph]
      exact Set.mem_range_self x
    obtain ⟨y,hy⟩ := hx
    rw [← hy]
  have hsmooth (n : ℕ) : ContDiff ℝ ∞ (s n) := by
    exact contDiff_invariant_graph_of_contracting_smooth_discs
      (U := fun k ↦ U (n+k)) (V := fun k ↦ V (n+k))
      (fun k ↦ (hdim n).trans (hdim (n+k)).symm)
      (fun k ↦ D (n+k)) (fun k ↦ s (n+k)) (hs n)
      (fun k ↦ hforward (n+k)) ρ q hρ hq hq1
      (fun k ↦ hcontract (n+k)) (fun k ↦ hlocal (n+k))
  have hreturn (n : ℕ) := diffeomorph_of_vertical_graph_invariance
    (D n) (s n) (s (n+1)) (hsmooth n) (hsmooth (n+1)) (hgraph n)
  choose R hR hRinv using hreturn
  have hRbound (n : ℕ) (x : V n) : ‖R n x‖ ≤ q * ‖x‖ := by
    have h := hcontract n x
    rwa [hR] at h
  obtain ⟨e⟩ := boxes.euclidean_of_contracting_parametrizations i hdim R ρ q hρ hq hq1
    hRbound a ha hinj hder hmem hcover (by
      intro n x hx
      have he : (D n (s n x,x)).2 = R n x := congrArg Prod.snd (hR n x)
      have h := hcompat n x (he.symm ▸ hx)
      simpa only [he] using h)
  let c : (Fin (r i) → ℝ) ≃L[ℝ] V 0 := ContinuousLinearEquiv.ofFinrankEq
    (by simpa using (hdim 0).symm)
  exact ⟨c.toDiffeomorph.trans e⟩
end HolomorphicAnosov.HPS

open scoped ContDiff Manifold Bundle Uniformity
open Set Topology Filter
set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov.HPS
open Set
open scoped ContDiff Manifold
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ,E) ∞ M]
variable {D : RealTangentDistribution 𝓘(ℝ,E) M}
variable {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ,Fin (r i) → ℝ) ∞ (L i)]
variable {F : LeafPartition D ι L r}

/-- A C¹ parametrization contained in a smooth native leaf of the same dimension is smooth if a
smooth local projection on the leaf recovers its parameter. -/
theorem LaminationBoxes.smooth_parametrization_of_projection
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) (i : ι)
    {G X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace X] [ChartedSpace G X] [IsManifold 𝓘(ℝ,G) ∞ X]
    (hdim : Module.finrank ℝ G = r i)
    (a : X → M) (ha : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) 1 a)
    (U : Set (L i)) (hU : IsOpen U)
    (b : L i → X) (hb : ContMDiffOn 𝓘(ℝ,Fin (r i) → ℝ) 𝓘(ℝ,G) ∞ b U)
    (hmem : ∀ x, ∃ y ∈ U, (F.leaf i).inclusion y = a x)
    (hleft : ∀ x y, (F.leaf i).inclusion y = a x → b y = x) :
    ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) ∞ a := by
  classical
  choose g hgU hcomm using hmem
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace G X
  have heq : (F.leaf i).inclusion ∘ g = a := funext hcomm
  have hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) 1 g := by
    apply (ContMDiff.iff_comp_isImmersion
      (immersion_at_lower_regularity (F.leaf i).immersion (show (1 : ℕ∞ω) ≤ ∞ by simp))).mpr
    refine ⟨boxes.continuous_of_inclusion_comp i g ?_,?_⟩
    · rw [heq]; exact ha.continuous
    · rw [heq]; exact ha
  have hs : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,Fin (r i) → ℝ) ∞ g := fun x ↦
    contMDiffAt_section_of_smoothOn_equal_dimension (by simpa using hdim)
      U hU b hb g hg x (hgU x) (fun y ↦ hleft y (g y) (hcomm y))
  rw [← heq]
  exact (F.leaf i).immersion.contMDiff.comp hs

/-- A C¹ parametrization contained in a smooth native leaf of the same dimension is smooth if a
smooth ambient projection recovers its parameter. -/
theorem LaminationBoxes.smooth_parametrization_of_ambient_projection
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) (i : ι)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (hdim : Module.finrank ℝ G = r i)
    (B : TopologicalSpace.Opens G) (x₀ : B)
    (a : B → M) (ha : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) 1 a)
    (W : Set M) (hW : IsOpen W)
    (projection : M → G) (hprojection : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ projection W)
    (hmem : Set.range a ⊆ Set.range (F.leaf i).inclusion)
    (hWmem : ∀ x, a x ∈ W) (hleft : ∀ x, projection (a x) = (x : G)) :
    ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) ∞ a := by
  classical
  let U₀ : Set (L i) := (F.leaf i).inclusion ⁻¹' W
  let b₀ : L i → G := projection ∘ (F.leaf i).inclusion
  have hb₀ : ContMDiffOn 𝓘(ℝ,Fin (r i) → ℝ) 𝓘(ℝ,G) ∞ b₀ U₀ :=
    hprojection.comp (F.leaf i).immersion.contMDiff.contMDiffOn (fun _ hy ↦ hy)
  have hU₀ : IsOpen U₀ := hW.preimage (F.leaf i).immersion.contMDiff.continuous
  let U : Set (L i) := U₀ ∩ b₀ ⁻¹' (B : Set G)
  have hU : IsOpen U := hb₀.continuousOn.isOpen_inter_preimage hU₀ B.isOpen
  let b : L i → B := fun y ↦ if hy : b₀ y ∈ B then ⟨b₀ y,hy⟩ else x₀
  have hb : ContMDiffOn 𝓘(ℝ,Fin (r i) → ℝ) 𝓘(ℝ,G) ∞ b U := by
    have heq : Set.EqOn (Subtype.val ∘ b) b₀ U := by
      intro y hy
      have hyB : b₀ y ∈ B := hy.2
      dsimp only [Function.comp_apply,b]
      rw [dite_eq_left hyB]
    have hh : ContMDiffOn 𝓘(ℝ,Fin (r i) → ℝ) 𝓘(ℝ,G) ∞ (Subtype.val ∘ b) U :=
      (hb₀.mono Set.inter_subset_left).congr heq
    intro y hy
    exact (ContMDiffWithinAt.subtypeVal_comp_iff B b U y).mp (hh y hy)
  apply boxes.smooth_parametrization_of_projection i hdim a ha U hU b hb
  · intro x
    obtain ⟨y,hy⟩ := hmem (Set.mem_range_self x)
    refine ⟨y,⟨?_,?_⟩,hy⟩
    · change (F.leaf i).inclusion y ∈ W
      rw [hy]
      exact hWmem x
    · change projection ((F.leaf i).inclusion y) ∈ B
      rw [hy,hleft]
      exact x.property
  · intro x y hy
    have heq : b₀ y = (x : G) := by dsimp only [b₀,Function.comp_def]; rw [hy,hleft]
    apply Subtype.ext
    simp only [b,dite_eq_left (heq.symm ▸ x.property)]
    exact heq

end HolomorphicAnosov.HPS





namespace HolomorphicAnosov.HPS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

set_option maxHeartbeats 400000 in
theorem native_stable_euclidean_from_anosov
    [FiniteDimensional ℝ E] (X : Type u) [EMetricSpace X] [CompactSpace X]
    [SecondCountableTopology X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
      (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsRiemannianManifold 𝓘(ℝ, E) X]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X X ∞)
    (S : InvariantRealTangentSplitting f) (h : BundleAnosovBounds f S)
    {κ : Type u} {L : κ → Type u} {k : ℕ}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin k → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ,Fin k → ℝ) ∞ (L i)]
    (F : LeafPartition S.stable.toDistribution κ L (fun _ ↦ k))
    {β : Type u} {dim : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β dim T)
    (identification : DistanceLeafIdentification F f edist) (i : κ) :
    Nonempty (Diffeomorph 𝓘(ℝ,Fin k → ℝ) 𝓘(ℝ,Fin k → ℝ) (Fin k → ℝ) (L i) ∞) := by
  obtain ⟨A, ⟨P⟩⟩ := local_strong_plaque_construction X f S h
  let ν := A.value
  let groupsU (p : X) := A.group S.unstable.toDistribution p
  let spacesU (p : X) := A.space S.unstable.toDistribution p
  let groupsS (p : X) := A.group S.stable.toDistribution p
  let spacesS (p : X) := A.space S.stable.toDistribution p
  let semiU (p : X) : SeminormedAddCommGroup (S.unstable.toDistribution p) :=
    (groupsU p).toSeminormedAddCommGroup
  let semiS (p : X) : SeminormedAddCommGroup (S.stable.toDistribution p) :=
    (groupsS p).toSeminormedAddCommGroup
  let metricS (p : X) : MetricSpace (S.stable.toDistribution p) :=
    (groupsS p).toMetricSpace
  let pseudoS (p : X) : PseudoMetricSpace (S.stable.toDistribution p) :=
    (groupsS p).toMetricSpace.toPseudoMetricSpace
  let distS (p : X) : Dist (S.stable.toDistribution p) :=
    (groupsS p).toMetricSpace.toDist
  let plaqueRadius := P.radius
  let stableGraph := P.graph
  let stablePlaque := P.plaque
  let cutoff := P.cutoff
  have hPlaqueRadius := P.radius_pos
  have hStableDiscOpen := P.disc_open
  have hStablePlaqueSmooth := P.plaque_smooth
  have hStablePlaqueC1 (p : X) := (P.plaque_smooth p).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hStablePlaqueInjective := P.plaque_injective
  have hStablePlaqueImmersion := P.plaque_immersion
  have hStableAsymptoticIff := P.asymptotic_iff
  have hStableAsymptotic (p : X) (y : S.stable.toDistribution p)
      (hy : ν p y.val < plaqueRadius) :
      Tendsto (fun n ↦ edist ((f : X → X)^[n] p)
        ((f : X → X)^[n] (stablePlaque p y))) atTop (𝓝 0) :=
    (P.asymptotic_iff p (stablePlaque p y)).mpr ⟨0, y, hy, rfl⟩
  have hPlaqueForward := P.plaque_forward
  have hCutoffContract (p : X) (y : S.stable.toDistribution p) :
      ‖(cutoff p (stableGraph p y,y)).2‖ ≤ P.rate * ‖y‖ := P.cutoff_contract p y
  have hGraphLocalSmooth (p : X) :
      ContDiffOn ℝ ∞ (stableGraph p) (Metric.ball 0 plaqueRadius) :=
    (P.graph_smooth p).contDiffOn
  have hRank (p : X) : Module.finrank ℝ (S.stable.toDistribution p) = k := by
    obtain ⟨j,z,hz⟩ := F.cover p
    have hr := LinearMap.finrank_range_of_inj ((F.leaf j).immersion.mfderiv_injective (by simp) z)
    rw [(F.leaf j).tangent,hz] at hr
    change Module.finrank ℝ (S.stable.toDistribution p) =
      Module.finrank ℝ (Fin k → ℝ) at hr
    simpa only [Module.finrank_fin_fun] using hr
  let := (F.leaf i).connected
  let a₀ : L i := Classical.choice inferInstance
  let p₀ := (F.leaf i).inclusion a₀
  let orbit : ℕ → X := Nat.rec p₀ (fun _ p ↦ f p)
  have hOrbit (n : ℕ) : orbit n = (f : X → X)^[n] p₀ := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg f ih |>.trans (Function.iterate_succ_apply' _ _ _).symm
  have hLabel : identification.label p₀ = i := by
    have hm : p₀ ∈ Set.range (F.leaf (identification.label p₀)).inclusion := by
      rw [identification.equality]
      simp only [Set.mem_ofPred_eq,edist_self]
      exact tendsto_const_nhds
    obtain ⟨z,hz⟩ := hm
    exact F.disjoint _ _ z a₀ hz
  let U (n : ℕ) : Type _ := S.unstable.toDistribution (orbit n)
  let V (n : ℕ) : Type _ := S.stable.toDistribution (orbit n)
  let ngU (n : ℕ) : NormedAddCommGroup (U n) := groupsU (orbit n)
  let nsU (n : ℕ) : NormedSpace ℝ (U n) := spacesU (orbit n)
  let ngV (n : ℕ) : NormedAddCommGroup (V n) := groupsS (orbit n)
  let nsV (n : ℕ) : NormedSpace ℝ (V n) := spacesS (orbit n)
  let tpU (n : ℕ) : TopologicalSpace (U n) := (ngU n).toUniformSpace.toTopologicalSpace
  let tpV (n : ℕ) : TopologicalSpace (V n) := (ngV n).toUniformSpace.toTopologicalSpace
  let pmV (n : ℕ) : PseudoMetricSpace (V n) := (ngV n).toMetricSpace.toPseudoMetricSpace
  let dsV (n : ℕ) : Dist (V n) := (ngV n).toMetricSpace.toDist
  let sgV (n : ℕ) : SeminormedAddCommGroup (V n) := (ngV n).toSeminormedAddCommGroup
  let cv (n : ℕ) : ChartedSpace (V n) (V n) := chartedSpaceSelf (V n)
  let imV (n : ℕ) : IsManifold 𝓘(ℝ,V n) ∞ (V n) := instIsManifoldModelSpace
  let B (n : ℕ) : TopologicalSpace.Opens (V n) :=
    ⟨Metric.ball 0 plaqueRadius,Metric.isOpen_ball⟩
  have hB (n : ℕ) (y : V n) : y ∈ B n ↔ ν (orbit n) y.val < plaqueRadius := by
    change dist y 0 < plaqueRadius ↔ _
    rw [dist_zero_right]
    rfl
  let iter (n : ℕ) := realIterate 𝓘(ℝ,E) f n
  let a (n : ℕ) (y : B n) : X := (iter n).symm (stablePlaque (orbit n) y)
  have ha (n : ℕ) : ContMDiff 𝓘(ℝ,V n) 𝓘(ℝ,E) ∞ (a n) := by
    apply (iter n).symm.contMDiff.comp
    intro y
    apply (contMDiffAt_subtype_iff (x := y)).mpr
    exact (hStablePlaqueSmooth (orbit n)).contMDiffAt
      ((hStableDiscOpen (orbit n)).mem_nhds ((hB n y).mp y.property))
  have hinj (n : ℕ) : Function.Injective (a n) := by
    intro y z he
    apply Subtype.ext
    exact hStablePlaqueInjective (orbit n) ((hB n y).mp y.property)
      ((hB n z).mp z.property) ((iter n).symm.injective he)
  have hder (n : ℕ) (y : B n) :
      Function.Injective (mfderiv 𝓘(ℝ,V n) 𝓘(ℝ,E) (a n) y) := by
    have hy := (hB n y).mp y.property
    have hp := (hStablePlaqueC1 (orbit n)).contMDiffAt
      ((hStableDiscOpen (orbit n)).mem_nhds hy)
    have hv := contMDiff_subtype_val (I := 𝓘(ℝ,V n)) (n := ∞) (U := B n)
    have hc : a n = (iter n).symm ∘ (stablePlaque (orbit n) ∘ Subtype.val) := rfl
    rw [hc,mfderiv_comp y ((iter n).symm.contMDiff.mdifferentiable (by simp) _)
      ((hp.comp y ((hv y).of_le (by simp))).mdifferentiableAt (by simp)),
      mfderiv_comp y (hp.mdifferentiableAt (by simp)) (hv.mdifferentiable (by simp) y)]
    exact ((iter n).symm.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      ((hStablePlaqueImmersion (orbit n) y hy).mfderiv_injective (by simp) |>.comp
        ((Manifold.IsImmersion.of_opens (M := V n) (I := 𝓘(ℝ,V n)) (n := ∞) (B n)).mfderiv_injective (by simp) y))
  have hAiterate (n : ℕ) (y : B n) :
      (f : X → X)^[n] (a n y) = stablePlaque (orbit n) y :=
    (iter n).apply_symm_apply _
  have hmem (n : ℕ) : Set.range (a n) ⊆ Set.range (F.leaf i).inclusion := by
    rintro q ⟨y,rfl⟩
    rw [← hLabel,identification.equality]
    change Tendsto (fun m : ℕ ↦ edist ((f : X → X)^[m] (a n y))
      ((f : X → X)^[m] p₀)) atTop (𝓝 0)
    have hh := hStableAsymptotic (orbit n) y ((hB n y).mp y.property)
    rw [← hAiterate] at hh
    rw [hOrbit] at hh
    have ht := (orbitAsymptotic_shift (f : X → X) p₀ (a n y) n).mp hh
    change Tendsto (fun m : ℕ ↦ edist ((f : X → X)^[m] p₀)
      ((f : X → X)^[m] (a n y))) atTop (𝓝 0) at ht
    simpa only [edist_comm] using ht
  have hcover (z : L i) : ∃ n, (F.leaf i).inclusion z ∈ Set.range (a n) := by
    have hz : (F.leaf i).inclusion z ∈ Set.range (F.leaf i).inclusion := Set.mem_range_self z
    have hr := identification.equality p₀
    rw [hLabel] at hr
    rw [hr] at hz
    change Tendsto (fun m : ℕ ↦ edist ((f : X → X)^[m] ((F.leaf i).inclusion z))
      ((f : X → X)^[m] p₀)) atTop (𝓝 0) at hz
    have ht : Tendsto (fun m : ℕ ↦ edist ((f : X → X)^[m] p₀)
        ((f : X → X)^[m] ((F.leaf i).inclusion z))) atTop (𝓝 0) := by
      simpa only [edist_comm] using hz
    obtain ⟨n,hn⟩ := (hStableAsymptoticIff p₀ ((F.leaf i).inclusion z)).mp ht
    have hn' : ∃ y : V n, ν (orbit n) y.val < plaqueRadius ∧
        stablePlaque (orbit n) y = (f : X → X)^[n] ((F.leaf i).inclusion z) := by
      change ∃ y : S.stable.toDistribution (orbit n), ν (orbit n) y.val < plaqueRadius ∧
        stablePlaque (orbit n) y = (f : X → X)^[n] ((F.leaf i).inclusion z)
      rw [hOrbit]
      exact hn
    obtain ⟨y,hy,he⟩ := hn'
    refine ⟨n,⟨y,(hB n y).mpr hy⟩,?_⟩
    apply (iter n).injective
    exact (hAiterate n _).trans he
  have hcompat (n : ℕ) (x : B n)
      (hx : (cutoff (orbit n) (stableGraph (orbit n) x,x)).2 ∈ B (n+1)) :
      a (n+1) ⟨(cutoff (orbit n) (stableGraph (orbit n) x,x)).2,hx⟩ = a n x := by
    apply (iter (n+1)).injective
    change (f : X → X)^[n+1] (a (n+1) _) = (f : X → X)^[n+1] (a n x)
    rw [hAiterate,Function.iterate_succ_apply',hAiterate]
    exact (hPlaqueForward (orbit n) x ((hB n x).mp x.property)).symm
  let fdT (p : X) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let fdV (n : ℕ) : FiniteDimensional ℝ (V n) :=
    @FiniteDimensional.finiteDimensional_submodule ℝ E _ _ _
      (inferInstance : FiniteDimensional ℝ E) (S.stable.toDistribution (orbit n))
  exact boxes.euclidean_of_cutoff_graphs i (U := U) (V := V)
    (fun n ↦ hRank (orbit n)) (fun n ↦ cutoff (orbit n))
    (fun n ↦ stableGraph (orbit n)) (fun n ↦ (P.graph_smooth (orbit n)).of_le (by simp))
    (fun n ↦ P.cutoff_graph (orbit n))
    plaqueRadius P.rate hPlaqueRadius P.rate_pos.le P.rate_lt_one
    (fun n ↦ hCutoffContract (orbit n)) (fun n ↦ hGraphLocalSmooth (orbit n))
    a ha hinj hder hmem hcover hcompat
end HolomorphicAnosov.HPS

namespace HolomorphicAnosov.HPS
open scoped ContDiff Manifold Bundle
open Filter
/-- A native stable leaf identified with a distance-asymptotic class on a compact manifold with
tensor Anosov bounds is diffeomorphic to its Euclidean model. -/
theorem native_stable_euclidean_tensor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [m : MetricSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] [CompactSpace M] [SecondCountableTopology M]
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) (S : InvariantRealTangentSplitting f)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    (h : Nonempty (TensorAnosovBounds f S g))
    {κ : Type u} {L : κ → Type u} {k : ℕ}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin k → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ,Fin k → ℝ) ∞ (L i)]
    (F : LeafPartition S.stable.toDistribution κ L (fun _ ↦ k))
    {β : Type u} {dim : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β dim T)
    (identification : DistanceLeafIdentification F f edist) (i : κ) :
    Nonempty (Diffeomorph 𝓘(ℝ,Fin k → ℝ) 𝓘(ℝ,Fin k → ℝ) (Fin k → ℝ) (L i) ∞) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := inferInstance
  have hcont : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := by
    change letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) :=
      ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
      IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)
    infer_instance
  let em := EMetricSpace.ofRiemannianMetric 𝓘(ℝ,E) M
  have hunif : em.toUniformSpace = m.toUniformSpace := unique_uniformity_of_compact rfl rfl
  have hzero (a b : ℕ → M) :
      Tendsto (fun n ↦ @edist M em.toEDist (a n) (b n)) atTop (nhds 0) ↔
      Tendsto (fun n ↦ @edist M m.toEDist (a n) (b n)) atTop (nhds 0) := by
    have h₁ := (@uniformity_basis_edist M em.toPseudoEMetricSpace).tendsto_right_iff
      (f := fun n ↦ (a n,b n)) (la := atTop)
    have h₂ := (@uniformity_basis_edist M m.toPseudoEMetricSpace).tendsto_right_iff
      (f := fun n ↦ (a n,b n)) (la := atTop)
    rw [ENNReal.nhds_zero_basis.tendsto_right_iff,ENNReal.nhds_zero_basis.tendsto_right_iff]
    simp only [Set.mem_ofPred_eq,Set.mem_Iio] at h₁ h₂ ⊢
    rw [← h₁,← h₂,hunif]
  let id' : DistanceLeafIdentification F f (@edist M em.toEDist) :=
    { label := identification.label
      equality := fun x ↦ by
        rw [identification.equality]
        ext y
        exact (hzero (fun n ↦ realIterate 𝓘(ℝ,E) f n y)
          (fun n ↦ realIterate 𝓘(ℝ,E) f n x)).symm }
  let : EMetricSpace M := em
  exact native_stable_euclidean_from_anosov M f S
    (tensorAnosovBounds_to_bundle f S g h) F boxes id' i
end HolomorphicAnosov.HPS
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold Bundle
namespace HolomorphicAnosov

variable {E F M L : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace L] [ChartedSpace F L] [IsManifold 𝓘(ℝ, F) ∞ L]

omit [IsManifold 𝓘(ℝ, F) ∞ L] in
/-- A tangent contraction bound on a distribution bounds the speed of the image of every piecewise
smooth path in an immersed leaf tangent to that distribution. -/
theorem immersed_path_image_speed_le
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ inc)
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (htan : ∀ z : L, (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) inc z).range ≤ D (inc z))
    (f : M → M) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) (θ : ℝ)
    (hθ : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
      Real.sqrt (h.inner (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)) ≤ θ * Real.sqrt (h.inner x v v))
    {a b : L} (p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, F) a b)
    (i : Fin (p.n+1)) {t : ℝ} (ht : t ∈ p.pieceInterval i) :
    ((p.map inc hinc).map f hf).speed h i t ≤ θ * (p.map inc hinc).speed h i t := by
  let c := p.map inc hinc
  have hunique := (uniqueDiffOn_Icc (p.time_strictMono Fin.castSucc_lt_succ)).uniqueMDiffOn t ht
  have hp := ((p.piece_smooth i).mdifferentiableOn (by simp)) t ht
  have hc := ((c.piece_smooth i).mdifferentiableOn (by simp)) t ht
  have hvelocity : c.velocity i t ∈ D (c.piece i t) := by
    change mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) (inc ∘ p.piece i)
      (p.pieceInterval i) t (show TangentSpace 𝓘(ℝ) t from (1 : ℝ)) ∈ D (inc (p.piece i t))
    erw [mfderiv_comp_mfderivWithin t (hinc.mdifferentiable (by simp) _) hp hunique]
    exact htan _ ⟨p.velocity i t, rfl⟩
  change Real.sqrt (h.inner _ ((c.map f hf).velocity i t) ((c.map f hf).velocity i t)) ≤ _
  have he : (c.map f hf).velocity i t =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (c.piece i t) (c.velocity i t) := by
    unfold RiemannianPiecewiseSmoothPath.velocity
    change mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) (f ∘ c.piece i) (p.pieceInterval i) t _ = _
    erw [mfderiv_comp_mfderivWithin t (hf.mdifferentiable (by simp) _) hc hunique]
    rfl
  rw [he]
  exact hθ _ _ hvelocity

omit [IsManifold 𝓘(ℝ, F) ∞ L] in
/-- A tangent contraction bound on a distribution bounds the length of the image of every piecewise
smooth path in an immersed leaf tangent to that distribution. (Lee, p.275; HPS, pp.111–114) -/
theorem immersed_path_image_length_le
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ inc)
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (htan : ∀ z : L, (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) inc z).range ≤ D (inc z))
    (f : M → M) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) (θ : ℝ)
    (hθ : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
      Real.sqrt (h.inner (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)) ≤ θ * Real.sqrt (h.inner x v v))
    {a b : L} (p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, F) a b) :
    ((p.map inc hinc).map f hf).length h ≤ θ * (p.map inc hinc).length h := by
  let c := p.map inc hinc
  let q := c.map f hf
  change (∑ i : Fin (p.n+1), ∫ t in p.time i.castSucc..p.time i.succ, q.speed h i t) ≤
    θ * ∑ i : Fin (p.n+1), ∫ t in p.time i.castSucc..p.time i.succ, c.speed h i t
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← intervalIntegral.integral_const_mul]
  have hle := p.time_strictMono.monotone (Fin.castSucc_le_succ i)
  apply intervalIntegral.integral_mono_on hle
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr (q.speed_integrableOn h i)
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr
      (c.speed_integrableOn h i)).const_mul θ
  · intro t ht
    exact immersed_path_image_speed_le inc hinc D htan f hf h θ hθ p i ht

omit [IsManifold 𝓘(ℝ, F) ∞ L] in
/-- Uniform exponential tangent contraction makes points joined by a piecewise smooth path in an
immersed leaf asymptotic for the tensor length distance. -/
theorem immersed_path_forward_asymptotic
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ inc)
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (htan : ∀ z : L, (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) inc z).range ≤ D (inc z))
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) (C rate : ℝ)
    (hrate : 0 ≤ rate ∧ rate < 1)
    (hbound : ∀ n x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
      Real.sqrt (h.inner (realIterate 𝓘(ℝ, E) f n x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f n) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f n) x v)) ≤
          C * rate^n * Real.sqrt (h.inner x v v))
    {a b : L} (p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, F) a b) :
    Filter.Tendsto (fun n : ℕ ↦ piecewiseSmoothRiemannianEDist h
      ((f : M → M)^[n] (inc a)) ((f : M → M)^[n] (inc b))) Filter.atTop (nhds 0) := by
  let c := p.map inc hinc
  have hdist (n : ℕ) : piecewiseSmoothRiemannianEDist h
      ((f : M → M)^[n] (inc a)) ((f : M → M)^[n] (inc b)) ≤
      ENNReal.ofReal (C * rate^n * c.length h) := by
    have hlen := immersed_path_image_length_le inc hinc D htan
      (realIterate 𝓘(ℝ, E) f n) (realIterate 𝓘(ℝ, E) f n).contMDiff
      h (C * rate^n) (hbound n) p
    exact (piecewiseSmoothRiemannianEDist_le_path h
      (c.map (realIterate 𝓘(ℝ, E) f n) (realIterate 𝓘(ℝ, E) f n).contMDiff)).trans
      (ENNReal.ofReal_le_ofReal hlen)
  have ht : Filter.Tendsto (fun n : ℕ ↦ C * rate^n * c.length h) Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hrate.1 hrate.2).const_mul C).mul_const
        (c.length h)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ bot_le) hdist
  simpa only [ENNReal.ofReal_zero, bot_eq_zero, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

/-- A connected smooth manifold immersed tangent to an exponentially contracted distribution lies in
one forward asymptotic class for the tensor length distance. -/
theorem immersed_connected_forward_asymptotic [PreconnectedSpace L]
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ inc)
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (htan : ∀ z : L, (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) inc z).range ≤ D (inc z))
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) (C rate : ℝ)
    (hrate : 0 ≤ rate ∧ rate < 1)
    (hbound : ∀ n x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
      Real.sqrt (h.inner (realIterate 𝓘(ℝ, E) f n x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f n) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f n) x v)) ≤
          C * rate^n * Real.sqrt (h.inner x v v))
    (a b : L) :
    Filter.Tendsto (fun n : ℕ ↦ piecewiseSmoothRiemannianEDist h
      ((f : M → M)^[n] (inc a)) ((f : M → M)^[n] (inc b))) Filter.atTop (nhds 0) := by
  obtain ⟨c, hc, hc0, hc1⟩ := connected_smooth_path_exists (E := F) a b
  let time : Fin 2 → ℝ := fun i ↦ (i : ℝ)
  let p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, F) a b :=
    { n := 0
      time := time
      time_strictMono := by
        intro i j hij
        simpa [time] using (show (i : ℝ) < (j : ℝ) by exact_mod_cast hij)
      time_zero := by simp [time]
      time_one := by simp [time]
      piece := fun _ ↦ c
      piece_smooth := fun i ↦ by fin_cases i; simpa [time] using hc.contMDiffOn
      source := by simpa using hc0
      target := by simpa using hc1
      junction := fun i ↦ Fin.elim0 i }
  exact immersed_path_forward_asymptotic inc hinc D htan f h C rate hrate hbound p


/-- On a compact manifold, convergence of tensor path distances to zero implies convergence of
distances to zero for any compatible metric, including for moving pairs. -/
theorem tensor_path_distance_zero_implies_edist_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [m : MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M]
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) (a b : ℕ → M)
    (hz : Filter.Tendsto (fun n ↦ piecewiseSmoothRiemannianEDist h (a n) (b n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ edist (a n) (b n)) Filter.atTop (nhds 0) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := inferInstance
  have hcont : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := by
    change letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
      IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
    infer_instance
  let em := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hunif : em.toUniformSpace = m.toUniformSpace :=
    unique_uniformity_of_compact rfl rfl
  have hsmall : Filter.Tendsto
      (fun n ↦ Manifold.riemannianEDist 𝓘(ℝ, E) (a n) (b n))
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun _ ↦ bot_le)
    exact fun n ↦ riemannianEDist_le_piecewiseSmoothRiemannianEDist h (a n) (b n)
  have h₁ := (@uniformity_basis_edist M em.toPseudoEMetricSpace).tendsto_right_iff
    (f := fun n ↦ (a n, b n)) (la := Filter.atTop)
  have h₂ := (@uniformity_basis_edist M m.toPseudoEMetricSpace).tendsto_right_iff
    (f := fun n ↦ (a n, b n)) (la := Filter.atTop)
  rw [ENNReal.nhds_zero_basis.tendsto_right_iff] at hsmall ⊢
  change (∀ ε, 0 < ε → ∀ᶠ n in Filter.atTop,
    @edist M em.toEDist (a n) (b n) < ε) at hsmall
  simp only [Set.mem_ofPred_eq, Set.mem_Iio] at h₁ h₂ hsmall ⊢
  apply h₂.mp
  change Filter.Tendsto _ _ (@UniformSpace.uniformity M m.toUniformSpace)
  rw [← hunif]
  exact h₁.mpr hsmall

/-- On a compact manifold, a connected smooth immersed leaf tangent to an exponentially contracted
distribution lies in one forward asymptotic class for the ambient metric. -/
theorem immersed_connected_metric_asymptotic
    {E F M L : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M]
    [TopologicalSpace L] [ChartedSpace F L] [IsManifold 𝓘(ℝ, F) ∞ L]
    [PreconnectedSpace L]
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ inc)
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (htan : ∀ z : L, (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) inc z).range ≤ D (inc z))
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) (C rate : ℝ)
    (hrate : 0 ≤ rate ∧ rate < 1)
    (hbound : ∀ n x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
      Real.sqrt (h.inner (realIterate 𝓘(ℝ, E) f n x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f n) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f n) x v)) ≤
          C * rate^n * Real.sqrt (h.inner x v v))
    (a b : L) :
    ForwardAsymptotic (f : M → M) (inc a) (inc b) := by
  have hpath := immersed_connected_forward_asymptotic inc hinc D htan f h C rate
    hrate hbound b a
  have hedist := tensor_path_distance_zero_implies_edist_zero h _ _ hpath
  have heq := ENNReal.tendsto_toReal_zero_iff (fi := Filter.atTop)
    (f := fun n : ℕ ↦ edist ((f : M → M)^[n] (inc b)) ((f : M → M)^[n] (inc a)))
  have hout := heq.mpr hedist
  simpa only [ForwardAsymptotic, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hout

end HolomorphicAnosov


namespace HolomorphicAnosov.HPS
open Set _root_.Topology
open scoped ContDiff Manifold Bundle
/-- A native partition tangent to an exponentially contracted distribution has leaves diffeomorphic,
preserving ambient points, to the corresponding distance-asymptotic lamination leaves. -/
theorem native_partition_diffeomorph_of_tangent_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M]
    (D : RealTangentDistribution 𝓘(ℝ,E) M)
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)) (C rate : ℝ)
    (hrate : 0 ≤ rate ∧ rate < 1)
    (hbound : ∀ n x (v : TangentSpace 𝓘(ℝ,E) x), v ∈ D x →
      Real.sqrt (h.inner (realIterate 𝓘(ℝ,E) f n x)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (realIterate 𝓘(ℝ,E) f n) x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (realIterate 𝓘(ℝ,E) f n) x v)) ≤
          C * rate^n * Real.sqrt (h.inner x v v))
    {ι κ : Type u} {L : ι → Type u} {K : κ → Type u} {r : ι → ℕ} {q : κ → ℕ}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ,Fin (r i) → ℝ) ∞ (L i)]
    [∀ k, TopologicalSpace (K k)] [∀ k, ChartedSpace (Fin (q k) → ℝ) (K k)]
    [∀ k, IsManifold 𝓘(ℝ,Fin (q k) → ℝ) ∞ (K k)]
    (F : LeafPartition D ι L r) (A : LeafPartition D κ K q)
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T)
    (identification : DistanceLeafIdentification F f edist) (k : κ) :
    ∃ i, ∃ e : Diffeomorph 𝓘(ℝ,Fin (q k) → ℝ) 𝓘(ℝ,Fin (r i) → ℝ) (K k) (L i) ∞,
      ∀ x, (F.leaf i).inclusion (e x) = (A.leaf k).inclusion x := by
  classical
  apply LeafPartition.diffeomorph_of_refines boxes A ?_ k
  intro j
  let := (A.leaf j).connected
  let a : K j := Classical.choice inferInstance
  refine ⟨identification.label ((A.leaf j).inclusion a),?_⟩
  rw [identification.equality]
  rintro y ⟨b,rfl⟩
  have hp := immersed_connected_forward_asymptotic (A.leaf j).inclusion
    (A.leaf j).immersion.contMDiff D (fun z ↦ le_of_eq ((A.leaf j).tangent z))
    f h C rate hrate hbound b a
  exact tensor_path_distance_zero_implies_edist_zero h _ _ hp

end HolomorphicAnosov.HPS

namespace HolomorphicAnosov.HPS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ,E) ∞ M]
variable {D : RealTangentDistribution 𝓘(ℝ,E) M}
variable {ι κ : Type u} {L : ι → Type u} {K : κ → Type u} {r : ι → ℕ} {q : κ → ℕ}
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ,Fin (r i) → ℝ) ∞ (L i)]
variable [∀ k, TopologicalSpace (K k)] [∀ k, ChartedSpace (Fin (q k) → ℝ) (K k)]
variable [∀ k, IsManifold 𝓘(ℝ,Fin (q k) → ℝ) ∞ (K k)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Diffeomorphisms preserving ambient points between corresponding leaves of two partitions induce
a bijection of leaf labels. -/
theorem LeafPartition.label_bijective_of_diffeomorph
    (A : LeafPartition D κ K q) (F : LeafPartition D ι L r)
    (σ : κ → ι)
    (e : ∀ k, Diffeomorph 𝓘(ℝ,Fin (q k) → ℝ) 𝓘(ℝ,Fin (r (σ k)) → ℝ) (K k) (L (σ k)) ∞)
    (he : ∀ k x, (F.leaf (σ k)).inclusion (e k x) = (A.leaf k).inclusion x) :
    Function.Bijective σ := by
  constructor
  · intro k l hkl
    let := (A.leaf k).connected
    obtain ⟨x⟩ := (inferInstance : Nonempty (K k))
    have h (j : ι) (h : σ k = j) (z : L j) :
        ∃ y : K k, (A.leaf k).inclusion y = (F.leaf j).inclusion z := by
      subst j
      exact ⟨(e k).symm z, (he k _).symm.trans
        (congrArg (F.leaf (σ k)).inclusion ((e k).apply_symm_apply z))⟩
    have h' : ∃ z : L (σ l), (F.leaf (σ l)).inclusion z = (A.leaf k).inclusion x := by
      rw [← hkl]
      exact ⟨e k x,he k x⟩
    obtain ⟨z,hz⟩ := h'
    exact A.disjoint k l x ((e l).symm z)
      (hz.symm.trans ((congrArg (F.leaf (σ l)).inclusion
        ((e l).apply_symm_apply z)).symm.trans (he l _)))
  · intro i
    let := (F.leaf i).connected
    obtain ⟨y⟩ := (inferInstance : Nonempty (L i))
    obtain ⟨k,x,hx⟩ := A.cover ((F.leaf i).inclusion y)
    exact ⟨k,F.disjoint _ _ (e k x) y ((he k x).trans hx)⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Dynamical invariance transfers between leaf partitions along diffeomorphisms preserving ambient
points. -/
theorem LeafDynamicalInvariance.of_leaf_diffeomorphs
    (A : LeafPartition D κ K q) (F : LeafPartition D ι L r)
    (σ : κ ≃ ι)
    (e : ∀ k, Diffeomorph 𝓘(ℝ,Fin (q k) → ℝ) 𝓘(ℝ,Fin (r (σ k)) → ℝ) (K k) (L (σ k)) ∞)
    (he : ∀ k x, (F.leaf (σ k)).inclusion (e k x) = (A.leaf k).inclusion x)
    {f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (inv : LeafDynamicalInvariance F f) : Nonempty (LeafDynamicalInvariance A f) := by
  let τ : κ ≃ κ := σ.trans (inv.permutation.trans σ.symm)
  have heq (k : κ) : inv.permutation (σ k) = σ (τ k) :=
    (σ.apply_symm_apply _).symm
  have hd (k : κ) (j : ι) (h : inv.permutation (σ k) = j) :
      ∃ d : Diffeomorph 𝓘(ℝ,Fin (r (σ k)) → ℝ) 𝓘(ℝ,Fin (r j) → ℝ)
          (L (σ k)) (L j) ∞,
        ∀ z, (F.leaf j).inclusion (d z) = f ((F.leaf (σ k)).inclusion z) := by
    subst j
    exact ⟨inv.transport (σ k),inv.intertwining (σ k)⟩
  choose t ht using fun k ↦ hd k (σ (τ k)) (heq k)
  refine ⟨{ permutation := τ
            transport := fun k ↦ ((e k).trans (t k)).trans (e (τ k)).symm
            intertwining := ?_ }⟩
  intro k x
  change (A.leaf (τ k)).inclusion ((e (τ k)).symm (t k (e k x))) = _
  rw [← he, (e (τ k)).apply_symm_apply, ht, he]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Native product boxes transfer between leaf partitions along diffeomorphisms preserving ambient
points. -/
theorem LaminationBoxes.of_leaf_diffeomorphs
    (A : LeafPartition D κ K q) (F : LeafPartition D ι L r)
    (σ : κ ≃ ι)
    (e : ∀ k, Diffeomorph 𝓘(ℝ,Fin (q k) → ℝ) 𝓘(ℝ,Fin (r (σ k)) → ℝ) (K k) (L (σ k)) ∞)
    (he : ∀ k x, (F.leaf (σ k)).inclusion (e k x) = (A.leaf k).inclusion x)
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (boxes : LaminationBoxes F β d T) : Nonempty (LaminationBoxes A β d T) := by
  have hback (k : κ) (j : ι) (h : σ k = j) :
      ∃ e' : Diffeomorph 𝓘(ℝ,Fin (q k) → ℝ) 𝓘(ℝ,Fin (r j) → ℝ) (K k) (L j) ∞,
        ∀ x, (F.leaf j).inclusion (e' x) = (A.leaf k).inclusion x := by
    subst j
    exact ⟨e k,he k⟩
  choose e' he' using fun j ↦ hback (σ.symm j) j (σ.apply_symm_apply j)
  let B (b : β) : NativeProductBox A (d b) (T b) :=
    { transverseRank := (boxes.boxes b).transverseRank
      transverseDisc := (boxes.boxes b).transverseDisc
      transverse_connected := (boxes.boxes b).transverse_connected
      transverse_chart := (boxes.boxes b).transverse_chart
      disc := (boxes.boxes b).disc
      disc_connected := (boxes.boxes b).disc_connected
      ambient := (boxes.boxes b).ambient
      box := (boxes.boxes b).box
      label := fun t ↦ σ.symm ((boxes.boxes b).label t)
      plaque := fun t ↦ ⟨e' ((boxes.boxes b).label t) ⁻¹'
        ((boxes.boxes b).plaque t : Set (L ((boxes.boxes b).label t))),
          ((boxes.boxes b).plaque t).isOpen.preimage (e' _).continuous⟩
      chart := fun t ↦ ((boxes.boxes b).chart t).trans
        (diffeomorphPreimageOpens (e' _) ((boxes.boxes b).plaque t)).symm
      factorization := by
        intro t v
        change ((boxes.boxes b).box (v,t)).val =
          (A.leaf (σ.symm ((boxes.boxes b).label t))).inclusion
            ((e' ((boxes.boxes b).label t)).symm ((boxes.boxes b).chart t v))
        rw [← he', (e' _).apply_symm_apply]
        exact (boxes.boxes b).factorization t v }
  have hcover : ∀ p : M, ∃ b, p ∈ (B b).ambient := boxes.cover
  exact ⟨{ boxes := B
           cover := hcover
           topology_generated := native_boxes_topology_generated A B hcover }⟩

/-- Finite C¹ native plaque families transfer between leaf partitions along diffeomorphisms
preserving ambient points. -/
theorem FiniteC1NativePlaqueFamily.of_leaf_diffeomorphs
    (A : LeafPartition D κ K q) (F : LeafPartition D ι L r)
    (σ : κ ≃ ι)
    (e : ∀ k, Diffeomorph 𝓘(ℝ,Fin (q k) → ℝ) 𝓘(ℝ,Fin (r (σ k)) → ℝ) (K k) (L (σ k)) ∞)
    (he : ∀ k x, (F.leaf (σ k)).inclusion (e k x) = (A.leaf k).inclusion x)
    {p : M} {d : ℕ} (family : FiniteC1NativePlaqueFamily F p d) :
    Nonempty (FiniteC1NativePlaqueFamily A p d) := by
  have hback (k : κ) (j : ι) (h : σ k = j) :
      ∃ e' : Diffeomorph 𝓘(ℝ,Fin (q k) → ℝ) 𝓘(ℝ,Fin (r j) → ℝ) (K k) (L j) ∞,
        ∀ x, (F.leaf j).inclusion (e' x) = (A.leaf k).inclusion x := by
    subst j
    exact ⟨e k,he k⟩
  choose e' he' using fun j ↦ hback (σ.symm j) j (σ.apply_symm_apply j)
  refine ⟨{
    family := family.family
    label := fun t ↦ σ.symm (family.label t)
    receivingPlaque := fun t ↦ ⟨e' (family.label t) ⁻¹'
      (family.receivingPlaque t : Set (L (family.label t))),
        (family.receivingPlaque t).isOpen.preimage (e' _).continuous⟩
    chart := fun t ↦ (family.chart t).trans
      (diffeomorphPreimageOpens (e' _) (family.receivingPlaque t)).symm
    factorization := ?_
    closedJet := family.closedJet
    closedJet_eval := family.closedJet_eval
    closedJet_continuous := family.closedJet_continuous
    compact_center_image := family.compact_center_image }⟩
  intro t v
  change (family.family.plaque t).param v =
    (A.leaf (σ.symm (family.label t))).inclusion
      ((e' (family.label t)).symm (family.chart t v))
  rw [← he', (e' _).apply_symm_apply]
  exact family.factorization t v

end HolomorphicAnosov.HPS


namespace HolomorphicAnosov.HPS
open Set _root_.Topology
open scoped ContDiff Manifold Bundle
/-- A partition tangent to an exponentially contracted distribution inherits dynamical invariance,
native boxes, and finite C¹ plaque families from its distance-asymptotic lamination. -/
theorem native_partition_outputs_of_tangent_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M]
    (D : RealTangentDistribution 𝓘(ℝ,E) M)
    (f g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)) (C rate : ℝ)
    (hrate : 0 ≤ rate ∧ rate < 1)
    (hbound : ∀ n x (v : TangentSpace 𝓘(ℝ,E) x), v ∈ D x →
      Real.sqrt (h.inner (realIterate 𝓘(ℝ,E) g n x)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (realIterate 𝓘(ℝ,E) g n) x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (realIterate 𝓘(ℝ,E) g n) x v)) ≤
          C * rate^n * Real.sqrt (h.inner x v v))
    {κ : Type u} {K : κ → Type u} {q : κ → ℕ}
    [∀ k, TopologicalSpace (K k)] [∀ k, ChartedSpace (Fin (q k) → ℝ) (K k)]
    [∀ k, IsManifold 𝓘(ℝ,Fin (q k) → ℝ) ∞ (K k)]
    (A : LeafPartition D κ K q)
    (source : HasNativeLamination D f
      (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent g edist)) :
    Nonempty (LeafDynamicalInvariance A f) ∧
      (∃ (β : Type u) (d : β → ℕ) (T : β → Type u) (topT : ∀ b, TopologicalSpace (T b)),
        letI := topT
        Nonempty (LaminationBoxes A β d T)) ∧
      Nonempty (SelectedFiniteC1NativePlaqueFamilies A) ∧
      Nonempty (DistanceLeafIdentification A g edist) := by
  classical
  obtain ⟨ι,L,r,top,charts,smooth,F,⟨β,d,T,topT,⟨boxes⟩⟩,⟨inv⟩,
    families,coherent,_,_,_,_,⟨identification,_⟩,_,_⟩ := source
  let := top
  let := charts
  let := smooth
  let := topT
  choose σ e he using fun k ↦ native_partition_diffeomorph_of_tangent_contraction
    D g h C rate hrate hbound F A boxes identification k
  let σ' : κ ≃ ι := Equiv.ofBijective σ (A.label_bijective_of_diffeomorph F σ e he)
  have invA := LeafDynamicalInvariance.of_leaf_diffeomorphs A F σ' e he inv
  have boxesA := LaminationBoxes.of_leaf_diffeomorphs A F σ' e he boxes
  have famA (p : M) : Nonempty (FiniteC1NativePlaqueFamily A p (families.dimension p)) :=
    FiniteC1NativePlaqueFamily.of_leaf_diffeomorphs A F σ' e he (families.family p)
  have hrange (k : κ) : Set.range (A.leaf k).inclusion = Set.range (F.leaf (σ' k)).inclusion := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨e k y,he k y⟩
    · rintro ⟨z,rfl⟩
      refine ⟨(e k).symm z,?_⟩
      exact (he k _).symm.trans (congrArg (F.leaf (σ k)).inclusion ((e k).apply_symm_apply z))
  refine ⟨invA,⟨β,d,T,topT,boxesA⟩,
    ⟨{dimension := families.dimension, family := fun p ↦ (famA p).some}⟩,
    ⟨{ label := fun p ↦ σ'.symm (identification.label p), equality := ?_ }⟩⟩
  intro p
  rw [hrange,σ'.apply_symm_apply,identification.equality]
end HolomorphicAnosov.HPS

/-! Global Euclidean models, connected local products, and compatible complex structures for the
stable and unstable leaves. (HPS, §§6B–7; Ghys, pp.588–589) -/

noncomputable section
open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov.HPS
/-- A native topological product restricts to connected Euclidean balls with intrinsically open leaf
slices and a continuous bracket exchanging the two coordinates. -/
theorem connected_native_product_restriction
    {s t : ℕ} {M : Type u} [TopologicalSpace M]
    {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    (incS : ∀ i, Ls i → M) (incU : ∀ i, Lu i → M)
    (Ds : Opens (Fin s → ℝ)) (Du : Opens (Fin t → ℝ))
    (O : Opens M) (e : (Ds × Du) ≃ₜ O) (p : O)
    (hs : ∀ w : Du, ∃ i : ιs, ∃ V : Opens (Ls i), ∃ c : Ds ≃ₜ V,
      ∀ z : Ds, (e (z,w)).val = incS i (c z))
    (hu : ∀ z : Ds, ∃ i : ιu, ∃ V : Opens (Lu i), ∃ c : Du ≃ₜ V,
      ∀ w : Du, (e (z,w)).val = incU i (c w)) :
    ∃ (As : Opens (Fin s → ℝ)) (Au : Opens (Fin t → ℝ)) (W : Opens M)
      (c : (As × Au) ≃ₜ W), p.val ∈ W ∧ IsConnected (As : Set (Fin s → ℝ)) ∧ IsConnected (Au : Set (Fin t → ℝ)) ∧
      (∀ w : Au, ∃ i : ιs, ∃ V : Opens (Ls i), ∃ h : As ≃ₜ V,
        ∀ z : As, (c (z,w)).val = incS i (h z)) ∧
      (∀ z : As, ∃ i : ιu, ∃ V : Opens (Lu i), ∃ h : Au ≃ₜ V,
        ∀ w : Au, (c (z,w)).val = incU i (h w)) ∧
      (∀ y z : W, ∃! w : W, (c.symm w).2 = (c.symm y).2 ∧ (c.symm w).1 = (c.symm z).1) ∧
      Continuous (fun yz : W × W ↦ c ((c.symm yz.2).1,(c.symm yz.1).2)) := by
  let z₀ := (e.symm p).1
  let w₀ := (e.symm p).2
  obtain ⟨rs,hrs,hsubS⟩ := Metric.isOpen_iff.mp Ds.isOpen z₀ z₀.property
  obtain ⟨ru,hru,hsubU⟩ := Metric.isOpen_iff.mp Du.isOpen w₀ w₀.property
  let As : Opens (Fin s → ℝ) := ⟨Metric.ball z₀.val rs,Metric.isOpen_ball⟩
  let Au : Opens (Fin t → ℝ) := ⟨Metric.ball w₀.val ru,Metric.isOpen_ball⟩
  let js : As → Ds := fun z ↦ ⟨z.val,hsubS z.property⟩
  let ju : Au → Du := fun w ↦ ⟨w.val,hsubU w.property⟩
  have hjs : IsOpenEmbedding js := IsOpenEmbedding.of_comp js
    Ds.isOpen.isOpenEmbedding_subtypeVal As.isOpen.isOpenEmbedding_subtypeVal
  have hju : IsOpenEmbedding ju := IsOpenEmbedding.of_comp ju
    Du.isOpen.isOpenEmbedding_subtypeVal Au.isOpen.isOpenEmbedding_subtypeVal
  let a : As × Au → M := fun zw ↦ (e (js zw.1,ju zw.2)).val
  have ha : IsOpenEmbedding a := O.isOpen.isOpenEmbedding_subtypeVal.comp
    (e.isOpenEmbedding.comp (hjs.prodMap hju))
  let W : Opens M := ⟨Set.range a,ha.isOpen_range⟩
  let c : (As × Au) ≃ₜ W := ha.isEmbedding.toHomeomorph
  refine ⟨As,Au,W,c,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨(⟨z₀.val,Metric.mem_ball_self hrs⟩,⟨w₀.val,Metric.mem_ball_self hru⟩),?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply p)
  · exact (convex_ball z₀.val rs).isConnected ⟨z₀.val,Metric.mem_ball_self hrs⟩
  · exact (convex_ball w₀.val ru).isConnected ⟨w₀.val,Metric.mem_ball_self hru⟩
  · intro w
    obtain ⟨i,V,b,hb⟩ := hs (ju w)
    let j : As → Ls i := fun z ↦ (b (js z)).val
    have hj : IsOpenEmbedding j := V.isOpen.isOpenEmbedding_subtypeVal.comp
      (b.isOpenEmbedding.comp hjs)
    exact ⟨i,⟨Set.range j,hj.isOpen_range⟩,hj.isEmbedding.toHomeomorph,fun z ↦ hb (js z)⟩
  · intro z
    obtain ⟨i,V,b,hb⟩ := hu (js z)
    let j : Au → Lu i := fun w ↦ (b (ju w)).val
    have hj : IsOpenEmbedding j := V.isOpen.isOpenEmbedding_subtypeVal.comp
      (b.isOpenEmbedding.comp hju)
    exact ⟨i,⟨Set.range j,hj.isOpen_range⟩,hj.isEmbedding.toHomeomorph,fun w ↦ hb (ju w)⟩
  · intro y z
    refine ⟨c ((c.symm z).1,(c.symm y).2),?_,?_⟩
    · simp only [c.symm_apply_apply,and_self]
    · intro w hw
      apply c.symm.injective
      rw [c.symm_apply_apply]
      exact Prod.ext hw.2 hw.1
  · exact c.continuous.comp
      ((continuous_fst.comp (c.symm.continuous.comp continuous_snd)).prodMk
        (continuous_snd.comp (c.symm.continuous.comp continuous_fst)))
end HolomorphicAnosov.HPS

namespace HolomorphicAnosov.HPS
open scoped ContDiff Manifold Bundle
open Set TopologicalSpace _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [CompactSpace M]
/-- Tensor Anosov bounds give connected local product boxes whose slices are homeomorphic to open
subsets of the intrinsic stable and unstable leaves. -/
theorem native_partition_connected_products
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (P : InvariantRealTangentSplitting f)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    (bounds : TensorAnosovBounds f P g)
    {s t : ℕ} {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin s → ℝ) (Ls i)] [∀ i, ChartedSpace (Fin t → ℝ) (Lu i)]
    [∀ i, IsManifold 𝓘(ℝ,Fin s → ℝ) ∞ (Ls i)]
    [∀ i, IsManifold 𝓘(ℝ,Fin t → ℝ) ∞ (Lu i)]
    (Fs : LeafPartition P.stable.toDistribution ιs Ls (fun _ ↦ s))
    (Fu : LeafPartition P.unstable.toDistribution ιu Lu (fun _ ↦ t))
    (dynS : LeafDynamicalInvariance Fs f) (dynU : LeafDynamicalInvariance Fu f) :
    ∀ p : M, ∃ (Ds : Opens (Fin s → ℝ)) (Du : Opens (Fin t → ℝ))
      (O : Opens M) (e : (Ds × Du) ≃ₜ O), p ∈ O ∧
      IsConnected (Ds : Set (Fin s → ℝ)) ∧ IsConnected (Du : Set (Fin t → ℝ)) ∧
      (∀ w : Du, ∃ i : ιs, ∃ V : Opens (Ls i), ∃ c : Ds ≃ₜ V,
        ∀ z : Ds, (e (z,w)).val = (Fs.leaf i).inclusion (c z)) ∧
      (∀ z : Ds, ∃ i : ιu, ∃ V : Opens (Lu i), ∃ c : Du ≃ₜ V,
        ∀ w : Du, (e (z,w)).val = (Fu.leaf i).inclusion (c w)) ∧
      (∀ y z : O, ∃! w : O, (e.symm w).2 = (e.symm y).2 ∧ (e.symm w).1 = (e.symm z).1) ∧
      Continuous (fun yz : O × O ↦ e ((e.symm yz.2).1,(e.symm yz.1).2)) := by
  have hs (x : M) (n : ℕ) (v : TangentSpace 𝓘(ℝ,E) x)
      (hv : v ∈ P.stable.toDistribution x) :
      hyperbolicRiemannianNorm g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((f : M → M)^[n]) x v) ≤
        max bounds.C 1 * bounds.lambda ^ n * hyperbolicRiemannianNorm g v := by
    exact (bounds.stable n x v hv).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg bounds.lambda_pos.le n))
      (Real.sqrt_nonneg _))
  have hu (x : M) (n : ℕ) (v : TangentSpace 𝓘(ℝ,E) x)
      (hv : v ∈ P.unstable.toDistribution x) :
      hyperbolicRiemannianNorm g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((f.symm : M → M)^[n]) x v) ≤
        max bounds.C 1 * bounds.lambda ^ n * hyperbolicRiemannianNorm g v := by
    exact (bounds.unstable n x v hv).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg bounds.lambda_pos.le n))
      (Real.sqrt_nonneg _))
  obtain ⟨m,β,γ,ε,hγ,hβ,hε,htop,⟨PS⟩,⟨PU⟩,bracket,hbc,hbi,products⟩ :=
    Ghys.selectedPartitionProducts f P g (max bounds.C 1) bounds.lambda
      (le_max_right _ _) bounds.lambda_pos bounds.lambda_lt_one hs hu Fs Fu dynS dynU
  let NS := nativeInvariantLeafSystemOfPartition P.stable.toDistribution f Fs dynS
  let NU := nativeInvariantLeafSystemInverse P.unstable.toDistribution f
    (nativeInvariantLeafSystemOfPartition P.unstable.toDistribution f Fu dynU)
  intro p
  obtain ⟨Ds,Du,O,e,hp,hslice,uslice⟩ := Ghys.adaptedProduct_real_box f
    P.stable.toDistribution P.unstable.toDistribution m NS NU hγ hε bracket hbi PS PU hβ
    htop p (Classical.choice (products p))
  apply connected_native_product_restriction (fun i ↦ (Fs.leaf i).inclusion)
    (fun i ↦ (Fu.leaf i).inclusion) Ds Du O e ⟨p,hp⟩
  · intro w
    obtain ⟨y,V,c,hc⟩ := hslice w
    exact ⟨Classical.choose (Fs.cover y),V,c,hc⟩
  · intro z
    obtain ⟨y,V,c,hc⟩ := uslice z
    exact ⟨Classical.choose (Fu.cover y),V,c,hc⟩
end HolomorphicAnosov.HPS
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- The identity maps between the original real leaf atlas and the realification of its compatible
complex atlas are smooth. -/
theorem NativeLeafComplexUpgrade.real_identity_smooth
    {r k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    {inc : L → M} (upgrade : NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    letI := upgrade.charts
    ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel k) ∞ (id : L → L) ∧
      ContMDiff (realModel k) 𝓘(ℝ, Fin r → ℝ) ∞ (id : L → L) := by
  let := upgrade.charts
  let := upgrade.complex_manifold
  constructor
  · rw [contMDiff_iff]
    refine ⟨continuous_id, ?_⟩
    intro x y
    simpa [extChartAt, realModel, Function.comp_def] using
      upgrade.real_to_complex (chartAt (Fin r → ℝ) x) (chart_mem_atlas _ _)
        (chartAt (ComplexModel k) y) (chart_mem_atlas _ _)
  · rw [contMDiff_iff]
    refine ⟨continuous_id, ?_⟩
    intro x y
    simpa [extChartAt, realModel, Function.comp_def] using
      upgrade.complex_to_real (chartAt (ComplexModel k) x) (chart_mem_atlas _ _)
        (chartAt (Fin r → ℝ) y) (chart_mem_atlas _ _)

/-- The complex derivative range of the upgraded leaf inclusion is the prescribed complex tangent
subspace. -/
theorem NativeLeafComplexUpgrade.derivative_range
    {r k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {inc : L → M} (upgrade : NativeLeafComplexUpgrade (d := d) (r := r) k inc)
    (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hS : ∀ z : L, ((S (inc z)).restrictScalars ℝ).map
      (complexTangentToReal d (inc z)).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z).range) :
    letI := upgrade.charts
    ∀ z : L, (mfderiv (complexModel k) (complexModel d) inc z).range = S (inc z) := by
  let := upgrade.charts
  let := upgrade.complex_manifold
  intro z
  have hid := upgrade.real_identity_smooth
  have hr := complexDerivative_range_of_compatible_real_charts (x := z)
    (hid.1.mdifferentiableAt (by simp)) (hid.2.mdifferentiableAt (by simp))
    (upgrade.inclusion_holomorphic.mdifferentiableAt (by simp))
    (hinc.mdifferentiableAt (by simp))
  apply Submodule.restrictScalars_injective ℝ
  apply Submodule.map_injective_of_injective (complexTangentToReal d (inc z)).injective
  exact hr.trans (hS z).symm


/-- The upgraded complex leaf inclusion is a global immersion with complement model of complex
dimension `d - k`. -/
theorem NativeLeafComplexUpgrade.global_immersion
    {r k d : ℕ} {L : Type u} {M : Type u}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    {inc : L → M} (upgrade : NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    letI := upgrade.charts
    Manifold.IsImmersion (complexModel k) (complexModel d) ∞ inc := by
  let := upgrade.charts
  refine ⟨ComplexModel (d-k), inferInstance, inferInstance, ?_⟩
  intro x
  let hx := upgrade.inclusion_immersion x
  let : FiniteDimensional ℂ (ComplexModel k × hx.complement) :=
    FiniteDimensional.of_injective hx.equiv.toLinearEquiv.toLinearMap hx.equiv.injective
  let : FiniteDimensional ℂ hx.complement :=
    FiniteDimensional.of_injective (LinearMap.inr ℂ (ComplexModel k) hx.complement)
      (by intro v w heq; exact congrArg Prod.snd heq)
  have he := hx.equiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at he
  have hdim : k + Module.finrank ℂ hx.complement = d := by
    simpa [ComplexModel] using he
  let e : hx.complement ≃L[ℂ] ComplexModel (d-k) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simpa [ComplexModel] using (show Module.finrank ℂ hx.complement = d-k by omega))
  exact hx.isImmersionAtOfComplement_complement.trans_F e

/-- The stable and unstable foliations have global Euclidean leaf models, connected local product
boxes, and compatible complex leaf atlases with holomorphic immersed inclusions. (HPS, §§6B–7,
pp.111–116, 127–129; Zhang, p.3, Lemma 2.5, p.8; Ghys, pp.588–590) -/
theorem stableFoliations_global_euclidean_paired_complex_completion
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M)
    (h : HermitianTangentMetricCore d M)
    (hh : IsSmoothHermitianTangentMetric h)
    (P : InvariantRealTangentSplitting f.toReal)
    (C rate : ℝ) (hC : 0 < C) (hrate : 0 < rate ∧ rate < 1)
    (hs : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.stable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v))
    (hu : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.unstable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f.symm : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v))
    {s t : ℕ} (_hst : s + t = d)
    {S U : ContinuousComplexTangentSubbundle (complexModel d) M}
    (hS : ∀ x, ((S.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.stable.toDistribution x)
    (hU : ∀ x, ((U.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.unstable.toDistribution x)
    {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin (2*s) → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin (2*t) → ℝ) (Lu i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (2*s) → ℝ) ∞ (Ls i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (2*t) → ℝ) ∞ (Lu i)]
    (Fs : HPS.LeafPartition P.stable.toDistribution ιs Ls (fun _ ↦ 2*s))
    (Fu : HPS.LeafPartition P.unstable.toDistribution ιu Lu (fun _ ↦ 2*t)) :
(∀ i, Nonempty (Diffeomorph 𝓘(ℝ, Fin (2*s) → ℝ)
  𝓘(ℝ, Fin (2*s) → ℝ) (Fin (2*s) → ℝ) (Ls i) ∞)) ∧
(∀ i, Nonempty (Diffeomorph 𝓘(ℝ, Fin (2*t) → ℝ)
  𝓘(ℝ, Fin (2*t) → ℝ) (Fin (2*t) → ℝ) (Lu i) ∞)) ∧
Nonempty (HPS.LeafDynamicalInvariance Fs f.toReal) ∧
Nonempty (HPS.LeafDynamicalInvariance Fu f.toReal) ∧
(∃ (βs βu : Type u) (Ts : βs → Type u) (Tu : βu → Type u)
  (tts : ∀ b, TopologicalSpace (Ts b)) (ttu : ∀ b, TopologicalSpace (Tu b)),
  letI := tts; letI := ttu
  Nonempty (HPS.LaminationBoxes Fs βs (fun _ ↦ 2*s) Ts) ∧
  Nonempty (HPS.LaminationBoxes Fu βu (fun _ ↦ 2*t) Tu)) ∧
(∀ p : M, ∃ (Ds : TopologicalSpace.Opens (Fin (2*s) → ℝ))
  (Du : TopologicalSpace.Opens (Fin (2*t) → ℝ))
  (O : TopologicalSpace.Opens M) (e : (Ds × Du) ≃ₜ O),
  p ∈ O ∧ IsConnected (Ds : Set (Fin (2*s) → ℝ)) ∧
  IsConnected (Du : Set (Fin (2*t) → ℝ)) ∧
  (∀ w : Du, ∃ (i : ιs) (V : TopologicalSpace.Opens (Ls i))
    (c : Ds ≃ₜ V),
    ∀ z : Ds, (e (z, w)).val = (Fs.leaf i).inclusion (c z)) ∧
  (∀ z : Ds, ∃ (i : ιu) (V : TopologicalSpace.Opens (Lu i))
    (c : Du ≃ₜ V),
    ∀ w : Du, (e (z, w)).val = (Fu.leaf i).inclusion (c w)) ∧
  (∀ y z : O, ∃! w : O,
    (e.symm w).2 = (e.symm y).2 ∧ (e.symm w).1 = (e.symm z).1) ∧
  Continuous (fun yz : O × O ↦
    e ((e.symm yz.2).1, (e.symm yz.1).2))) ∧
(∀ p : M, ∃ (V : Set M) (a : OpenPartialHomeomorph M (ComplexModel d))
  (r : ℝ) (q : M → (Fin (2*s) → ℝ) → M),
  IsOpen V ∧ p ∈ V ∧ V ⊆ a.source ∧
  a ∈ IsManifold.maximalAtlas (complexModel d) ∞ M ∧ 0 < r ∧
  (∀ x ∈ V, q x 0 = x) ∧
  (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin (2*s) → ℝ) r, q x v ∈ a.source) ∧
  (∀ x ∈ V, ContMDiffOn 𝓘(ℝ, Fin (2*s) → ℝ) (realModel d) ∞
    (q x) (Metric.ball 0 r)) ∧
  (∀ x ∈ V, IsEmbedding (fun v : ↥(Metric.ball (0 : Fin (2*s) → ℝ) r) ↦ q x v)) ∧
  (∀ x ∈ V, ∃ (i : ιs) (c : OpenPartialHomeomorph (Ls i) (Fin (2*s) → ℝ)),
    c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (2*s) → ℝ) ∞ (Ls i) ∧
    Metric.ball (0 : Fin (2*s) → ℝ) r ⊆ c.target ∧
    ∀ v ∈ Metric.ball (0 : Fin (2*s) → ℝ) r,
      q x v = (Fs.leaf i).inclusion (c.symm v)) ∧
  (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin (2*s) → ℝ) r,
    HasFDerivAt (fun w ↦ a (q x w))
      (fderiv ℝ (fun w ↦ a (q x w)) v) v) ∧
  ContinuousOn (fun xv : M × (Fin (2*s) → ℝ) ↦ a (q xv.1 xv.2))
    (V ×ˢ Metric.ball 0 r) ∧
  ContinuousOn (fun xv : M × (Fin (2*s) → ℝ) ↦
    fderiv ℝ (fun v ↦ a (q xv.1 v)) xv.2) (V ×ˢ Metric.ball 0 r)) ∧
(∀ p : M, ∃ (V : Set M) (a : OpenPartialHomeomorph M (ComplexModel d))
  (r : ℝ) (q : M → (Fin (2*t) → ℝ) → M),
  IsOpen V ∧ p ∈ V ∧ V ⊆ a.source ∧
  a ∈ IsManifold.maximalAtlas (complexModel d) ∞ M ∧ 0 < r ∧
  (∀ x ∈ V, q x 0 = x) ∧
  (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin (2*t) → ℝ) r, q x v ∈ a.source) ∧
  (∀ x ∈ V, ContMDiffOn 𝓘(ℝ, Fin (2*t) → ℝ) (realModel d) ∞
    (q x) (Metric.ball 0 r)) ∧
  (∀ x ∈ V, IsEmbedding (fun v : ↥(Metric.ball (0 : Fin (2*t) → ℝ) r) ↦ q x v)) ∧
  (∀ x ∈ V, ∃ (i : ιu) (c : OpenPartialHomeomorph (Lu i) (Fin (2*t) → ℝ)),
    c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (2*t) → ℝ) ∞ (Lu i) ∧
    Metric.ball (0 : Fin (2*t) → ℝ) r ⊆ c.target ∧
    ∀ v ∈ Metric.ball (0 : Fin (2*t) → ℝ) r,
      q x v = (Fu.leaf i).inclusion (c.symm v)) ∧
  (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin (2*t) → ℝ) r,
    HasFDerivAt (fun w ↦ a (q x w))
      (fderiv ℝ (fun w ↦ a (q x w)) v) v) ∧
  ContinuousOn (fun xv : M × (Fin (2*t) → ℝ) ↦ a (q xv.1 xv.2))
    (V ×ˢ Metric.ball 0 r) ∧
  ContinuousOn (fun xv : M × (Fin (2*t) → ℝ) ↦
    fderiv ℝ (fun v ↦ a (q xv.1 v)) xv.2) (V ×ˢ Metric.ball 0 r)) ∧
(∀ i, ∃ c : ChartedSpace (ComplexModel s) (Ls i),
  letI := c
  IsManifold (complexModel s) ∞ (Ls i) ∧
  Manifold.IsImmersion (complexModel s) (complexModel d) ∞ (Fs.leaf i).inclusion ∧
  ∃ upgrade : NativeLeafComplexUpgrade (d := d) (r := 2*s) s
      (Fs.leaf i).inclusion,
    upgrade.charts = c ∧
    ∀ z : Ls i, (mfderiv (complexModel s) (complexModel d)
      (Fs.leaf i).inclusion z).range = S.toDistribution ((Fs.leaf i).inclusion z)) ∧
(∀ i, ∃ c : ChartedSpace (ComplexModel t) (Lu i),
  letI := c
  IsManifold (complexModel t) ∞ (Lu i) ∧
  Manifold.IsImmersion (complexModel t) (complexModel d) ∞ (Fu.leaf i).inclusion ∧
  ∃ upgrade : NativeLeafComplexUpgrade (d := d) (r := 2*t) t
      (Fu.leaf i).inclusion,
    upgrade.charts = c ∧
    ∀ z : Lu i, (mfderiv (complexModel t) (complexModel d)
      (Fu.leaf i).inclusion z).range = U.toDistribution ((Fu.leaf i).inclusion z)) := by
  have hnative := HPS.anosov_global_lamination_tensor_metric f.toReal P
    (StableFoliationsSupport.originalSmoothRealMetric h hh)
    (StableFoliationsSupport.tensor_bounds_of_exact_pairing f h hh P C rate hC hrate hs hu
      (StableFoliationsSupport.originalSmoothRealMetric h hh)
      (StableFoliationsSupport.originalSmoothRealMetric_inner h hh))
  have hs' : ∀ n x (v : TangentSpace (realModel d) x), v ∈ P.stable.toDistribution x →
      Real.sqrt ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner
        (realIterate (realModel d) f.toReal n x)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)) ≤
        C * rate^n * Real.sqrt ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner x v v) := by
    intro n x v hv
    simp only [StableFoliationsSupport.originalSmoothRealMetric_inner]
    convert hs n x v hv using 1
    rfl
  have hu' : ∀ n x (v : TangentSpace (realModel d) x), v ∈ P.unstable.toDistribution x →
      Real.sqrt ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner
        (realIterate (realModel d) f.toReal.symm n x)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal.symm n) x v)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal.symm n) x v)) ≤
        C * rate^n * Real.sqrt ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner x v v) := by
    intro n x v hv
    simp only [StableFoliationsSupport.originalSmoothRealMetric_inner]
    convert hu n x v hv using 1
    rfl
  obtain ⟨hinvS,hboxesS,⟨familiesS⟩,⟨idS⟩⟩ := HPS.native_partition_outputs_of_tangent_contraction
    P.stable.toDistribution f.toReal f.toReal
    (StableFoliationsSupport.originalSmoothRealMetric h hh) C rate ⟨hrate.1.le,hrate.2⟩ hs' Fs hnative.1
  obtain ⟨hinvU,hboxesU,⟨familiesU⟩,⟨idU⟩⟩ := HPS.native_partition_outputs_of_tangent_contraction
    P.unstable.toDistribution f.toReal f.toReal.symm
    (StableFoliationsSupport.originalSmoothRealMetric h hh) C rate ⟨hrate.1.le,hrate.2⟩ hu' Fu hnative.2
  have complexS : ∀ i, Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2*s) s
      (Fs.leaf i).inclusion) := by
    intro i
    apply nativeLeafComplexUpgrade_of_complex_tangent (Fs.leaf i).inclusion
      (P := P.stable) (S := S) (Fs.leaf i).immersion
      (fun z ↦ (Fs.leaf i).tangent z)
    intro z
    exact (hS _).trans ((Fs.leaf i).tangent z).symm
  have complexU : ∀ i, Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2*t) t
      (Fu.leaf i).inclusion) := by
    intro i
    apply nativeLeafComplexUpgrade_of_complex_tangent (Fu.leaf i).inclusion
      (P := P.unstable) (S := U) (Fu.leaf i).immersion
      (fun z ↦ (Fu.leaf i).tangent z)
    intro z
    exact (hU _).trans ((Fu.leaf i).tangent z).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    intro i
    obtain ⟨β,dim,T,topT,⟨boxes⟩⟩ := hboxesS
    let := topT
    exact HPS.native_stable_euclidean_tensor f.toReal P
      (StableFoliationsSupport.originalSmoothRealMetric h hh)
      (StableFoliationsSupport.tensor_bounds_of_exact_pairing f h hh P C rate hC hrate hs hu
        (StableFoliationsSupport.originalSmoothRealMetric h hh)
        (StableFoliationsSupport.originalSmoothRealMetric_inner h hh)) Fs boxes idS i
  case refine_2 =>
    intro i
    obtain ⟨β,dim,T,topT,⟨boxes⟩⟩ := hboxesU
    let := topT
    let Pinv := TheoremAProof.inverseSplitting f.toReal P
    have hb : Nonempty (TensorAnosovBounds f.toReal.symm Pinv
        (StableFoliationsSupport.originalSmoothRealMetric h hh)) := by
      refine ⟨⟨C,rate,hC,hrate.1,hrate.2,hu',?_⟩⟩
      exact hs'
    exact HPS.native_stable_euclidean_tensor f.toReal.symm Pinv
      (StableFoliationsSupport.originalSmoothRealMetric h hh) hb Fu boxes idU i
  case refine_3 => exact hinvS
  case refine_4 => exact hinvU
  case refine_5 =>
    obtain ⟨βs,ds,Ts,topTs,⟨Bs⟩⟩ := hboxesS
    let := topTs
    have hds : ds = (fun _ ↦ 2*s) := funext (fun b ↦ (Bs.boxes b).dimension_eq)
    cases hds
    obtain ⟨βu,du,Tu,topTu,⟨Bu⟩⟩ := hboxesU
    let := topTu
    have hdu : du = (fun _ ↦ 2*t) := funext (fun b ↦ (Bu.boxes b).dimension_eq)
    cases hdu
    exact ⟨βs,βu,Ts,Tu,topTs,topTu,⟨Bs⟩,⟨Bu⟩⟩
  case refine_7 => exact fun p ↦ (familiesS.family p).coordinate_export
  case refine_8 => exact fun p ↦ (familiesU.family p).coordinate_export
  case refine_9 =>
    intro i
    obtain ⟨upgrade⟩ := complexS i
    refine ⟨upgrade.charts, upgrade.complex_manifold, upgrade.global_immersion,
      upgrade, rfl, ?_⟩
    apply upgrade.derivative_range (Fs.leaf i).immersion.contMDiff S.toDistribution
    intro z
    exact (hS _).trans ((Fs.leaf i).tangent z).symm
  case refine_10 =>
    intro i
    obtain ⟨upgrade⟩ := complexU i
    refine ⟨upgrade.charts, upgrade.complex_manifold, upgrade.global_immersion,
      upgrade, rfl, ?_⟩
    apply upgrade.derivative_range (Fu.leaf i).immersion.contMDiff U.toDistribution
    intro z
    exact (hU _).trans ((Fu.leaf i).tangent z).symm
  case refine_6 =>
    exact HPS.native_partition_connected_products f.toReal P
      (StableFoliationsSupport.originalSmoothRealMetric h hh)
      ⟨C,rate,hC,hrate.1,hrate.2,hs',hu'⟩ Fs Fu hinvS.some hinvU.some

end HolomorphicAnosov
