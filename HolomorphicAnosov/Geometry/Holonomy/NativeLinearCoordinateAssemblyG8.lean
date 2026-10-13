import HolomorphicAnosov.Paper.Zhang.LinearUnstableHolonomy
import HolomorphicAnosov.Topology.Holonomy.UnitDiskEmbedding
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! # Native leaf coordinate assembly (HPS) (Zhang, Lemma 2.8) -/
noncomputable section
open scoped ContDiff Manifold _root_.Topology
open Set Filter _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
/-- A unit coordinate disk can be embedded through a prescribed point inside an open subset of an existing coordinate domain. (HPS) -/
private theorem unit_disk_embedding_in_open_subset {r : ℕ}
    (D : TopologicalSpace.Opens (Fin r → ℝ)) (W : Set D) (hW : IsOpen W)
    (x : D) (hx : x ∈ W) :
    ∃ j : FoliationCoordinateDisk r → D, IsOpenEmbedding j ∧
      x ∈ range j ∧ ∀ z, j z ∈ W := by
  let D' : TopologicalSpace.Opens (Fin r → ℝ) :=
    ⟨Subtype.val '' W, D.isOpen.isOpenMap_subtype_val _ hW⟩
  obtain ⟨j,hj,z,hz⟩ := unit_disk_embedding_in_domain D' ⟨x.val,⟨x,hx,rfl⟩⟩
  have hp : ∀ z, (j z).val ∈ D := by
    intro z
    obtain ⟨y,_,hy⟩ := (j z).property
    exact hy ▸ y.property
  let k : FoliationCoordinateDisk r → D := fun z ↦ ⟨(j z).val,hp z⟩
  have hk : IsOpenEmbedding k := D.isOpen.isOpenEmbedding_subtypeVal.of_comp k
    (D'.isOpen.isOpenEmbedding_subtypeVal.comp hj)
  refine ⟨k,hk,⟨z,Subtype.ext (congrArg (fun y : D' ↦ y.val) hz)⟩,?_⟩
  intro v
  obtain ⟨y,hy,he⟩ := (j v).property
  have hh : k v = y := Subtype.ext he.symm
  exact hh ▸ hy

/-- The fixed-unit product box can be chosen inside any given ambient neighborhood of its original center. (HPS) -/
theorem fixed_unit_product_box_within {s t : ℕ} {M : Type u} [TopologicalSpace M]
    (Ds : TopologicalSpace.Opens (Fin s → ℝ))
    (Du : TopologicalSpace.Opens (Fin t → ℝ)) (O : TopologicalSpace.Opens M)
    (e : (Ds × Du) ≃ₜ O) (p : O) (W : Set M) (hW : IsOpen W) (hp : p.val ∈ W) :
    ∃ js : FoliationCoordinateDisk s → Ds, ∃ ju : FoliationCoordinateDisk t → Du,
      IsOpenEmbedding js ∧ IsOpenEmbedding ju ∧
      ∃ B : TransverseFoliationBox s t M, p.val ∈ B.image ∧ B.image ⊆ W ∧
        ∀ zw, (B.chart zw).val = (e (js zw.1, ju zw.2)).val := by
  have hopen : IsOpen ((fun z : Ds × Du ↦ (e z).val) ⁻¹' W) :=
    hW.preimage (continuous_subtype_val.comp e.continuous)
  obtain ⟨Us,Uu,hUs,hUu,hs,hu,hsub⟩ := isOpen_prod_iff.mp hopen
    (e.symm p).1 (e.symm p).2 (by simpa using hp)
  obtain ⟨js,hjs,⟨zs,hzs⟩,hjsU⟩ := unit_disk_embedding_in_open_subset Ds Us hUs (e.symm p).1 hs
  obtain ⟨ju,hju,⟨zu,hzu⟩,hjuU⟩ := unit_disk_embedding_in_open_subset Du Uu hUu (e.symm p).2 hu
  let v : FoliationCoordinateDisk s × FoliationCoordinateDisk t → M :=
    fun zw ↦ (e (js zw.1,ju zw.2)).val
  have hv : IsOpenEmbedding v :=
    O.isOpen.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp (hjs.prodMap hju))
  let B : TransverseFoliationBox s t M :=
    { image := range v, isOpen_image := hv.isOpen_range, chart := hv.isEmbedding.toHomeomorph }
  refine ⟨js,ju,hjs,hju,B,?_,?_,fun _ ↦ rfl⟩
  · refine ⟨(zs,zu),?_⟩
    change (e (js zs,ju zu)).val = p.val
    rw [hzs,hzu,Prod.mk.eta,e.apply_symm_apply]
  · rintro _ ⟨⟨z,w⟩,rfl⟩
    exact hsub ⟨hjsU z,hjuU w⟩



/-- A point-preserving intrinsic homeomorphism between holomorphically immersed leaves is biholomorphic in their given complex atlases. (Ghys) -/
theorem biholomorph_of_immersed_homeomorph
    {k l d : ℕ} {L L' M : Type*}
    [TopologicalSpace L] [TopologicalSpace L'] [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) L] [ChartedSpace (ComplexModel l) L']
    [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel k) ∞ L] [IsManifold (complexModel l) ∞ L']
    (inc : L → M) (inc' : L' → M)
    (hi : ContMDiff (complexModel k) (complexModel d) ∞ inc)
    (hi' : ContMDiff (complexModel l) (complexModel d) ∞ inc')
    (him : ∀ z, Manifold.IsImmersionAt (complexModel k) (complexModel d) ∞ inc z)
    (him' : ∀ z, Manifold.IsImmersionAt (complexModel l) (complexModel d) ∞ inc' z)
    (e : L ≃ₜ L') (he : ∀ z, inc' (e z) = inc z) :
    ∃ E : Biholomorph k l L L', E.toHomeomorph = e := by
  have hf : inc' ∘ e = inc := funext he
  have hb : inc ∘ e.symm = inc' := by
    funext z
    exact (he (e.symm z)).symm.trans (congrArg inc' (e.apply_symm_apply z))
  have hs : ContMDiff (complexModel k) (complexModel l) ∞ e := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt (him' (e z))).mpr
    refine ⟨e.continuous.continuousAt,?_⟩
    rw [hf]
    exact hi z
  have ht : ContMDiff (complexModel l) (complexModel k) ∞ e.symm := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt (him (e.symm z))).mpr
    refine ⟨e.symm.continuous.continuousAt,?_⟩
    rw [hb]
    exact hi' z
  exact ⟨{ toEquiv := e.toEquiv, contMDiff_toFun := hs, contMDiff_invFun := ht },rfl⟩



/-- A homeomorphism between compact metric spaces preserves asymptotic pairs of sequences. (Zhang) -/
theorem paired_distance_zero_iff_of_homeomorph
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    (e : X ≃ₜ Y) (a b : ℕ → X) :
    Tendsto (fun n ↦ dist (a n) (b n)) atTop (𝓝 0) ↔
      Tendsto (fun n ↦ dist (e (a n)) (e (b n))) atTop (𝓝 0) := by
  constructor
  · intro h
    have hu : Tendsto (fun p : X × X ↦ (e p.1,e p.2)) (uniformity X) (uniformity Y) :=
      CompactSpace.uniformContinuous_of_continuous e.continuous
    have hs : Tendsto (fun n ↦ (a n,b n)) atTop (uniformity X) :=
      tendsto_uniformity_iff_dist_tendsto_zero.mpr h
    exact tendsto_uniformity_iff_dist_tendsto_zero.mp (hu.comp hs)
  · intro h
    have hu : Tendsto (fun p : Y × Y ↦ (e.symm p.1,e.symm p.2)) (uniformity Y) (uniformity X) :=
      CompactSpace.uniformContinuous_of_continuous e.symm.continuous
    have hs : Tendsto (fun n ↦ (e (a n),e (b n))) atTop (uniformity Y) :=
      tendsto_uniformity_iff_dist_tendsto_zero.mpr h
    have ht := tendsto_uniformity_iff_dist_tendsto_zero.mp (hu.comp hs)
    simpa only [Function.comp_apply, e.symm_apply_apply] using ht

/-- The ambient-neighborhood-restricted fixed-unit box retains the native open plaques of its given source paired chart. (HPS) -/
theorem fixed_unit_product_box_native_plaques_within {s t : ℕ}
    {M : Type u} [TopologicalSpace M] {ιs ιu : Type u}
    {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin s → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin t → ℝ) (Lu i)]
    (is : ∀ i, Ls i → M) (iu : ∀ i, Lu i → M)
    (Ds : TopologicalSpace.Opens (Fin s → ℝ))
    (Du : TopologicalSpace.Opens (Fin t → ℝ)) (O : TopologicalSpace.Opens M)
    (e : (Ds × Du) ≃ₜ O) (p : O) (W : Set M) (hW : IsOpen W) (hpW : p.val ∈ W)
    (hs : ∀ w : Du, ∃ i : ιs, ∃ V : TopologicalSpace.Opens (Ls i),
      ∃ c : Ds ≃ₜ V,
        ∀ z : Ds, (e (z, w)).val = is i (c z))
    (hu : ∀ z : Ds, ∃ i : ιu, ∃ V : TopologicalSpace.Opens (Lu i),
      ∃ c : Du ≃ₜ V,
        ∀ w : Du, (e (z, w)).val = iu i (c w)) :
    ∃ B : TransverseFoliationBox s t M, p.val ∈ B.image ∧ B.image ⊆ W ∧
      (∀ w : FoliationCoordinateDisk t, ∃ i : ιs,
        ∃ j : FoliationCoordinateDisk s → Ls i, IsOpenEmbedding j ∧
          ∀ z, (B.chart (z, w)).val = is i (j z)) ∧
      (∀ z : FoliationCoordinateDisk s, ∃ i : ιu,
        ∃ j : FoliationCoordinateDisk t → Lu i, IsOpenEmbedding j ∧
          ∀ w, (B.chart (z, w)).val = iu i (j w)) := by
  obtain ⟨js, ju, hjs, hju, B, hp, hBW, hB⟩ := fixed_unit_product_box_within Ds Du O e p W hW hpW
  refine ⟨B, hp, hBW, ?_, ?_⟩
  · intro w
    obtain ⟨i, V, c, hc⟩ := hs (ju w)
    let j : FoliationCoordinateDisk s → Ls i := fun z ↦ (c (js z)).val
    have hj : IsOpenEmbedding j :=
      V.isOpen.isOpenEmbedding_subtypeVal.comp (c.isOpenEmbedding.comp hjs)
    refine ⟨i, j, hj, ?_⟩
    intro z
    exact (hB (z, w)).trans (hc (js z))
  · intro z
    obtain ⟨i, V, c, hc⟩ := hu (js z)
    let j : FoliationCoordinateDisk t → Lu i := fun w ↦ (c (ju w)).val
    have hj : IsOpenEmbedding j :=
      V.isOpen.isOpenEmbedding_subtypeVal.comp (c.isOpenEmbedding.comp hju)
    refine ⟨i, j, hj, ?_⟩
    intro w
    exact (hB (z, w)).trans (hc (ju w))


/-- Pull back the domain charts of a global immersion along a diffeomorphism, retaining the same fixed complement at every point.  This is the global version of the chart argument in `immersion_precompose_diffeomorph_g15`. -/
theorem immersion_precompose_diffeomorph_global {r : ℕ}
    {L N : Type*} [TopologicalSpace L] [TopologicalSpace N]
    [ChartedSpace (Fin r → ℝ) L] [ChartedSpace (Fin r → ℝ) N]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (ι : L → M) (e : Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) N L ∞)
    (h : Manifold.IsImmersion 𝓘(ℝ, Fin r → ℝ) I ∞ ι) :
    Manifold.IsImmersion 𝓘(ℝ, Fin r → ℝ) I ∞ (ι ∘ e) := by
  refine ⟨h.complement, inferInstance, inferInstance, ?_⟩
  intro x
  have hc := h.isImmersionOfComplement_complement (e x)
  have hdom : e.toHomeomorph.transOpenPartialHomeomorph hc.domChart ∈
      IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ N := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas).comp
        e.contMDiff.contMDiffOn (fun z hz ↦ hz)
    · exact e.symm.contMDiff.comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas)
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (hc.continuousAt.comp e.contMDiff.continuous.continuousAt) hc.equiv
    (e.toHomeomorph.transOpenPartialHomeomorph hc.domChart) hc.codChart
    (by simpa using hc.mem_domChart_source) hc.mem_codChart_source hdom
    hc.codChart_mem_maximalAtlas
  intro y hy
  simpa [OpenPartialHomeomorph.extend, Function.comp_def] using hc.writtenInCharts hy


open HolonomyTransverseConstancy
/-- A holomorphic scalar function whose kernel contains the complex tangent of a smooth immersed leaf is locally constant on that leaf inside its domain. (Zhang, Lemma 2) -/
theorem immersed_leaf_transverse_locally_constant
    {d r : ℕ} {X L : Type*}
    [MetricSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (U : ContinuousComplexTangentSubbundle (complexModel d) X)
    (inc : L → X) (hi : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (htangent : ∀ z, (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z).range =
      complexStableRealDistribution U (inc z))
    (V : TopologicalSpace.Opens X) (t : X → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (hker : ∀ z ∈ V,
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t z)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z)).ker = U.toDistribution z) :
    IsLocallyConstant (fun z : inc ⁻¹' (V : Set X) ↦ t (inc z.val)) := by
  have hW : IsOpen (inc ⁻¹' (V : Set X)) := V.isOpen.preimage hi.continuous
  have hmd : MDifferentiableOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, ℂ)
      (t ∘ inc) (inc ⁻¹' (V : Set X)) := by
    intro z hz
    have htc := ht.mdifferentiableOn (by simp)
      |>.mdifferentiableAt (V.isOpen.mem_nhds hz)
    exact ((scalar_real_derivative t (inc z) htc).1.comp z
      (hi.mdifferentiable (by simp) z)).mdifferentiableWithinAt
  apply zero_mfderiv_locally_constant (t ∘ inc) _ hW hmd
  intro z hz
  have htc := ht.mdifferentiableOn (by simp)
    |>.mdifferentiableAt (V.isOpen.mem_nhds hz)
  obtain ⟨htr, hdr⟩ := scalar_real_derivative t (inc z) htc
  rw [mfderiv_comp z htr (hi.mdifferentiable (by simp) z), hdr]
  ext v
  have hv : mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z v ∈
      complexStableRealDistribution U (inc z) := by
    rw [← htangent z]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  obtain ⟨w, hw, he⟩ := Submodule.mem_map.mp hv
  have ht0 : mfderiv (complexModel d) 𝓘(ℂ, ℂ) t (inc z) w = 0 := by
    have hk : w ∈ (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t (inc z))).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t (inc z))).ker := by
      rw [hker _ hz]
      exact hw
    exact hk
  change mfderiv (complexModel d) 𝓘(ℂ, ℂ) t (inc z)
    (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z v) = 0
  rw [← he]
  exact ht0


/-- A transverse holomorphic scalar is constant along each first-factor plaque whose box lies in its domain.  Pull the preceding local constancy statement back through the continuous intrinsic plaque chart and use connectedness of the disk. (Zhang, Lemma 2) -/
theorem intrinsic_plaque_transverse_eq
    {d s r : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] [SecondCountableTopology X]
    [ChartedSpace (Fin (s+r) → ℝ) X]
    (F : TransverseContinuousFoliations s r X)
    (U : ContinuousComplexTangentSubbundle (complexModel d) X)
    (hman : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q; letI := F.stableCharts q
      IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (IntrinsicFoliationLeaf F.stablePartition q))
    (hinc : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q; letI := F.stableCharts q
      ContMDiff 𝓘(ℝ, Fin s → ℝ) (realModel d) ∞
        (fun z : IntrinsicFoliationLeaf F.stablePartition q ↦ z.val))
    (htangent : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q; letI := F.stableCharts q
      ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
        (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel d) Subtype.val z).range =
          complexStableRealDistribution U z.val)
    (V : TopologicalSpace.Opens X) (t : X → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (hker : ∀ z ∈ V,
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t z)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z)).ker = U.toDistribution z)
    (b : F.boxIndex) (hbox : (F.box b).image ⊆ V)
    (w : FoliationCoordinateDisk r) (z z' : FoliationCoordinateDisk s) :
    t ((F.box b).chart (z,w)).val = t ((F.box b).chart (z',w)).val := by
  let q := F.stableLabel b w
  let := F.stableTopology q
  let := F.stableCharts q
  let := hman q
  let plaque : FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition q :=
    fun a ↦ ⟨((F.box b).chart (a,w)).val,F.stable_label b a w⟩
  let T : FoliationCoordinateDisk s →
      (Subtype.val : IntrinsicFoliationLeaf F.stablePartition q → X) ⁻¹' (V : Set X) :=
    fun a ↦ ⟨plaque a,hbox ((F.box b).chart (a,w)).property⟩
  have hT : Continuous T := (F.stable_plaque b w).continuous.subtype_mk _
  have hlc := (immersed_leaf_transverse_locally_constant U Subtype.val
    (hinc q) (htangent q) V t ht hker).comp_continuous hT
  let : PreconnectedSpace (FoliationCoordinateDisk s) :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : Fin s → ℝ) 1).isPreconnected
  exact hlc.apply_eq_of_preconnectedSpace z z'



end HolomorphicAnosov
