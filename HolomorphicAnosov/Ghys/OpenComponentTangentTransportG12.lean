import HolomorphicAnosov.Geometry.Manifold.OpenSubsetInclusionTangentG9
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Constructions
import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant
import HolomorphicAnosov.Geometry.HermitianTangentMetric

/-! Restriction to actual open components (Lee) -/

noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology
namespace HolomorphicAnosov.Ghys

variable {𝕜 E M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ∞ M]

omit [IsManifold 𝓘(𝕜, E) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
/-- In inherited open-submanifold coordinates the inclusion has identity derivative. (Lee, Prop. 1.8) -/
theorem open_component_inclusion_mfderiv (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : U → M) x =
      ContinuousLinearMap.id 𝕜 E := by
  have hd : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : U → M) x :=
    (contMDiff_subtype_val (I := 𝓘(𝕜, E)) (n := ∞)).mdifferentiableAt (by simp)
  rw [hd.mfderiv_abuse]
  change fderivWithin 𝕜 (writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E) x (Subtype.val : U → M)) (Set.range (𝓘(𝕜, E) : E → E)) ((extChartAt 𝓘(𝕜, E) x) x) = ContinuousLinearMap.id 𝕜 E
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  have he : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E) x (Subtype.val : U → M) =ᶠ[
      𝓝 ((extChartAt 𝓘(𝕜, E) x) x)] id := by
    have h := (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (H := E) U (x := x)).symm
    filter_upwards [h, (chartAt E x.val).open_target.mem_nhds (mem_chart_target E x.val)]
      with y hy hyt
    change (chartAt E x.val) (((chartAt E x).symm y).val) = y
    exact (congrArg (chartAt E x.val) hy).trans ((chartAt E x.val).right_inv hyt)
  rw [he.fderiv_eq]
  exact fderiv_id

set_option backward.isDefEq.respectTransparency false in
/-- Tangent inclusion of an open submanifold carries its original topology. (Lee, Prop. 1.8) -/
theorem open_component_tangent_inducing (U : TopologicalSpace.Opens M) :
    _root_.Topology.IsInducing (fun p : TangentBundle 𝓘(𝕜, E) U ↦
      (⟨p.proj.val, p.snd⟩ : TangentBundle 𝓘(𝕜, E) M)) := by
  classical
  let j : TangentBundle 𝓘(𝕜, E) U → TangentBundle 𝓘(𝕜, E) M :=
    fun p ↦ ⟨p.proj.val, p.snd⟩
  have hj : Continuous j := by
    have hc := (contMDiff_subtype_val (I := 𝓘(𝕜, E)) (n := ∞) (U := U)).continuous_tangentMap (by simp)
    convert hc using 1
    funext p
    simp only [j, tangentMap, open_component_inclusion_mfderiv]
    rfl
  rcases isEmpty_or_nonempty U with hempty | hnonempty
  · let : IsEmpty (TangentBundle 𝓘(𝕜, E) U) := ⟨fun p ↦ hempty.false p.proj⟩
    exact ⟨Subsingleton.elim _ _⟩
  let e := U.openPartialHomeomorphSubtypeCoe hnonempty
  have hei : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ∞ (e.symm : M → U) (U : Set M) := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.subtypeVal_comp_iff U e.symm y).mp
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    exact e.right_inv (by simpa [e] using hz)
  let W : Set (TangentBundle 𝓘(𝕜, E) M) :=
    Bundle.TotalSpace.proj ⁻¹' (U : Set M)
  let j' : TangentBundle 𝓘(𝕜, E) U → W := fun p ↦ ⟨j p, p.proj.property⟩
  let k : W → TangentBundle 𝓘(𝕜, E) U :=
    fun p ↦ tangentMapWithin 𝓘(𝕜, E) 𝓘(𝕜, E) e.symm (U : Set M) p.val
  have hk : Continuous k :=
    (hei.continuousOn_tangentMapWithin (by simp) U.isOpen.uniqueMDiffOn).comp_continuous
      continuous_subtype_val (fun p ↦ p.property)
  have hkj : k ∘ j' = id := by
    funext p
    have hp : j p ∈ W := p.proj.property
    have hd := (hei p.proj.val p.proj.property).contMDiffAt (U.isOpen.mem_nhds p.proj.property)
    have heq : (Subtype.val : U → M) ∘ e.symm =ᶠ[𝓝 p.proj.val] id := by
      filter_upwards [U.isOpen.mem_nhds p.proj.property] with y hy
      exact e.right_inv (by simpa [e] using hy)
    have hder := heq.mfderiv_eq (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, E))
    rw [mfderiv_comp _ ((contMDiff_subtype_val (I := 𝓘(𝕜, E)) (n := ∞)).mdifferentiableAt
      (by simp)) (hd.mdifferentiableAt (by simp)), open_component_inclusion_mfderiv,
      mfderiv_id] at hder
    have hid : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e.symm p.proj.val = ContinuousLinearMap.id 𝕜 E := by
      ext v
      exact congrArg (fun T ↦ T v) hder
    change tangentMapWithin 𝓘(𝕜, E) 𝓘(𝕜, E) e.symm (U : Set M) (j p) = p
    rw [tangentMapWithin_eq_tangentMap (U.isOpen.uniqueMDiffOn _ p.proj.property)
      (hd.mdifferentiableAt (by simp))]
    change (⟨e.symm p.proj.val, mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e.symm p.proj.val p.snd⟩ :
      TangentBundle 𝓘(𝕜, E) U) = p
    rw [hid]
    have heleft : e.symm p.proj.val = p.proj := e.left_inv (by simp [e])
    cases p
    simp_all
    rfl
  have hj' : _root_.Topology.IsInducing j' :=
    _root_.Topology.IsInducing.of_comp (hj.subtype_mk _) hk
      (by rw [hkj]; exact _root_.Topology.IsInducing.id)
  exact _root_.Topology.IsInducing.subtypeVal.comp hj'

set_option backward.isDefEq.respectTransparency false in
/-- Local tangent subbundle frames restrict to inherited open submanifolds. (Lee, Prop. 1.8) -/
theorem open_component_subbundle_locally_trivial
    (P : ∀ x : M, Submodule 𝕜 (TangentSpace 𝓘(𝕜, E) x))
    (hloc : ∀ x : M, ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → 𝕜) (fun y : M ↦ ↥(P y))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(𝕜, E) M)) inferInstance
      ∃ e : Bundle.Trivialization (Fin r → 𝕜)
          (TotalSpace.proj (F := Fin r → 𝕜) (E := fun y : M ↦ ↥(P y))),
        x ∈ e.baseSet ∧ e.IsLinear 𝕜)
    (U : TopologicalSpace.Opens M) (x : U) :
    ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → 𝕜) (fun y : U ↦ ↥(P y.val))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(𝕜, E) U)) inferInstance
      ∃ e : Bundle.Trivialization (Fin r → 𝕜)
          (TotalSpace.proj (F := Fin r → 𝕜) (E := fun y : U ↦ ↥(P y.val))),
        x ∈ e.baseSet ∧ e.IsLinear 𝕜 := by
  obtain ⟨r, e, hx, he⟩ := hloc x.val
  let : TopologicalSpace (TotalSpace (Fin r → 𝕜) (fun y : M ↦ ↥(P y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(𝕜, E) M)) inferInstance
  let f : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let : e.IsLinear 𝕜 := he
  refine ⟨r, ?_⟩
  let targetTop : TopologicalSpace (TotalSpace (Fin r → 𝕜) (fun y : U ↦ ↥(P y.val))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj.val, z.snd.val⟩ : TangentBundle 𝓘(𝕜, E) M)) inferInstance
  have ht : pullbackTopology (Fin r → 𝕜) (fun y : M ↦ ↥(P y)) (f : U → M) = targetTop := by
    rw [pullbackTopology_def]
    change TopologicalSpace.induced TotalSpace.proj inferInstance ⊓
      TopologicalSpace.induced (Bundle.Pullback.lift (F := Fin r → 𝕜)
        (E := fun y : M ↦ ↥(P y)) f) (TopologicalSpace.induced _ _) = targetTop
    rw [induced_compose]
    change TopologicalSpace.induced TotalSpace.proj inferInstance ⊓ targetTop = targetTop
    let := targetTop
    apply inf_eq_right.mpr
    rw [← continuous_iff_le_induced]
    have hc : Continuous (fun z : TotalSpace (Fin r → 𝕜) (fun y : U ↦ ↥(P y.val)) ↦
        (⟨z.proj.val, z.snd.val⟩ : TangentBundle 𝓘(𝕜, E) M)) := continuous_induced_dom
    exact (FiberBundle.continuous_proj E (fun y : M ↦ TangentSpace 𝓘(𝕜, E) y)
      |>.comp hc).subtype_mk (fun z ↦ z.proj.property)
  have hu : TopologicalSpace.induced
      (fun z : TotalSpace (Fin r → 𝕜) (fun y : U ↦ ↥(P y.val)) ↦
        (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(𝕜, E) U)) inferInstance = targetTop := by
    rw [(open_component_tangent_inducing (𝕜 := 𝕜) U).eq_induced, induced_compose]
    rfl
  rw [hu, ← ht]
  exact ⟨e.pullback f, hx, Bundle.Trivialization.pullback_linear 𝕜 e f⟩

omit [IsManifold 𝓘(𝕜, E) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction preserves the actual differential in inherited open charts. (Lee, Prop. 1.8) -/
theorem open_component_mfderiv_restrict (U : TopologicalSpace.Opens M)
    (f : M → M) (g : U → U)
    (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ∞ f)
    (hg : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ∞ g)
    (hfg : ∀ x : U, (g x).val = f x.val) (x : U) :
    @Eq (E →L[𝕜] E) (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) g x)
      (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) f x.val) := by
  have heq : (Subtype.val : U → M) ∘ g = f ∘ Subtype.val := funext hfg
  have hval : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ∞ (Subtype.val : U → M) := contMDiff_subtype_val
  have hd := mfderiv_comp x (hval.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
  rw [heq, mfderiv_comp x (hf.mdifferentiableAt (by simp))
    (hval.mdifferentiableAt (by simp)), open_component_inclusion_mfderiv,
    open_component_inclusion_mfderiv] at hd
  ext v
  exact (congrArg (fun T ↦ T v) hd).symm

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Restrict a continuous real tangent subbundle to the inherited open manifold. (Lee, Prop. 1.8) -/
def ContinuousRealTangentSubbundle.restrictOpen
    (P : ContinuousRealTangentSubbundle 𝓘(ℝ, E) M) (U : TopologicalSpace.Opens M) :
    ContinuousRealTangentSubbundle 𝓘(ℝ, E) U where
  toDistribution x := P.toDistribution x.val
  locally_trivial := Ghys.open_component_subbundle_locally_trivial
    P.toDistribution P.locally_trivial U

/-- A component return retains the original invariant complementary subbundles. (Lee, Prop. 1.8) -/
def InvariantRealTangentSplitting.restrictOpenIterate
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (P : InvariantRealTangentSplitting f) (U : TopologicalSpace.Opens M) (N : ℕ)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U U ∞)
    (hfg : ∀ x : U, (g x).val = (f : M → M)^[N] x.val) :
    InvariantRealTangentSplitting g where
  stable := P.stable.restrictOpen U
  unstable := P.unstable.restrictOpen U
  isCompl x := P.isCompl x.val
  stable_map x := by
    have hd := Ghys.open_component_mfderiv_restrict U (realIterate 𝓘(ℝ, E) f N) g
      (realIterate 𝓘(ℝ, E) f N).contMDiff g.contMDiff hfg x
    change (P.stable.toDistribution x.val).map
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x).toLinearMap = P.stable.toDistribution (g x).val
    rw [hd, hfg]
    exact real_distribution_iterate_invariant f _ P.stable_map N x.val
  unstable_map x := by
    have hd := Ghys.open_component_mfderiv_restrict U (realIterate 𝓘(ℝ, E) f N) g
      (realIterate 𝓘(ℝ, E) f N).contMDiff g.contMDiff hfg x
    change (P.unstable.toDistribution x.val).map
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x).toLinearMap = P.unstable.toDistribution (g x).val
    rw [hd, hfg]
    exact real_distribution_iterate_invariant f _ P.unstable_map N x.val

end HolomorphicAnosov

namespace HolomorphicAnosov.Ghys
variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the same smooth Hermitian tensor to an open component. (Lee, Prop. 1.8) -/
theorem smooth_hermitian_restrict_open (U : TopologicalSpace.Opens M)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    IsSmoothHermitianTangentMetric (fun x : U ↦ h x.val) := by
  classical
  intro e he i j
  rcases isEmpty_or_nonempty U with hempty | hnonempty
  · intro z hz
    exact hempty.false (e.symm z) |>.elim
  let v := U.openPartialHomeomorphSubtypeCoe hnonempty
  let c := v.symm.trans e
  have hv : ContMDiff (complexModel d) (complexModel d) ∞ (v : U → M) :=
    contMDiff_subtype_val
  have hvi : ContMDiffOn (complexModel d) (complexModel d) ∞ (v.symm : M → U) v.target := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.subtypeVal_comp_iff U v.symm y).mp
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [v.open_target.mem_nhds hy] with z hz
    exact v.right_inv hz
  have hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ M := by
    apply c.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas he).comp
        (hvi.mono inter_subset_left) inter_subset_right
    · exact (hv.contMDiffOn (s := Set.univ)).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left)
        (fun _ _ ↦ mem_univ _)
  have ht : c.target = e.target := by
    ext z
    change (z ∈ e.target ∧ e.symm z ∈ v.source) ↔ z ∈ e.target
    simp [v]
  have hs := hh c hc i j
  rw [ht] at hs
  apply hs.congr
  intro z hz
  have hz' : z ∈ c.target := by rwa [ht]
  have hd := mfderiv_comp z (hv.mdifferentiableAt (by simp))
    ((contMDiffAt_symm_of_mem_maximalAtlas he hz).mdifferentiableAt (by simp))
  simp only [v, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] at hd
  rw [open_component_inclusion_mfderiv] at hd
  have hd' : @Eq ((ComplexModel d) →L[ℂ] (ComplexModel d))
      (mfderiv (complexModel d) (complexModel d) c.symm z)
      (mfderiv (complexModel d) (complexModel d) e.symm z) := by
    ext w
    exact congrArg (fun T : ComplexModel d →L[ℂ] ComplexModel d ↦ T w) hd
  unfold hermitianTangentChartCoefficient hermitianTangentPairing hermitianTangentChartFrame
  change (h (e.symm z).val).inner _ _ = (h (e.symm z).val).inner _ _
  rw [hd']
  rfl

end HolomorphicAnosov.Ghys

