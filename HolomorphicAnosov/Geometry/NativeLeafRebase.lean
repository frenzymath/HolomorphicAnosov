import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Geometry.ProductBallTransverseIndependence
import HolomorphicAnosov.Geometry.TransverseCompMFDerivZero
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import Mathlib.Topology.Homeomorph.TransferInstance
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace




/-! Native plaque charts define complex atlases on intrinsic leaves and make their inclusions
holomorphic immersions. (Zhang, Thm 1.2; Demailly, I §1.A, pp.7–8 and I §7, p.60) -/

open Set Topology _root_.Topology
open scoped ContDiff Manifold

noncomputable section
namespace HolomorphicAnosov.NativeComplexAtlas

universe u v w a b
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {A : Type w} [NormedAddCommGroup A] [NormedSpace ℂ A]
  {H : Type a} [TopologicalSpace H] {I : ModelWithCorners ℂ A H}
  {X : Type b} [TopologicalSpace X] [ChartedSpace H X]
  {L : Type*} [TopologicalSpace L]

/-- The charted space determined by the native plaque charts on the intrinsic leaf topology. -/
@[local instance_reducible] private def nativeChartedSpace (c : L → OpenPartialHomeomorph L E)
    (hc : ∀ p, p ∈ (c p).source) : ChartedSpace E L where
  atlas := Set.range c
  chartAt := c
  mem_chart_source := hc
  chart_mem_atlas p := ⟨p, rfl⟩

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- The forward native chart coordinate equals the first projection of the ambient box coordinate. -/
private theorem chart_eq_fst (ι : L → X) (c : L → OpenPartialHomeomorph L E)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (p q : L) (hq : q ∈ (c p).source) :
    (c p) q = ((B p) (ι q)).1 := by
  have hm := hmem p ((c p) q) ((c p).map_source hq)
  have he := hinv p ((c p) q) ((c p).map_source hq)
  rw [(c p).left_inv hq] at he
  rw [he, (B p).right_inv hm]

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- The inclusion of a native plaque lies in its assigned ambient box. -/
private theorem inclusion_mem_box (ι : L → X) (c : L → OpenPartialHomeomorph L E)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (p q : L) (hq : q ∈ (c p).source) : ι q ∈ (B p).source := by
  have he := hinv p ((c p) q) ((c p).map_source hq)
  rw [(c p).left_inv hq] at he
  rw [he]
  exact (B p).map_target (hmem p _ ((c p).map_source hq))

/-- Native plaque chart transitions are holomorphic on their overlap domains. -/
private theorem transition_contDiffOn (ι : L → X) (c : L → OpenPartialHomeomorph L E)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (hB : ∀ p, ContMDiffOn I 𝓘(ℂ, E × F) ∞ (B p) (B p).source)
    (hBi : ∀ p, ContMDiffOn 𝓘(ℂ, E × F) I ∞ (B p).symm (B p).target)
    (p q : L) :
    ContDiffOn ℂ ∞ ((c p).symm.trans (c q)) ((c p).symm.trans (c q)).source := by
  let S := ((c p).symm.trans (c q)).source
  have hs : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E × F) ∞
      (fun z : E ↦ (z, t p)) S := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (contDiff_id.prodMk contDiff_const).contDiffOn
  have hi : ContMDiffOn 𝓘(ℂ, E) I ∞
      (fun z ↦ (B p).symm (z, t p)) S :=
    (hBi p).comp hs (fun z hz ↦ hmem p z hz.1)
  have ho : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E × F) ∞
      (fun z ↦ (B q) ((B p).symm (z, t p))) S := by
    apply (hB q).comp hi
    intro z hz
    change z ∈ (c p).target ∧ (c p).symm z ∈ (c q).source at hz
    change (B p).symm (z, t p) ∈ (B q).source
    rw [← hinv p z hz.1]
    exact inclusion_mem_box ι c B t hmem hinv q _ hz.2
  have hf : ContMDiff 𝓘(ℂ, E × F) 𝓘(ℂ, E) ∞ (Prod.fst : E × F → E) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_fst
  have hh := hf.comp_contMDiffOn ho
  rw [contMDiffOn_iff_contDiffOn] at hh
  apply hh.congr
  intro z hz
  change z ∈ (c p).target ∧ (c p).symm z ∈ (c q).source at hz
  change (c q) ((c p).symm z) = ((B q) ((B p).symm (z, t p))).1
  rw [chart_eq_fst ι c B t hmem hinv q _ hz.2, hinv p z hz.1]

/-- The native plaque atlas defines a complex manifold structure on the intrinsic leaf. -/
private theorem native_isManifold (ι : L → X) (c : L → OpenPartialHomeomorph L E)
    (hc : ∀ p, p ∈ (c p).source)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (hB : ∀ p, ContMDiffOn I 𝓘(ℂ, E × F) ∞ (B p) (B p).source)
    (hBi : ∀ p, ContMDiffOn 𝓘(ℂ, E × F) I ∞ (B p).symm (B p).target) :
    letI := nativeChartedSpace c hc
    IsManifold 𝓘(ℂ, E) ∞ L := by
  let _ := nativeChartedSpace c hc
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
  simpa only [Function.comp_def, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, id_eq, Set.preimage_id, Set.range_id, Set.inter_univ] using
    transition_contDiffOn ι c B t hmem hinv hB hBi p q

/-- The leaf inclusion is holomorphic in the native plaque atlas. -/
private theorem native_inclusion_contMDiff (ι : L → X) (c : L → OpenPartialHomeomorph L E)
    (hc : ∀ p, p ∈ (c p).source)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (hB : ∀ p, ContMDiffOn I 𝓘(ℂ, E × F) ∞ (B p) (B p).source)
    (hBi : ∀ p, ContMDiffOn 𝓘(ℂ, E × F) I ∞ (B p).symm (B p).target) :
    letI := nativeChartedSpace c hc
    ContMDiff 𝓘(ℂ, E) I ∞ ι := by
  let _ := nativeChartedSpace c hc
  let _ := native_isManifold ι c hc B t hmem hinv hB hBi
  intro p
  have hs : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (c p) (c p).source :=
    contMDiffOn_chart (I := 𝓘(ℂ, E)) (x := p)
  have hp := hs.prodMk_space (contMDiffOn_const (c := t p))
  have hb : ContMDiffOn 𝓘(ℂ, E) I ∞
      (fun q ↦ (B p).symm ((c p) q, t p)) (c p).source :=
    (hBi p).comp hp (fun q hq ↦ hmem p _ ((c p).map_source hq))
  have hi : ContMDiffOn 𝓘(ℂ, E) I ∞ ι (c p).source := by
    apply hb.congr
    intro q hq
    have he := hinv p ((c p) q) ((c p).map_source hq)
    simpa only [(c p).left_inv hq] using he
  exact hi.contMDiffAt ((c p).open_source.mem_nhds (hc p))

/-- The derivative of the native leaf inclusion is injective at every point. -/
private theorem native_inclusion_mfderiv_injective
    (ι : L → X) (c : L → OpenPartialHomeomorph L E)
    (hc : ∀ p, p ∈ (c p).source)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (hB : ∀ p, ContMDiffOn I 𝓘(ℂ, E × F) ∞ (B p) (B p).source)
    (hBi : ∀ p, ContMDiffOn 𝓘(ℂ, E × F) I ∞ (B p).symm (B p).target) :
    letI := nativeChartedSpace c hc
    ∀ p, Function.Injective (mfderiv 𝓘(ℂ, E) I ι p) := by
  let _ := nativeChartedSpace c hc
  let _ := native_isManifold ι c hc B t hmem hinv hB hBi
  have hi := native_inclusion_contMDiff ι c hc B t hmem hinv hB hBi
  intro p
  let g : X → E := fun x ↦ ((B p) x).1
  have hf : ContMDiff 𝓘(ℂ, E × F) 𝓘(ℂ, E) ∞ (Prod.fst : E × F → E) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_fst
  have hg : ContMDiffAt I 𝓘(ℂ, E) ∞ g (ι p) :=
    hf.contMDiffAt.comp (ι p) ((hB p).contMDiffAt
      ((B p).open_source.mem_nhds (inclusion_mem_box ι c B t hmem hinv p p (hc p))))
  have he : g ∘ ι =ᶠ[𝓝 p] (c p) := by
    filter_upwards [(c p).open_source.mem_nhds (hc p)] with q hq
    exact (chart_eq_fst ι c B t hmem hinv p q hq).symm
  have hd : (mfderiv I 𝓘(ℂ, E) g (ι p)).comp (mfderiv 𝓘(ℂ, E) I ι p) =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (c p) p := by
    rw [← mfderiv_comp p (hg.mdifferentiableAt (by simp))
      ((hi p).mdifferentiableAt (by simp))]
    exact he.mfderiv_eq
  intro u v huv
  apply (mdifferentiable_chart (I := 𝓘(ℂ, E)) p).mfderiv_injective (hc p)
  have hh := congrArg (fun D ↦ D u) hd
  have hh' := congrArg (fun D ↦ D v) hd
  exact hh.symm.trans ((congrArg (mfderiv I 𝓘(ℂ, E) g (ι p)) huv).trans hh')

/-- Local plaque charts compatible with holomorphic ambient boxes give a complex leaf atlas whose
inclusion is a holomorphic immersion. -/
private theorem native_complex_leaf_structure
    (ι : L → X) (c : L → OpenPartialHomeomorph L E)
    (hc : ∀ p, p ∈ (c p).source)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (hB : ∀ p, ContMDiffOn I 𝓘(ℂ, E × F) ∞ (B p) (B p).source)
    (hBi : ∀ p, ContMDiffOn 𝓘(ℂ, E × F) I ∞ (B p).symm (B p).target) :
    ∃ cs : ChartedSpace E L, letI := cs
      IsManifold 𝓘(ℂ, E) ∞ L ∧
      ContMDiff 𝓘(ℂ, E) I ∞ ι ∧
      ∀ p, Function.Injective (mfderiv 𝓘(ℂ, E) I ι p) := by
  refine ⟨nativeChartedSpace c hc, ?_⟩
  exact ⟨native_isManifold ι c hc B t hmem hinv hB hBi,
    native_inclusion_contMDiff ι c hc B t hmem hinv hB hBi,
    native_inclusion_mfderiv_injective ι c hc B t hmem hinv hB hBi⟩


end HolomorphicAnosov.NativeComplexAtlas

/-! Local inverse charts give open holomorphic plaque parametrizations on the intrinsic leaf
topology. -/
namespace HolomorphicAnosov.WholePlaqueSupport
open TopologicalSpace Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
section Topological
variable {A F X L : Type*} [TopologicalSpace A] [TopologicalSpace F]
  [TopologicalSpace X] [TopologicalSpace L]

/-- A plaque parametrization with local inverse charts at every parameter is an open embedding. -/
private theorem whole_plaque_isOpenEmbedding
    (D : Opens A) (ι : L → X) (hι : Function.Injective ι)
    (e : OpenPartialHomeomorph X (A × F)) (b : F)
    (htarget : ∀ a : D, (a.val, b) ∈ e.target)
    (h : D → L) (hvalue : ∀ a, ι (h a) = e.symm (a.val, b))
    (k : D → OpenPartialHomeomorph L A)
    (hk : ∀ a, h a ∈ (k a).source)
    (hkforward : ∀ a, (k a) (h a) = a.val)
    (hkinverse : ∀ a u, u ∈ (k a).target → ι ((k a).symm u) = e.symm (u, b)) :
    IsOpenEmbedding h := by
  have heforward : ∀ a, e (ι (h a)) = (a.val, b) := by
    intro a
    rw [hvalue a, e.right_inv (htarget a)]
  have hinj : Function.Injective h := by
    intro a a' haa'
    apply Subtype.ext
    have hh := congrArg (fun z ↦ (e (ι z)).1) haa'
    simpa only [heforward, Prod.fst] using hh
  have hlocal : ∀ a u, u ∈ (k a).target → ∀ a' : D, a'.val = u → h a' = (k a).symm u := by
    intro a u hu a' ha'
    apply hι
    rw [hvalue a', hkinverse a u hu, ha']
  have hcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro a
    have hat : a.val ∈ (k a).target := hkforward a ▸ (k a).map_source (hk a)
    have hc : ContinuousAt (fun a' : D ↦ (k a).symm a'.val) a :=
      ((k a).continuousAt_symm hat).comp continuous_subtype_val.continuousAt
    apply hc.congr
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((k a).open_target.mem_nhds hat)] with a' ha'
    exact (hlocal a a'.val ha' a' rfl).symm
  have hopen : IsOpenMap h := by
    intro O hO
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨a, haO, rfl⟩
    let S : Set A := Subtype.val '' O
    have hS : IsOpen S := D.isOpen.isOpenMap_subtype_val O hO
    let V : Set L := (k a).source ∩ (k a) ⁻¹' S
    have hV : IsOpen V :=
      (k a).continuousOn.isOpen_inter_preimage (k a).open_source hS
    have haV : h a ∈ V := ⟨hk a, by
      change (k a) (h a) ∈ S
      rw [hkforward a]
      exact ⟨a, haO, rfl⟩⟩
    apply Filter.mem_of_superset (hV.mem_nhds haV)
    intro z hz
    obtain ⟨a', ha'O, ha'z⟩ := hz.2
    refine ⟨a', ha'O, ?_⟩
    exact (hlocal a ((k a) z) ((k a).map_source hz.1) a' ha'z).trans
      ((k a).left_inv hz.1)
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen

/-- The plaque parametrization is a homeomorphism onto an intrinsically open range. -/
private theorem whole_plaque_homeomorph
    (D : Opens A) (ι : L → X) (hι : Function.Injective ι)
    (e : OpenPartialHomeomorph X (A × F)) (b : F)
    (htarget : ∀ a : D, (a.val, b) ∈ e.target)
    (h : D → L) (hvalue : ∀ a, ι (h a) = e.symm (a.val, b))
    (k : D → OpenPartialHomeomorph L A)
    (hk : ∀ a, h a ∈ (k a).source)
    (hkforward : ∀ a, (k a) (h a) = a.val)
    (hkinverse : ∀ a u, u ∈ (k a).target → ι ((k a).symm u) = e.symm (u, b)) :
    ∃ U : Opens L, ∃ H : D ≃ₜ U, ∀ a, (H a).val = h a := by
  have hh := whole_plaque_isOpenEmbedding D ι hι e b htarget h hvalue k hk hkforward hkinverse
  let U : Opens L := ⟨Set.range h, hh.isOpen_range⟩
  exact ⟨U, hh.isEmbedding.toHomeomorph, fun _ ↦ rfl⟩
end Topological

section Complex
variable {E F A H X L : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [TopologicalSpace H] (I : ModelWithCorners ℂ A H)
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace L]

/-- The plaque parametrization is holomorphic in the native complex atlas. -/
private theorem whole_plaque_contMDiff
    (D : Opens E) (ι : L → X)
    (c : L → OpenPartialHomeomorph L E) (hc : ∀ p, p ∈ (c p).source)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (hB : ∀ p, ContMDiffOn I 𝓘(ℂ, E × F) ∞ (B p) (B p).source)
    (hBi : ∀ p, ContMDiffOn 𝓘(ℂ, E × F) I ∞ (B p).symm (B p).target)
    (e : OpenPartialHomeomorph X (E × F))
    (hei : ContMDiffOn 𝓘(ℂ, E × F) I ∞ e.symm e.target)
    (b : F) (htarget : ∀ a : D, (a.val, b) ∈ e.target)
    (h : D → L) (hvalue : ∀ a, ι (h a) = e.symm (a.val, b))
    (hcont : Continuous h) :
    letI := NativeComplexAtlas.nativeChartedSpace c hc
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ h := by
  let _ := NativeComplexAtlas.nativeChartedSpace c hc
  let _ := NativeComplexAtlas.native_isManifold ι c hc B t hmem hinv hB hBi
  have hs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E × F) ∞ (fun a : D ↦ (a.val, b)) :=
    contMDiff_subtype_val.prodMk_space contMDiff_const
  have hz : ContMDiff 𝓘(ℂ, E) I ∞ (fun a : D ↦ e.symm (a.val, b)) :=
    hei.comp_contMDiff hs htarget
  intro a
  let p := h a
  have hp : ι p ∈ (B p).source :=
    NativeComplexAtlas.inclusion_mem_box ι c B t hmem hinv p p (hc p)
  have hb : ContMDiffAt I 𝓘(ℂ, E × F) ∞ (B p) (e.symm (a.val, b)) := by
    rw [← hvalue a]
    exact (hB p).contMDiffAt ((B p).open_source.mem_nhds hp)
  have hv : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞
      (fun a' : D ↦ ((B p) (e.symm (a'.val, b))).1) a :=
    (ContinuousLinearMap.fst ℂ E F).contDiff.contDiffAt.comp_contMDiffAt
      (hb.comp a (hz a))
  apply (contMDiffAt_iff_target_of_mem_source (I := 𝓘(ℂ, E))
    (I' := 𝓘(ℂ, E)) (y := p) (hc p)).mpr
  refine ⟨hcont.continuousAt, ?_⟩
  change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ ((c p) ∘ h) a
  apply hv.congr_of_eventuallyEq
  filter_upwards [hcont.continuousAt.preimage_mem_nhds
    ((c p).open_source.mem_nhds (hc p))] with a' ha'
  change (c p) (h a') = ((B p) (e.symm (a'.val, b))).1
  rw [NativeComplexAtlas.chart_eq_fst ι c B t hmem hinv p (h a') ha', hvalue a']

/-- The inverse of the plaque homeomorphism is holomorphic. -/
private theorem whole_plaque_homeomorph_inverse_contMDiff
    (D : Opens E) (ι : L → X)
    (c : L → OpenPartialHomeomorph L E) (hc : ∀ p, p ∈ (c p).source)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (hB : ∀ p, ContMDiffOn I 𝓘(ℂ, E × F) ∞ (B p) (B p).source)
    (hBi : ∀ p, ContMDiffOn 𝓘(ℂ, E × F) I ∞ (B p).symm (B p).target)
    (e : OpenPartialHomeomorph X (E × F))
    (he : ContMDiffOn I 𝓘(ℂ, E × F) ∞ e e.source)
    (b : F) (htarget : ∀ a : D, (a.val, b) ∈ e.target)
    (h : D → L) (hvalue : ∀ a, ι (h a) = e.symm (a.val, b))
    (U : Opens L) (H : D ≃ₜ U) (hH : ∀ a, (H a).val = h a) :
    letI := NativeComplexAtlas.nativeChartedSpace c hc
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ H.symm := by
  let _ := NativeComplexAtlas.nativeChartedSpace c hc
  let _ := NativeComplexAtlas.native_isManifold ι c hc B t hmem hinv hB hBi
  have hi := NativeComplexAtlas.native_inclusion_contMDiff ι c hc B t hmem hinv hB hBi
  have hback : ∀ z : U, h (H.symm z) = z.val := by
    intro z
    exact (hH (H.symm z)).symm.trans (congrArg Subtype.val (H.apply_symm_apply z))
  have hdomain : ∀ z : U, ι z.val ∈ e.source := by
    intro z
    rw [← hback z, hvalue (H.symm z)]
    exact e.map_target (htarget (H.symm z))
  have hh : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E × F) ∞ (fun z : U ↦ e (ι z.val)) :=
    he.comp_contMDiff (hi.comp contMDiff_subtype_val) hdomain
  have hp : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (fun z : U ↦ (e (ι z.val)).1) :=
    (ContinuousLinearMap.fst ℂ E F).contDiff.comp_contMDiff hh
  apply (ContMDiff.subtypeVal_comp_iff D H.symm).mp
  apply hp.congr
  intro z
  change (H.symm z).val = (e (ι z.val)).1
  rw [← hback z, hvalue (H.symm z), e.right_inv (htarget (H.symm z))]

/-- The plaque parametrization is a complex diffeomorphism onto its intrinsically open image. -/
private theorem whole_plaque_diffeomorph
    (D : Opens E) (ι : L → X) (hι : Function.Injective ι)
    (c : L → OpenPartialHomeomorph L E) (hc : ∀ p, p ∈ (c p).source)
    (B : L → OpenPartialHomeomorph X (E × F)) (t : L → F)
    (hmem : ∀ p z, z ∈ (c p).target → (z, t p) ∈ (B p).target)
    (hinv : ∀ p z, z ∈ (c p).target → ι ((c p).symm z) = (B p).symm (z, t p))
    (hB : ∀ p, ContMDiffOn I 𝓘(ℂ, E × F) ∞ (B p) (B p).source)
    (hBi : ∀ p, ContMDiffOn 𝓘(ℂ, E × F) I ∞ (B p).symm (B p).target)
    (e : OpenPartialHomeomorph X (E × F))
    (he : ContMDiffOn I 𝓘(ℂ, E × F) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℂ, E × F) I ∞ e.symm e.target)
    (b : F) (htarget : ∀ a : D, (a.val, b) ∈ e.target)
    (h : D → L) (hvalue : ∀ a, ι (h a) = e.symm (a.val, b))
    (k : D → OpenPartialHomeomorph L E)
    (hk : ∀ a, h a ∈ (k a).source)
    (hkforward : ∀ a, (k a) (h a) = a.val)
    (hkinverse : ∀ a u, u ∈ (k a).target → ι ((k a).symm u) = e.symm (u, b)) :
    letI := NativeComplexAtlas.nativeChartedSpace c hc
    ∃ U : Opens L, (U : Set L) = Set.range h ∧
      ∃ H : Diffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) D U ∞,
        (∀ a, (H a).val = h a) ∧ ∀ a, ι (H a).val = e.symm (a.val, b) := by
  let _ := NativeComplexAtlas.nativeChartedSpace c hc
  have hhopen := whole_plaque_isOpenEmbedding D ι hι e b htarget h hvalue
    k hk hkforward hkinverse
  obtain ⟨U, H, hH⟩ := whole_plaque_homeomorph D ι hι e b htarget h hvalue
    k hk hkforward hkinverse
  have hU : (U : Set L) = Set.range h := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := H.surjective ⟨z, hz⟩
      exact ⟨a, (hH a).symm.trans (congrArg Subtype.val ha)⟩
    · rintro ⟨a, rfl⟩
      rw [← hH a]
      exact (H a).property
  have hforward : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ H := by
    apply (ContMDiff.subtypeVal_comp_iff U H).mp
    have hh := whole_plaque_contMDiff I D ι c hc B t hmem hinv hB hBi
      e hei b htarget h hvalue hhopen.continuous
    exact hh.congr hH
  have hback := whole_plaque_homeomorph_inverse_contMDiff I D ι c hc B t
    hmem hinv hB hBi e he b htarget h hvalue U H hH
  let H' : Diffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) D U ∞ :=
    { H.toEquiv with contMDiff_toFun := hforward, contMDiff_invFun := hback }
  refine ⟨U, hU, H', hH, ?_⟩
  intro a
  change ι (H a).val = e.symm (a.val, b)
  rw [hH a, hvalue a]

end Complex
end
end HolomorphicAnosov.WholePlaqueSupport


/-! Asymptotic quotient classes are identified with native leaves by maps preserving ambient points.
The intrinsic topology and complex atlas transfer along these identifications. (HPS, §7,
pp.115–116; Ghys, §2, pp.588–589; Demailly, I §1.A, pp.7–8) -/

open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
namespace HolomorphicAnosov.NativeClassCarrier

universe u v w

section Carrier
variable {M : Type u} [MetricSpace M] (f : M ≃ₜ M) (R : Setoid M)
  (hR : ∀ x y, R x y ↔ ForwardAsymptotic f x y) (q : Quotient R)

include hR in
/-- Equality of quotient labels is equivalent to asymptotic equivalence. -/
private theorem class_label_iff (x y : M) :
    Quotient.mk R y = Quotient.mk R x ↔ ForwardAsymptotic f x y := by
  rw [Quotient.eq]
  exact ⟨fun h ↦ (hR x y).mp (R.symm h),
    fun h ↦ R.symm ((hR x y).mpr h)⟩

/-- The point-preserving equivalence between a quotient-class carrier and the native leaf at its
representative. -/
private def nativeExtractClassNativeEquiv : IntrinsicFoliationLeaf R q ≃ StableAsymptoticLeaf f q.out where
  toFun z := ⟨z.val, (hR q.out z.val).mp
    (R.symm (Quotient.mk_eq_iff_out.mp z.property))⟩
  invFun z := ⟨z.val, Quotient.mk_eq_iff_out.mpr
    (R.symm ((hR q.out z.val).mpr z.property))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem nativeExtractClassNativeEquiv_val (z : IntrinsicFoliationLeaf R q) :
    (nativeExtractClassNativeEquiv f R hR q z).val = z.val := rfl

@[simp] theorem nativeExtractClassNativeEquiv_symm_val (z : StableAsymptoticLeaf f q.out) :
    ((nativeExtractClassNativeEquiv f R hR q).symm z).val = z.val := rfl

/-- The quotient-class topology pulled back from the intrinsic native leaf topology by the
point-preserving equivalence. -/
@[local instance_reducible] private def classTopology (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out)) :
    TopologicalSpace (IntrinsicFoliationLeaf R q) :=
  letI := nativeTopology
  (nativeExtractClassNativeEquiv f R hR q).topologicalSpace

/-- The point-preserving homeomorphism between the quotient class and its native leaf. -/
private def nativeExtractClassNativeHomeomorph
    (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out)) :
    letI := nativeTopology
    letI := classTopology f R hR q nativeTopology
    IntrinsicFoliationLeaf R q ≃ₜ StableAsymptoticLeaf f q.out :=
  letI := nativeTopology
  (nativeExtractClassNativeEquiv f R hR q).homeomorph

@[simp] theorem nativeExtractClassNativeHomeomorph_val
    (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out))
    (z : IntrinsicFoliationLeaf R q) :
    letI := nativeTopology
    letI := classTopology f R hR q nativeTopology
    (nativeExtractClassNativeHomeomorph f R hR q nativeTopology z).val = z.val := rfl

@[simp] theorem nativeExtractClassNativeHomeomorph_symm_val
    (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out))
    (z : StableAsymptoticLeaf f q.out) :
    letI := nativeTopology
    letI := classTopology f R hR q nativeTopology
    ((nativeExtractClassNativeHomeomorph f R hR q nativeTopology).symm z).val = z.val := rfl

/-- The quotient-class topology is Hausdorff, second countable, and connected when the native
topology has these properties. -/
private theorem class_topological_properties
    (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out))
    (hT : @T2Space _ nativeTopology)
    (hS : @SecondCountableTopology _ nativeTopology)
    (hC : @ConnectedSpace _ nativeTopology) :
    letI := classTopology f R hR q nativeTopology
    T2Space (IntrinsicFoliationLeaf R q) ∧
      SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
      ConnectedSpace (IntrinsicFoliationLeaf R q) := by
  let _ := nativeTopology
  let _ := classTopology f R hR q nativeTopology
  let h := nativeExtractClassNativeHomeomorph f R hR q nativeTopology
  exact ⟨h.symm.t2Space, h.secondCountableTopology,
    h.symm.surjective.connectedSpace h.symm.continuous⟩

end Carrier

section ChartTransport
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {C : Type u} {L : Type w} [TopologicalSpace C] [TopologicalSpace L]
  [ChartedSpace E L]

/-- The charted space obtained by pulling back native charts along a homeomorphism. -/
@[local instance_reducible] private def carriedChartedSpace (h : C ≃ₜ L) : ChartedSpace E C where
  atlas := Set.range (fun p : C ↦ h.transOpenPartialHomeomorph (chartAt E (h p)))
  chartAt p := h.transOpenPartialHomeomorph (chartAt E (h p))
  mem_chart_source p := mem_chart_source E (h p)
  chart_mem_atlas p := ⟨p, rfl⟩

omit [NormedSpace ℂ E] in
/-- Transitions between pulled-back charts equal the corresponding native chart transitions. -/
private theorem carried_transition (h : C ≃ₜ L) (p q : C) :
    (h.transOpenPartialHomeomorph (chartAt E (h p))).symm.trans
      (h.transOpenPartialHomeomorph (chartAt E (h q))) =
    (chartAt E (h p)).symm.trans (chartAt E (h q)) := by
  apply OpenPartialHomeomorph.ext
  · intro z
    change (chartAt E (h q)) (h (h.symm ((chartAt E (h p)).symm z))) = _
    rw [h.apply_symm_apply]
    rfl
  · intro z
    change (chartAt E (h p)) (h (h.symm ((chartAt E (h q)).symm z))) = _
    rw [h.apply_symm_apply]
    rfl
  · ext z
    simp [Homeomorph.transOpenPartialHomeomorph]

/-- The pulled-back atlas defines a complex manifold structure. -/
private theorem carried_isManifold [IsManifold 𝓘(ℂ, E) ∞ L] (h : C ≃ₜ L) :
    letI := carriedChartedSpace (E := E) h
    IsManifold 𝓘(ℂ, E) ∞ C := by
  let _ := carriedChartedSpace (E := E) h
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
  rw [carried_transition]
  have hh : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ∞
      ((chartAt E (h p)).symm.trans (chartAt E (h q)))
      ((chartAt E (h p)).symm.trans (chartAt E (h q))).source :=
    (contMDiffOn_chart (I := 𝓘(ℂ, E)) (x := h q)).comp
      ((contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (x := h p)).mono
        (fun z hz ↦ hz.1)) (fun z hz ↦ hz.2)
  simpa only [contMDiffOn_iff_contDiffOn, Function.comp_def,
    OpenPartialHomeomorph.coe_trans, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, id_eq, Set.preimage_id, Set.range_id,
    Set.inter_univ] using hh

/-- The homeomorphism to the native leaf is holomorphic in the pulled-back atlas. -/
private theorem carried_contMDiff [IsManifold 𝓘(ℂ, E) ∞ L] (h : C ≃ₜ L) :
    letI := carriedChartedSpace (E := E) h
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ h := by
  let _ := carriedChartedSpace (E := E) h
  let _ := carried_isManifold (E := E) h
  intro p
  have hh : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ∞
      (fun q : C ↦ (chartAt E (h p)).symm ((chartAt E p) q))
      (chartAt E p).source :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (x := h p)).comp
      (contMDiffOn_chart (I := 𝓘(ℂ, E)) (x := p))
      (fun q hq ↦ (chartAt E p).map_source hq)
  have hi : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ h (chartAt E p).source := by
    apply hh.congr
    intro q hq
    exact ((chartAt E (h p)).left_inv hq).symm
  exact hi.contMDiffAt ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))

/-- The inverse homeomorphism is holomorphic in the pulled-back atlas. -/
private theorem carried_symm_contMDiff [IsManifold 𝓘(ℂ, E) ∞ L] (h : C ≃ₜ L) :
    letI := carriedChartedSpace (E := E) h
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ h.symm := by
  let _ := carriedChartedSpace (E := E) h
  let _ := carried_isManifold (E := E) h
  intro l
  let p := h.symm l
  have hh : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ∞
      (fun q : L ↦ (chartAt E p).symm ((chartAt E (h p)) q))
      (chartAt E (h p)).source :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (x := p)).comp
      (contMDiffOn_chart (I := 𝓘(ℂ, E)) (x := h p))
      (fun q hq ↦ (chartAt E (h p)).map_source hq)
  have hi : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ h.symm (chartAt E (h p)).source := by
    apply hh.congr
    intro q hq
    change h.symm q = h.symm ((chartAt E (h p)).symm ((chartAt E (h p)) q))
    rw [(chartAt E (h p)).left_inv hq]
  have hl := hi.contMDiffAt ((chartAt E (h p)).open_source.mem_nhds
    (mem_chart_source E (h p)))
  simpa only [p, h.apply_symm_apply] using hl

/-- The derivative of the chart-transport homeomorphism is injective. -/
private theorem carried_mfderiv_injective [IsManifold 𝓘(ℂ, E) ∞ L] (h : C ≃ₜ L) :
    letI := carriedChartedSpace (E := E) h
    ∀ p, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) h p) := by
  let _ := carriedChartedSpace (E := E) h
  let _ := carried_isManifold (E := E) h
  intro p
  have hd := mfderiv_comp p
    ((carried_symm_contMDiff (E := E) h (h p)).mdifferentiableAt (by simp))
    ((carried_contMDiff (E := E) h p).mdifferentiableAt (by simp))
  have he : (h.symm ∘ h : C → C) = id := funext h.symm_apply_apply
  rw [he, mfderiv_id] at hd
  intro v w hvw
  have hh := congrArg (fun D ↦ D v) hd
  have hh' := congrArg (fun D ↦ D w) hd
  exact hh.trans ((congrArg (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) h.symm (h p)) hvw).trans hh'.symm)

end ChartTransport

section NativeDatum
variable {d r : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
  (f : M ≃ₜ M) (R : Setoid M)
  (hR : ∀ x y, R x y ↔ ForwardAsymptotic f x y) (q : Quotient R)
  {P : RealTangentDistribution (realModel d) M}
  (D : NativeAsymptoticLeafDatum (realModel d) f P q.out)

/-- The quotient class inherits a complex manifold structure and a holomorphic immersed inclusion
from its native leaf datum. -/
private theorem native_class_complex_structure
    (cs : letI := D.topology
      ChartedSpace (ComplexModel r) (StableAsymptoticLeaf f q.out))
    (hm : letI := D.topology; letI := cs
      IsManifold (complexModel r) ∞ (StableAsymptoticLeaf f q.out))
    (hi : letI := D.topology; letI := cs
      ContMDiff (complexModel r) (complexModel d) ∞
        (Subtype.val : StableAsymptoticLeaf f q.out → M))
    (hd : letI := D.topology; letI := cs
      ∀ p, Function.Injective (mfderiv (complexModel r) (complexModel d)
        (Subtype.val : StableAsymptoticLeaf f q.out → M) p)) :
    letI := classTopology f R hR q D.topology
    ∃ classCharts : ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf R q),
      letI := classCharts
      IsManifold (complexModel r) ∞ (IntrinsicFoliationLeaf R q) ∧
      T2Space (IntrinsicFoliationLeaf R q) ∧
      SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
      ConnectedSpace (IntrinsicFoliationLeaf R q) ∧
      ContMDiff (complexModel r) (complexModel d) ∞
        (Subtype.val : IntrinsicFoliationLeaf R q → M) ∧
      ∀ p, Function.Injective (mfderiv (complexModel r) (complexModel d)
        (Subtype.val : IntrinsicFoliationLeaf R q → M) p) := by
  let _ := D.topology
  let _ := cs
  let _ := classTopology f R hR q D.topology
  let h := nativeExtractClassNativeHomeomorph f R hR q D.topology
  let _ := carriedChartedSpace (E := ComplexModel r) h
  let _ := hm
  let _ := carried_isManifold (E := ComplexModel r) h
  have hh := carried_contMDiff (E := ComplexModel r) h
  have hj : ContMDiff (complexModel r) (complexModel d) ∞
      (Subtype.val : IntrinsicFoliationLeaf R q → M) := hi.comp hh
  obtain ⟨hT, hS, hC⟩ := class_topological_properties f R hR q D.topology
    D.hausdorff D.secondCountable D.connected
  refine ⟨carriedChartedSpace (E := ComplexModel r) h, inferInstance,
    hT, hS, hC, hj, ?_⟩
  intro p v w hvw
  have he : (Subtype.val : StableAsymptoticLeaf f q.out → M) ∘ h =
      (Subtype.val : IntrinsicFoliationLeaf R q → M) := rfl
  have hc := mfderiv_comp p ((hi (h p)).mdifferentiableAt (by simp))
    ((hh p).mdifferentiableAt (by simp))
  rw [he] at hc
  apply carried_mfderiv_injective (E := ComplexModel r) h p
  apply hd (h p)
  have hv := congrArg (fun D ↦ D v) hc
  have hw := congrArg (fun D ↦ D w) hc
  exact hv.symm.trans (hvw.trans hw)

end NativeDatum

end HolomorphicAnosov.NativeClassCarrier


/-! Product-box slices generate the native asymptotic partition and determine its quotient labels.
(Shub, Def. 2.1, pp.8–9; HPS, pp.114–116; Nisoli, Defs. 1.1.1–1.1.3, pp.9–10) -/

namespace HolomorphicAnosov.NativeBoxPartition
noncomputable section
open Set Filter Topology _root_.Topology
open scoped ContDiff

/-- Forward asymptoticity is an equivalence relation. -/
private theorem asymptotic_equivalence {M : Type*} [MetricSpace M] (f : M → M) :
    Equivalence (ForwardAsymptotic f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [ForwardAsymptotic]
  · intro x y h
    simpa only [ForwardAsymptotic, dist_comm] using h
  · intro x y z hxy hyz
    apply squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ dist_triangle ((f^[n]) z) ((f^[n]) y) ((f^[n]) x))
    simpa only [add_zero] using hyz.add hxy

/-- If every point has a neighborhood related to it, all points of a preconnected space are
equivalent. -/
private theorem related_of_local {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (s : Setoid A)
    (hlocal : ∀ a : A, ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U, s a b)
    (a b : A) : s a b := by
  have hq : IsLocallyConstant (Quotient.mk s) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro a
    obtain ⟨U, hU, haU, hrel⟩ := hlocal a
    filter_upwards [hU.mem_nhds haU] with b hb
    exact Quotient.sound (s.symm (hrel b hb))
  exact Quotient.exact (hq.apply_eq_of_preconnectedSpace a b)

/-- A connected parametrized plaque is contained in one asymptotic class if it locally lifts into
native asymptotic carriers. -/
private theorem connected_plaque_sound_of_native_lifts
    {A M : Type*} [TopologicalSpace A] [PreconnectedSpace A] [MetricSpace M]
    (f : M ≃ₜ M) (h : A → M)
    (hlift : ∀ a : A, ∃ U : Set A, IsOpen U ∧ a ∈ U ∧
      ∃ ψ : U → StableAsymptoticLeaf f (h a), ∀ b : U, (ψ b).val = h b.val)
    (a b : A) : ForwardAsymptotic f (h a) (h b) := by
  let s : Setoid A := ⟨fun a b ↦ ForwardAsymptotic f (h a) (h b),
    ⟨fun a ↦ (asymptotic_equivalence f).refl (h a),
      fun hab ↦ (asymptotic_equivalence f).symm hab,
      fun hab hbc ↦ (asymptotic_equivalence f).trans hab hbc⟩⟩
  apply related_of_local s ?_ a b
  intro a
  obtain ⟨U, hU, haU, ψ, hψ⟩ := hlift a
  refine ⟨U, hU, haU, ?_⟩
  intro b hb
  change ForwardAsymptotic f (h a) (h b)
  have hmem := (ψ ⟨b, hb⟩).property
  simpa only [hψ] using hmem

/-- A parametrized complex foliation disk is contained in one asymptotic class if it locally lifts
into native asymptotic carriers. -/
private theorem complex_plaque_sound_of_native_lifts
    {M : Type*} [MetricSpace M] (r : ℕ) (f : M ≃ₜ M)
    (h : complexFoliationDisk r → M)
    (hlift : ∀ a : complexFoliationDisk r,
      ∃ U : Set (complexFoliationDisk r), IsOpen U ∧ a ∈ U ∧
        ∃ ψ : U → StableAsymptoticLeaf f (h a), ∀ b : U, (ψ b).val = h b.val)
    (a b : complexFoliationDisk r) : ForwardAsymptotic f (h a) (h b) := by
  let : PreconnectedSpace (complexFoliationDisk r) :=
    isPreconnected_iff_preconnectedSpace.mp
      (Metric.isConnected_ball (x := (0 : ComplexModel r)) (r := 1)
        zero_lt_one).isPreconnected
  exact connected_plaque_sound_of_native_lifts f h hlift a b

/-- The setoid of forward asymptotic equivalence for `f`. -/
private def asymptoticSetoid {M : Type*} [MetricSpace M] (f : M ≃ₜ M) : Setoid M :=
  ⟨ForwardAsymptotic f, asymptotic_equivalence f⟩

/-- The relation of lying in the same horizontal slice of a product box. (Nisoli, Defs. 1.1.1–1.1.3,
pp.9–10) -/
private def sameBoxSlice {M J : Type*} [TopologicalSpace M] (r c : ℕ)
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (x y : M) : Prop :=
  ∃ i, ∃ w : complexFoliationDisk c, ∃ a b : complexFoliationDisk r,
    (box i).symm (a.val, w.val) = x ∧ (box i).symm (b.val, w.val) = y

/-- Native inverse plaque charts yield coordinate-open local lifts of each product-box slice. -/
private theorem slice_lifts_of_native_inverse_charts
    {E H M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [MetricSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (f : M ≃ₜ M) (P : RealTangentDistribution I M)
    (D : ∀ x, NativeAsymptoticLeafDatum I f P x) (r c : ℕ)
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (hcharts : ∀ i (w : complexFoliationDisk c) (a : complexFoliationDisk r),
      let x := (box i).symm (a.val, w.val)
      letI := (D x).topology
      ∃ k : OpenPartialHomeomorph (StableAsymptoticLeaf f x) (ComplexModel r),
        (⟨x, (asymptotic_equivalence f).refl x⟩ : StableAsymptoticLeaf f x) ∈ k.source ∧
        k ⟨x, (asymptotic_equivalence f).refl x⟩ = a.val ∧
        ∀ u ∈ k.target, (k.symm u).val = (box i).symm (u, w.val)) :
    ∀ i (w : complexFoliationDisk c) (a : complexFoliationDisk r),
      ∃ U : Set (complexFoliationDisk r), IsOpen U ∧ a ∈ U ∧
        ∃ ψ : U → StableAsymptoticLeaf f ((box i).symm (a.val, w.val)),
          ∀ b : U, (ψ b).val = (box i).symm (b.val.val, w.val) := by
  intro i w a
  let x := (box i).symm (a.val, w.val)
  let := (D x).topology
  obtain ⟨k, hak, hka, hfactor⟩ := hcharts i w a
  let U : Set (complexFoliationDisk r) := Subtype.val ⁻¹' k.target
  refine ⟨U, k.open_target.preimage continuous_subtype_val, ?_,
    (fun b ↦ k.symm b.val.val), ?_⟩
  · change a.val ∈ k.target
    exact (congrArg (fun u : ComplexModel r ↦ u ∈ k.target) hka).mp (k.map_source hak)
  · intro b
    exact hfactor b.val.val b.property

/-- Locally constant transverse coordinates on native leaves give intrinsic neighborhoods lying in a
single product-box slice. -/
private theorem same_slice_neighbourhoods_of_transverse_constant
    {E H M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [MetricSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (f : M ≃ₜ M) (P : RealTangentDistribution I M)
    (D : ∀ x, NativeAsymptoticLeafDatum I f P x) (r c : ℕ)
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (htarget : ∀ i, (box i).target =
      (complexFoliationDisk r : Set _) ×ˢ (complexFoliationDisk c : Set _))
    (hcover : ∀ z : M, ∃ i, z ∈ (box i).source)
    (hconstant : ∀ x i, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x, a.val ∈ (box i).source →
        ∃ W : Set (StableAsymptoticLeaf f x), IsOpen W ∧ a ∈ W ∧
          W ⊆ Subtype.val ⁻¹' (box i).source ∧
            ∀ b ∈ W, (box i b.val).2 = (box i a.val).2) :
    ∀ x, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x,
        ∃ W : Set (StableAsymptoticLeaf f x), IsOpen W ∧ a ∈ W ∧
          ∀ b ∈ W, sameBoxSlice r c box a.val b.val := by
  intro x
  let := (D x).topology
  intro a
  obtain ⟨i, hai⟩ := hcover a.val
  obtain ⟨W, hW, haW, hsource, htrans⟩ := hconstant x i a hai
  refine ⟨W, hW, haW, ?_⟩
  intro b hb
  have hbi := hsource hb
  have haT := (box i).map_source hai
  have hbT := (box i).map_source hbi
  rw [htarget] at haT hbT
  refine ⟨i, ⟨(box i a.val).2, haT.2⟩, ⟨(box i a.val).1, haT.1⟩,
    ⟨(box i b.val).1, hbT.1⟩, ?_, ?_⟩
  · exact (box i).left_inv hai
  · change (box i).symm ((box i b.val).1, (box i a.val).2) = b.val
    rw [← htrans b hb]
    exact (box i).left_inv hbi

/-- The asymptotic partition is the equivalence relation generated by the product-box slices. -/
private theorem asymptotic_partition_generated
    {E H M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [MetricSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (f : M ≃ₜ M) (P : RealTangentDistribution I M)
    (D : ∀ x, NativeAsymptoticLeafDatum I f P x) (r c : ℕ)
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (hlift : ∀ i (w : complexFoliationDisk c) (a : complexFoliationDisk r),
      ∃ U : Set (complexFoliationDisk r), IsOpen U ∧ a ∈ U ∧
        ∃ ψ : U → StableAsymptoticLeaf f ((box i).symm (a.val, w.val)),
          ∀ b : U, (ψ b).val = (box i).symm (b.val.val, w.val))
    (hlocal : ∀ x, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x,
        ∃ W : Set (StableAsymptoticLeaf f x), IsOpen W ∧ a ∈ W ∧
          ∀ b ∈ W, sameBoxSlice r c box a.val b.val)
    (x y : M) : asymptoticSetoid f x y ↔ Relation.EqvGen (sameBoxSlice r c box) x y := by
  have hsound : ∀ a b, sameBoxSlice r c box a b → ForwardAsymptotic f a b := by
    rintro a b ⟨i, w, u, v, rfl, rfl⟩
    exact complex_plaque_sound_of_native_lifts r f
      (fun u ↦ (box i).symm (u.val, w.val)) (hlift i w) u v
  constructor
  · intro h
    let := (D x).topology
    let := (D x).connected
    let s : Setoid (StableAsymptoticLeaf f x) :=
      ⟨fun a b ↦ Relation.EqvGen (sameBoxSlice r c box) a.val b.val,
        ⟨fun a ↦ Relation.EqvGen.refl a.val,
          fun h ↦ Relation.EqvGen.symm _ _ h,
          fun h₁ h₂ ↦ Relation.EqvGen.trans _ _ _ h₁ h₂⟩⟩
    apply related_of_local s ?_ ⟨x, (asymptotic_equivalence f).refl x⟩ ⟨y, h⟩
    intro a
    obtain ⟨W, hW, haW, hstep⟩ := hlocal x a
    exact ⟨W, hW, haW, fun b hb ↦ Relation.EqvGen.rel _ _ (hstep b hb)⟩
  · intro h
    exact (asymptotic_equivalence f).eqvGen_iff.mp (Relation.EqvGen.mono hsound x y h)

/-- The zero point of the complex foliation disk. -/
private def diskZero (r : ℕ) : complexFoliationDisk r :=
  ⟨0, Metric.mem_ball_self zero_lt_one⟩

/-- The quotient label of a slice is the asymptotic class of its horizontal zero point. -/
private def sliceLabel {M J : Type*} [MetricSpace M] (r c : ℕ) (f : M ≃ₜ M)
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (i : J) (w : complexFoliationDisk c) : Quotient (asymptoticSetoid f) :=
  Quotient.mk _ ((box i).symm ((diskZero r).val, w.val))

/-- The quotient label of a product-box slice is independent of its horizontal coordinate. -/
private theorem slice_label_eq {M J : Type*} [MetricSpace M] (r c : ℕ) (f : M ≃ₜ M)
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (hlift : ∀ i (w : complexFoliationDisk c) (a : complexFoliationDisk r),
      ∃ U : Set (complexFoliationDisk r), IsOpen U ∧ a ∈ U ∧
        ∃ ψ : U → StableAsymptoticLeaf f ((box i).symm (a.val, w.val)),
          ∀ b : U, (ψ b).val = (box i).symm (b.val.val, w.val))
    (i : J) (a : complexFoliationDisk r) (w : complexFoliationDisk c) :
    Quotient.mk (asymptoticSetoid f) ((box i).symm (a.val, w.val)) =
      sliceLabel r c f box i w := by
  apply Quotient.sound
  exact complex_plaque_sound_of_native_lifts r f
    (fun u ↦ (box i).symm (u.val, w.val)) (hlift i w) a (diskZero r)

/-- The point-preserving equivalence between a native asymptotic carrier and its quotient-class
carrier. -/
private def nativeCarrierEquiv {M : Type*} [MetricSpace M] (f : M ≃ₜ M) (x : M) :
    IntrinsicFoliationLeaf (asymptoticSetoid f) (Quotient.mk (asymptoticSetoid f) x) ≃
      StableAsymptoticLeaf f x where
  toFun y := ⟨y.val, (asymptotic_equivalence f).symm (Quotient.exact y.property)⟩
  invFun y := ⟨y.val, Quotient.sound ((asymptotic_equivalence f).symm y.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The native carrier equivalence preserves the ambient value of each point. -/
private theorem nativeCarrierEquiv_val {M : Type*} [MetricSpace M] (f : M ≃ₜ M) (x : M)
    (y : IntrinsicFoliationLeaf (asymptoticSetoid f)
      (Quotient.mk (asymptoticSetoid f) x)) : (nativeCarrierEquiv f x y).val = y.val := rfl

end
end HolomorphicAnosov.NativeBoxPartition


/-! Transitions between product charts flattening the same tangent distribution have locally
constant transverse components along horizontal slices. (Nisoli, Defs. 1.1.1–1.1.3, pp.9–10) -/

open Set

namespace HolomorphicAnosov.FrobeniusSupport

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

section ManifoldCharts

open scoped Manifold ContDiff

variable {A H M : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ A H)

/-- Two differentiable product charts flattening the same tangent distribution satisfy the local
transverse overlap law. (Nisoli, Defs. 1.1.1–1.1.3, pp.9–10) -/
private theorem product_charts_transverse_overlap
    (P : ∀ x : M, Submodule ℂ (TangentSpace I x))
    (e₁ e₂ : OpenPartialHomeomorph M (E × F))
    (he₁ : e₁.MDifferentiable I 𝓘(ℂ, E × F))
    (he₂ : e₂.MDifferentiable I 𝓘(ℂ, E × F))
    (hflat₁ : ∀ x ∈ e₁.source,
      (P x).map (mfderiv I 𝓘(ℂ, E × F) e₁ x).toLinearMap =
        (ContinuousLinearMap.inl ℂ E F).toLinearMap.range)
    (hflat₂ : ∀ x ∈ e₂.source,
      (P x).map (mfderiv I 𝓘(ℂ, E × F) e₂ x).toLinearMap =
        (ContinuousLinearMap.inl ℂ E F).toLinearMap.range)
    {z : E × F} (hz₁ : z ∈ e₁.target) (hz₂ : e₁.symm z ∈ e₂.source) :
    ∃ W : Set (E × F), IsOpen W ∧ z ∈ W ∧
      W ⊆ e₁.target ∩ e₁.symm ⁻¹' e₂.source ∧
      ∀ a ∈ W, ∀ b ∈ W, a.2 = b.2 →
        (e₂ (e₁.symm a)).2 = (e₂ (e₁.symm b)).2 := by
  let U := e₁.target ∩ e₁.symm ⁻¹' e₂.source
  have hU : IsOpen U :=
    e₁.continuousOn_symm.isOpen_inter_preimage e₁.open_target e₂.open_source
  let t : E × F → E × F := e₂ ∘ e₁.symm
  have ht : ∀ q ∈ U, MDifferentiableAt 𝓘(ℂ, E × F) 𝓘(ℂ, E × F) t q := by
    intro q hq
    exact (he₂.mdifferentiableAt hq.2).comp q (he₁.mdifferentiableAt_symm hq.1)
  have ht' : DifferentiableOn ℂ t U :=
    fun q hq ↦ (ht q hq).differentiableAt.differentiableWithinAt
  have hzero : ∀ q ∈ U, ∀ v : E, fderiv ℂ (fun q ↦ (t q).2) q (v, 0) = 0 := by
    intro q hq v
    let x := e₁.symm q
    let D₁ := mfderiv I 𝓘(ℂ, E × F) e₁ x
    let D₂ := mfderiv I 𝓘(ℂ, E × F) e₂ x
    let Dinv := mfderiv 𝓘(ℂ, E × F) I e₁.symm q
    have hx₁ : x ∈ e₁.source := e₁.map_target hq.1
    have hmap₁ : (v, (0 : F)) ∈ (P x).map D₁.toLinearMap := by
      rw [hflat₁ x hx₁]
      exact ⟨v, rfl⟩
    obtain ⟨u, hu, hDu⟩ := hmap₁
    have hinv : D₁ (Dinv (v, 0)) = (v, 0) :=
      congrArg (fun L : (E × F) →L[ℂ] (E × F) ↦ L (v, 0))
        (he₁.comp_symm_deriv hq.1)
    have hmem : Dinv (v, 0) ∈ P x := by
      have heq : Dinv (v, 0) = u := (he₁.mfderiv_injective hx₁) (hinv.trans hDu.symm)
      rwa [heq]
    have hmap₂ : D₂ (Dinv (v, 0)) ∈
        (ContinuousLinearMap.inl ℂ E F).toLinearMap.range := by
      rw [← hflat₂ x hq.2]
      exact ⟨Dinv (v, 0), hmem, rfl⟩
    obtain ⟨w, hw⟩ := hmap₂
    have htrans : fderiv ℂ t q = D₂.comp Dinv := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp q (he₂.mdifferentiableAt hq.2)
        (he₁.mdifferentiableAt_symm hq.1)
    rw [(ht q hq).differentiableAt.hasFDerivAt.snd.fderiv, htrans]
    change (D₂ (Dinv (v, 0))).2 = 0
    exact (congrArg Prod.snd hw).symm
  obtain ⟨ε, hε, hsub, hconst⟩ := HolomorphicAnosov.FrobeniusSupport.exists_product_ball_transverse_independent hU
    (fun q ↦ (t q).2) ht'.snd hzero ⟨hz₁, hz₂⟩
  refine ⟨Metric.ball z.1 ε ×ˢ Metric.ball z.2 ε,
    Metric.isOpen_ball.prod Metric.isOpen_ball, ⟨Metric.mem_ball_self hε,
      Metric.mem_ball_self hε⟩, hsub, ?_⟩
  exact hconst


/-- Two holomorphic product charts flattening the same tangent distribution satisfy the local
transverse overlap law. -/
private theorem holomorphic_product_charts_transverse_overlap
    (P : ∀ x : M, Submodule ℂ (TangentSpace I x))
    (e₁ e₂ : OpenPartialHomeomorph M (E × F))
    (he₁ : ContMDiffOn I (𝓘(ℂ, E).prod 𝓘(ℂ, F)) ∞ e₁ e₁.source)
    (he₁inv : ContMDiffOn (𝓘(ℂ, E).prod 𝓘(ℂ, F)) I ∞ e₁.symm e₁.target)
    (he₂ : ContMDiffOn I (𝓘(ℂ, E).prod 𝓘(ℂ, F)) ∞ e₂ e₂.source)
    (he₂inv : ContMDiffOn (𝓘(ℂ, E).prod 𝓘(ℂ, F)) I ∞ e₂.symm e₂.target)
    (hflat₁ : ∀ x ∈ e₁.source,
      (P x).map (mfderiv I (𝓘(ℂ, E).prod 𝓘(ℂ, F)) e₁ x).toLinearMap =
        (ContinuousLinearMap.inl ℂ E F).toLinearMap.range)
    (hflat₂ : ∀ x ∈ e₂.source,
      (P x).map (mfderiv I (𝓘(ℂ, E).prod 𝓘(ℂ, F)) e₂ x).toLinearMap =
        (ContinuousLinearMap.inl ℂ E F).toLinearMap.range)
    {z : E × F} (hz₁ : z ∈ e₁.target) (hz₂ : e₁.symm z ∈ e₂.source) :
    ∃ W : Set (E × F), IsOpen W ∧ z ∈ W ∧
      W ⊆ e₁.target ∩ e₁.symm ⁻¹' e₂.source ∧
      ∀ a ∈ W, ∀ b ∈ W, a.2 = b.2 →
        (e₂ (e₁.symm a)).2 = (e₂ (e₁.symm b)).2 := by
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at he₁ he₁inv he₂ he₂inv hflat₁ hflat₂

  let : ChartedSpace (ModelProd E F) (E × F) := chartedSpaceSelf (E × F)
  exact product_charts_transverse_overlap I P e₁ e₂
    ⟨he₁.mdifferentiableOn (by simp), he₁inv.mdifferentiableOn (by simp)⟩
    ⟨he₂.mdifferentiableOn (by simp), he₂inv.mdifferentiableOn (by simp)⟩
    hflat₁
    hflat₂
    hz₁ hz₂


end ManifoldCharts

end HolomorphicAnosov.FrobeniusSupport


/-! Transverse coordinates annihilating the native leaf tangent distribution are locally constant on
intrinsic leaf neighborhoods. -/

open Topology _root_.Topology Set
open scoped ContDiff

namespace HolomorphicAnosov.Theorem12PlaqueSupport

variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
variable (I : ModelWithCorners ℝ E H)

/-- A transverse coordinate with zero leaf derivative is constant on an intrinsic coordinate ball
inside its ambient domain. -/
private theorem exists_native_open_constant
    [IsManifold (modelWithCornersSelf ℝ G) ∞ N]
    (j : N → M) (hj : Continuous j) (τ : M → F) (V : Set M) (hV : IsOpen V)
    (hf : ∀ z, j z ∈ V →
      MDifferentiableAt (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ F) (τ ∘ j) z)
    (hzero : ∀ z, j z ∈ V →
      mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ F) (τ ∘ j) z = 0)
    (a : N) (ha : j a ∈ V) :
    ∃ W : Set N, IsOpen W ∧ a ∈ W ∧ W ⊆ j ⁻¹' V ∧
      ∀ z ∈ W, τ (j z) = τ (j a) := by
  let c := chartAt G a
  have hac : a ∈ c.source := mem_chart_source G a
  have hct : c a ∈ c.target := c.map_source hac
  have hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ G) ∞ N :=
    IsManifold.chart_mem_maximalAtlas a
  let T : Set G := c.target ∩ (j ∘ c.symm) ⁻¹' V
  have hT : IsOpen T :=
    (hj.comp_continuousOn c.continuousOn_symm).isOpen_inter_preimage c.open_target hV
  have haT : c a ∈ T := ⟨hct, by simpa only [Set.mem_preimage, Function.comp_apply, c.left_inv hac] using ha⟩
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.mp hT (c a) haT
  let g : G → F := (τ ∘ j) ∘ c.symm
  have hgd : ∀ t ∈ Metric.ball (c a) ε, DifferentiableAt ℝ g t := by
    intro t ht
    have htT := hεT ht
    have hc' : MDifferentiableAt (modelWithCornersSelf ℝ G)
        (modelWithCornersSelf ℝ G) c.symm t :=
      (contMDiffAt_symm_of_mem_maximalAtlas hc htT.1).mdifferentiableAt (by simp)
    exact ((hf (c.symm t) htT.2).comp t hc').differentiableAt
  have hgz : ∀ t ∈ Metric.ball (c a) ε, fderiv ℝ g t = 0 := by
    intro t ht
    have htT := hεT ht
    have hc' : MDifferentiableAt (modelWithCornersSelf ℝ G)
        (modelWithCornersSelf ℝ G) c.symm t :=
      (contMDiffAt_symm_of_mem_maximalAtlas hc htT.1).mdifferentiableAt (by simp)
    rw [← mfderiv_eq_fderiv]
    change mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ F)
      ((τ ∘ j) ∘ c.symm) t = 0
    rw [mfderiv_comp t (hf (c.symm t) htT.2) hc', hzero (c.symm t) htT.2]
    simp
  have hgconst : ∀ t ∈ Metric.ball (c a) ε, g t = g (c a) := by
    intro t ht
    exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero
      (convex_ball (c a) ε).isPreconnected (fun t ht ↦ (hgd t ht).differentiableWithinAt)
      (fun t ht ↦ hgz t ht) ht (Metric.mem_ball_self hε)
  let W : Set N := c.source ∩ c ⁻¹' Metric.ball (c a) ε
  refine ⟨W, c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball,
    ⟨hac, Metric.mem_ball_self hε⟩, ?_, ?_⟩
  · intro z hz
    have htz := (hεT hz.2).2
    simpa only [Set.mem_preimage, Function.comp_apply, c.left_inv hz.1] using htz
  · intro z hz
    have hh := hgconst (c z) hz.2
    simpa only [g, Function.comp_apply, c.left_inv hz.1, c.left_inv hac] using hh

section ProductChart

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The transverse coordinate derivative of a product chart flattening a distribution annihilates
that distribution. -/
private theorem product_chart_transverse_kills
    (e : OpenPartialHomeomorph M (A × F))
    (he : ContMDiffOn I (modelWithCornersSelf ℝ (A × F)) ∞ e e.source)
    (P : (x : M) → Submodule ℝ (TangentSpace I x))
    (hhor : ∀ z ∈ e.source, ∀ v ∈ P z,
      (mfderiv I (modelWithCornersSelf ℝ (A × F)) e z v).2 = 0)
    (z : M) (hz : z ∈ e.source) :
    MDifferentiableAt I (modelWithCornersSelf ℝ F) (fun x ↦ (e x).2) z ∧
      ∀ v ∈ P z,
        mfderiv I (modelWithCornersSelf ℝ F) (fun x ↦ (e x).2) z v = 0 := by
  have he' := (he.contMDiffAt (e.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have hsnd : MDifferentiableAt (modelWithCornersSelf ℝ (A × F))
      (modelWithCornersSelf ℝ F) Prod.snd (e z) :=
    (ContinuousLinearMap.snd ℝ A F).differentiableAt.mdifferentiableAt
  refine ⟨hsnd.comp z he', ?_⟩
  intro v hv
  change mfderiv I (modelWithCornersSelf ℝ F) (Prod.snd ∘ e) z v = 0
  rw [mfderiv_comp z hsnd he', mfderiv_eq_fderiv]
  change (fderiv ℝ (ContinuousLinearMap.snd ℝ A F) (e z))
    (mfderiv I (modelWithCornersSelf ℝ (A × F)) e z v) = 0
  rw [ContinuousLinearMap.fderiv]
  exact hhor z hz v hv

end ProductChart

section OriginalNative

variable {M₀ : Type*} [MetricSpace M₀] [ChartedSpace H M₀] [IsManifold I ∞ M₀]
variable (f : M₀ ≃ₜ M₀) (P : RealTangentDistribution I M₀) (x : M₀)

/-- A transverse coordinate annihilating the native tangent distribution is constant on an intrinsic
open neighborhood of each leaf point. -/
theorem nativeAsymptoticLeaf_transverse_locally_constant
    (D : NativeAsymptoticLeafDatum I f P x) (τ : M₀ → F) (V : Set M₀) (hV : IsOpen V)
    (hτ : ∀ z ∈ V, MDifferentiableAt I (modelWithCornersSelf ℝ F) τ z)
    (hkill : ∀ z ∈ V, ∀ v ∈ P z, mfderiv I (modelWithCornersSelf ℝ F) τ z v = 0) :
    letI : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
    ∀ a : StableAsymptoticLeaf f x, a.val ∈ V →
      ∃ W : Set (StableAsymptoticLeaf f x), IsOpen W ∧ a ∈ W ∧
        W ⊆ Subtype.val ⁻¹' V ∧ ∀ z ∈ W, τ z.val = τ a.val := by
  let : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
  let : ChartedSpace (Fin D.rank → ℝ) (StableAsymptoticLeaf f x) := D.charts
  let : IsManifold (modelWithCornersSelf ℝ (Fin D.rank → ℝ)) ∞
      (StableAsymptoticLeaf f x) := D.smoothAtlas
  intro a ha
  apply exists_native_open_constant Subtype.val D.inclusion_smooth.continuous τ V hV
    (fun z hz ↦ (hτ z.val hz).comp z (D.inclusion_smooth.mdifferentiable (by simp) z))
    _ a ha
  intro z hz
  exact HolomorphicAnosov.Theorem12PlaqueSupport.transverse_comp_mfderiv_zero I Subtype.val
    (D.inclusion_smooth.mdifferentiable (by simp)) P D.tangent_image τ
    (hτ z.val hz) (hkill z.val hz)

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- A native leaf has an intrinsic open neighborhood contained in a single horizontal product
plaque. -/
private theorem nativeAsymptoticLeaf_single_product_plaque
    (D : NativeAsymptoticLeafDatum I f P x)
    (e : OpenPartialHomeomorph M₀ (A × F))
    (he : ContMDiffOn I (modelWithCornersSelf ℝ (A × F)) ∞ e e.source)
    (hhor : ∀ z ∈ e.source, ∀ v ∈ P z,
      (mfderiv I (modelWithCornersSelf ℝ (A × F)) e z v).2 = 0) :
    letI : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
    ∀ a : StableAsymptoticLeaf f x, a.val ∈ e.source →
      ∃ W : Set (StableAsymptoticLeaf f x), IsOpen W ∧ a ∈ W ∧
        W ⊆ Subtype.val ⁻¹' e.source ∧
        ∀ z ∈ W, (e z.val).2 = (e a.val).2 := by
  apply nativeAsymptoticLeaf_transverse_locally_constant I f P x D
    (fun z ↦ (e z).2) e.source e.open_source
  · intro z hz
    exact (product_chart_transverse_kills I e he P hhor z hz).1
  · intro z hz
    exact (product_chart_transverse_kills I e he P hhor z hz).2

end OriginalNative


end HolomorphicAnosov.Theorem12PlaqueSupport



noncomputable section
open Topology _root_.Topology Set
open scoped ContDiff
namespace HolomorphicAnosov.Theorem12HorizontalSupport
variable {G A : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ G] [FiniteDimensional ℝ A]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold (modelWithCornersSelf ℝ G) ∞ N]

omit [FiniteDimensional ℝ A] in
/-- A function with invertible derivative in a preferred intrinsic chart defines a local chart
agreeing with that function. -/
private theorem native_horizontal_inverse
    (h : N → A) (a : N)
    (hh : ContMDiffAt (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A) ∞ h a)
    (hbij : Function.Bijective
      (mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A) h a))
    (W : Set N) (hW : IsOpen W) (haW : a ∈ W) :
    ∃ e : OpenPartialHomeomorph N A,
      a ∈ e.source ∧ e.source ⊆ W ∧ ∀ z ∈ e.source, e z = h z := by
  let c := chartAt G a
  have hac : a ∈ c.source := mem_chart_source G a
  have hct : c a ∈ c.target := c.map_source hac
  have hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ G) ∞ N :=
    IsManifold.chart_mem_maximalAtlas a
  have hcs := contMDiffAt_symm_of_mem_maximalAtlas hc hct
  let g : G → A := h ∘ c.symm
  have hg : ContDiffAt ℝ ∞ g (c a) := by
    have hh' : ContMDiffAt (modelWithCornersSelf ℝ G)
        (modelWithCornersSelf ℝ A) ∞ h (c.symm (c a)) := by
      simpa only [c.left_inv hac] using hh
    exact (hh'.comp (c a) hcs).contDiffAt
  have hgbij : Function.Bijective (fderiv ℝ g (c a)) := by
    rw [← mfderiv_eq_fderiv]
    change Function.Bijective
      (mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A)
        (h ∘ c.symm) (c a))
    rw [mfderiv_comp (c a)
      (by simpa only [c.left_inv hac] using hh.mdifferentiableAt (by simp))
      (hcs.mdifferentiableAt (by simp))]
    have hb : Function.Bijective
        (mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A) h (c.symm (c a))) := by
      rw [c.left_inv hac]
      exact hbij
    exact hb.comp
      ((mdifferentiable_chart (I := modelWithCornersSelf ℝ G) a).symm.mfderiv_bijective hct)
  let D : G ≃L[ℝ] A :=
    (LinearEquiv.ofBijective (fderiv ℝ g (c a)).toLinearMap hgbij).toContinuousLinearEquiv
  have hd : HasFDerivAt g (D : G →L[ℝ] A) (c a) :=
    hg.differentiableAt (by simp) |>.hasFDerivAt
  let R := hg.toOpenPartialHomeomorph g hd (by simp)
  have haR : c a ∈ R.source := hg.mem_toOpenPartialHomeomorph_source hd (by simp)
  let e := (c.trans R).restrOpen W hW
  refine ⟨e, ⟨⟨hac, haR⟩, haW⟩, fun _ hz ↦ hz.2, ?_⟩
  intro z hz
  change g (c z) = h z
  exact congrArg h (c.left_inv hz.1.1)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H)

omit [IsManifold (modelWithCornersSelf ℝ G) ∞ N] in
/-- The horizontal derivative of a flattened product chart composed with the native inclusion is
bijective. -/
private theorem horizontal_mfderiv_bijective
    (j : N → M) (hj : ContMDiff (modelWithCornersSelf ℝ G) I ∞ j)
    (P : (z : M) → Submodule ℝ (TangentSpace I z))
    (hP : ∀ z, LinearMap.range
      (mfderiv (modelWithCornersSelf ℝ G) I j z).toLinearMap = P (j z))
    (hji : ∀ z, Function.Injective (mfderiv (modelWithCornersSelf ℝ G) I j z))
    (e : OpenPartialHomeomorph M (A × F))
    (he : ContMDiffOn I (modelWithCornersSelf ℝ (A × F)) ∞ e e.source)
    (hei : ContMDiffOn (modelWithCornersSelf ℝ (A × F)) I ∞ e.symm e.target)
    (hhor : ∀ z ∈ e.source, ∀ v ∈ P z,
      (mfderiv I (modelWithCornersSelf ℝ (A × F)) e z v).2 = 0)
    (T : G ≃L[ℝ] A) (a : N) (ha : j a ∈ e.source) :
    Function.Bijective (mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A)
      (fun z ↦ (e (j z)).1) a) := by
  have hj' := hj.mdifferentiable (by simp)
  have he' := (he.contMDiffAt (e.open_source.mem_nhds ha)).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt (modelWithCornersSelf ℝ (A × F))
      (modelWithCornersSelf ℝ A) Prod.fst (e (j a)) :=
    (ContinuousLinearMap.fst ℝ A F).differentiableAt.mdifferentiableAt
  have hder : ∀ v,
      mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A)
        (fun z ↦ (e (j z)).1) a v =
      (mfderiv I (modelWithCornersSelf ℝ (A × F)) e (j a)
        (mfderiv (modelWithCornersSelf ℝ G) I j a v)).1 := by
    intro v
    change mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A)
      (Prod.fst ∘ (e ∘ j)) a v = _
    rw [mfderiv_comp a hf (he'.comp a (hj' a)), mfderiv_comp a he' (hj' a),
      mfderiv_eq_fderiv]
    change (fderiv ℝ (ContinuousLinearMap.fst ℝ A F) (e (j a)))
      (mfderiv I (modelWithCornersSelf ℝ (A × F)) e (j a)
        (mfderiv (modelWithCornersSelf ℝ G) I j a v)) = _
    rw [ContinuousLinearMap.fderiv]
    rfl
  have hsec : ∀ v,
      (mfderiv I (modelWithCornersSelf ℝ (A × F)) e (j a)
        (mfderiv (modelWithCornersSelf ℝ G) I j a v)).2 = 0 := by
    intro v
    apply hhor (j a) ha
    rw [← hP a]
    exact ⟨v, rfl⟩
  have heMD : e.MDifferentiable I (modelWithCornersSelf ℝ (A × F)) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinj : Function.Injective
      (mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A)
        (fun z ↦ (e (j z)).1) a) := by
    intro v w hvw
    apply hji a
    apply heMD.mfderiv_injective ha
    apply Prod.ext
    · exact (hder v).symm.trans (hvw.trans (hder w))
    · rw [hsec v, hsec w]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    T.toLinearEquiv.finrank_eq).mp hinj⟩

/-- The horizontal product coordinate defines an intrinsic plaque chart whose inverse agrees with
the ambient box inverse on a fixed transverse slice. -/
private theorem native_product_plaque_chart
    (j : N → M) (hj : ContMDiff (modelWithCornersSelf ℝ G) I ∞ j)
    (P : (z : M) → Submodule ℝ (TangentSpace I z))
    (hP : ∀ z, LinearMap.range
      (mfderiv (modelWithCornersSelf ℝ G) I j z).toLinearMap = P (j z))
    (hji : ∀ z, Function.Injective (mfderiv (modelWithCornersSelf ℝ G) I j z))
    (e : OpenPartialHomeomorph M (A × F))
    (he : ContMDiffOn I (modelWithCornersSelf ℝ (A × F)) ∞ e e.source)
    (hei : ContMDiffOn (modelWithCornersSelf ℝ (A × F)) I ∞ e.symm e.target)
    (hhor : ∀ z ∈ e.source, ∀ v ∈ P z,
      (mfderiv I (modelWithCornersSelf ℝ (A × F)) e z v).2 = 0)
    (T : G ≃L[ℝ] A) (a : N) (ha : j a ∈ e.source) :
    ∃ c : OpenPartialHomeomorph N A,
      a ∈ c.source ∧ (∀ z ∈ c.source, j z ∈ e.source ∧ c z = (e (j z)).1) ∧
      ∀ u ∈ c.target,
        (u, (e (j a)).2) ∈ e.target ∧
          j (c.symm u) = e.symm (u, (e (j a)).2) := by
  have hτ : ∀ z ∈ e.source,
      MDifferentiableAt I (modelWithCornersSelf ℝ F) (fun z ↦ (e z).2) z := by
    intro z hz
    exact (Theorem12PlaqueSupport.product_chart_transverse_kills I e he P hhor z hz).1
  have hkill : ∀ z ∈ e.source, ∀ v ∈ P z,
      mfderiv I (modelWithCornersSelf ℝ F) (fun z ↦ (e z).2) z v = 0 := by
    intro z hz
    exact (Theorem12PlaqueSupport.product_chart_transverse_kills I e he P hhor z hz).2
  obtain ⟨W, hW, haW, hWV, hconstant⟩ :=
    Theorem12PlaqueSupport.exists_native_open_constant j hj.continuous
      (fun z ↦ (e z).2) e.source e.open_source
      (fun z hz ↦ (hτ (j z) hz).comp z (hj.mdifferentiable (by simp) z))
      (fun z hz ↦ HolomorphicAnosov.Theorem12PlaqueSupport.transverse_comp_mfderiv_zero I j
        (hj.mdifferentiable (by simp)) P hP (fun z ↦ (e z).2)
        (hτ (j z) hz) (hkill (j z) hz)) a ha
  let h : N → A := fun z ↦ (e (j z)).1
  have hh : ContMDiffAt (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ A) ∞ h a :=
    (ContinuousLinearMap.fst ℝ A F).contDiff.contDiffAt.comp_contMDiffAt
      ((he.contMDiffAt (e.open_source.mem_nhds ha)).comp a (hj a))
  obtain ⟨c, hac, hcW, hch⟩ := native_horizontal_inverse h a hh
    (horizontal_mfderiv_bijective I j hj P hP hji e he hei hhor T a ha) W hW haW
  refine ⟨c, hac, fun z hz ↦ ⟨hWV (hcW hz), hch z hz⟩, ?_⟩
  intro u hu
  have hcu : c.symm u ∈ c.source := c.map_target hu
  have hw : c.symm u ∈ W := hcW hcu
  have hv : j (c.symm u) ∈ e.source := hWV hw
  have hfirst : (e (j (c.symm u))).1 = u :=
    (hch (c.symm u) hcu).symm.trans (c.right_inv hu)
  have hpair : e (j (c.symm u)) = (u, (e (j a)).2) :=
    Prod.ext hfirst (hconstant _ hw)
  refine ⟨?_, ?_⟩
  · rw [← hpair]
    exact e.map_source hv
  · exact (e.left_inv hv).symm.trans (congrArg e.symm hpair)

section OriginalNative
variable {M₀ : Type*} [MetricSpace M₀] [ChartedSpace H M₀] [IsManifold I ∞ M₀]
variable (f : M₀ ≃ₜ M₀) (P : RealTangentDistribution I M₀) (x : M₀)
/-- A native asymptotic leaf admits local horizontal product-plaque charts in its intrinsic
topology. -/
private theorem nativeAsymptoticLeaf_product_plaque_chart
    (D : NativeAsymptoticLeafDatum I f P x)
    (T : (Fin D.rank → ℝ) ≃L[ℝ] A)
    (e : OpenPartialHomeomorph M₀ (A × F))
    (he : ContMDiffOn I (modelWithCornersSelf ℝ (A × F)) ∞ e e.source)
    (hei : ContMDiffOn (modelWithCornersSelf ℝ (A × F)) I ∞ e.symm e.target)
    (hhor : ∀ z ∈ e.source, ∀ v ∈ P z,
      (mfderiv I (modelWithCornersSelf ℝ (A × F)) e z v).2 = 0) :
    letI : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
    ∀ a : StableAsymptoticLeaf f x, a.val ∈ e.source →
      ∃ c : OpenPartialHomeomorph (StableAsymptoticLeaf f x) A,
        a ∈ c.source ∧
        (∀ z ∈ c.source, z.val ∈ e.source ∧ c z = (e z.val).1) ∧
        ∀ u ∈ c.target, (u, (e a.val).2) ∈ e.target ∧
          (c.symm u).val = e.symm (u, (e a.val).2) := by
  let : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
  let : ChartedSpace (Fin D.rank → ℝ) (StableAsymptoticLeaf f x) := D.charts
  let : IsManifold (modelWithCornersSelf ℝ (Fin D.rank → ℝ)) ∞
      (StableAsymptoticLeaf f x) := D.smoothAtlas
  intro a ha
  exact native_product_plaque_chart I Subtype.val D.inclusion_smooth P D.tangent_image
    (fun z ↦ (D.inclusion_immersion z).mfderiv_injective (by simp)) e he hei hhor T a ha
end OriginalNative

end HolomorphicAnosov.Theorem12HorizontalSupport

noncomputable section
open scoped ContDiff Manifold
open Module
namespace HolomorphicAnosov.NativeLeafRankScratch

variable {V W : Type*} [AddCommGroup V] [TopologicalSpace V] [Module ℂ V]
  [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup W] [TopologicalSpace W] [Module ℝ W]

/-- An injective real derivative with prescribed complex tangent image determines a real frame
equivalence with the complex fibre coordinates. -/
private theorem derivative_frame_equiv {n r : ℕ}
    (D : (Fin n → ℝ) →L[ℝ] W) (hD : Function.Injective D)
    (P : Submodule ℂ V) (e : V ≃L[ℝ] W)
    (b : (Fin r → ℂ) ≃ₗ[ℂ] P)
    (hrange : D.toLinearMap.range =
      (P.restrictScalars ℝ).map e.toLinearEquiv.toLinearMap) :
    ∃ T : (Fin n → ℝ) ≃L[ℝ] (Fin r → ℂ),
      (∀ v, D v = e (b (T v))) ∧ n = 2 * r := by
  let A := LinearEquiv.ofInjective D.toLinearMap hD
  let B := LinearEquiv.ofEq _ _ hrange
  let C := Submodule.equivMapOfInjective e.toLinearEquiv.toLinearMap e.injective
    (P.restrictScalars ℝ)
  let T₀ : (Fin n → ℝ) ≃ₗ[ℝ] (Fin r → ℂ) :=
    ((A.trans B).trans C.symm).trans (b.restrictScalars ℝ).symm
  let T := T₀.toContinuousLinearEquiv
  refine ⟨T, ?_, ?_⟩
  · intro v
    change D v = e (b ((b.restrictScalars ℝ).symm (C.symm (B (A v)))))
    rw [show b ((b.restrictScalars ℝ).symm (C.symm (B (A v)))) =
      C.symm (B (A v)) from (b.restrictScalars ℝ).apply_symm_apply _]
    exact (Submodule.map_equivMapOfInjective_symm_apply
      e.toLinearEquiv.toLinearMap e.injective (P.restrictScalars ℝ) (B (A v))).symm
  · have h := T₀.finrank_eq
    have hdim : Module.finrank ℝ (Fin r → ℂ) = 2 * r := by
      rw [← Module.finrank_mul_finrank ℝ ℂ (Fin r → ℂ)]
      simp [Complex.finrank_real_complex]
    simpa [hdim] using h


variable {d r : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  [IsManifold (realModel d) ∞ M]

omit [IsManifold (complexModel d) ∞ M] in
/-- A complex frame spanning the native tangent image determines a real frame equivalence for the
native leaf tangent space. -/
private theorem native_leaf_frame_equiv {f : M ≃ₜ M}
    {Q : RealTangentDistribution (realModel d) M} {x : M}
    (N : NativeAsymptoticLeafDatum (realModel d) f Q x)
    (z : StableAsymptoticLeaf f x)
    (P : Submodule ℂ (TangentSpace (complexModel d) z.val))
    (s : Fin r → TangentSpace (complexModel d) z.val)
    (hli : LinearIndependent ℂ s) (hspan : Submodule.span ℂ (Set.range s) = P)
    (hbind : (P.restrictScalars ℝ).map
      (complexTangentToReal d z.val).toLinearEquiv.toLinearMap = Q z.val) :
    letI := N.topology
    letI := N.charts
    ∃ T : (Fin N.rank → ℝ) ≃L[ℝ] (Fin r → ℂ),
      (∀ v, mfderiv 𝓘(ℝ, Fin N.rank → ℝ) (realModel d)
        (Subtype.val : StableAsymptoticLeaf f x → M) z v =
          complexTangentToReal d z.val (∑ i, T v i • s i)) ∧ N.rank = 2 * r := by
  let _ := N.topology
  let _ := N.charts
  let b : (Fin r → ℂ) ≃ₗ[ℂ] P :=
    (Basis.span hli).equivFun.symm.trans (LinearEquiv.ofEq _ _ hspan)
  let D := mfderiv 𝓘(ℝ, Fin N.rank → ℝ) (realModel d)
    (Subtype.val : StableAsymptoticLeaf f x → M) z
  have hi : Function.Injective D :=
    (N.inclusion_immersion z).mfderiv_injective (by simp)
  have hR : D.toLinearMap.range = (P.restrictScalars ℝ).map
      (complexTangentToReal d z.val).toLinearEquiv.toLinearMap :=
    (N.tangent_image z).trans hbind.symm
  obtain ⟨T, hT, hr⟩ := derivative_frame_equiv
    (V := TangentSpace (complexModel d) z.val)
    (W := TangentSpace (realModel d) z.val) (n := N.rank) (r := r)
    D hi P (complexTangentToReal d z.val) b hR
  refine ⟨T, ?_, hr⟩
  intro v
  convert hT v using 1
  congr 1
  simp [b, Basis.equivFun_symm_apply]


/-- The real rank of a native leaf tangent to a complex rank-`r` subbundle is `2 * r`. -/
private theorem native_leaf_rank {f : M ≃ₜ M}
    {Q : RealTangentDistribution (realModel d) M} {x : M}
    (N : NativeAsymptoticLeafDatum (realModel d) f Q x)
    (P : (y : M) → Submodule ℂ (TangentSpace (complexModel d) y))
    (hP : IsHolomorphicTangentSubbundle r P)
    (hbind : ∀ y, ((P y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = Q y) :
    N.rank = 2 * r := by
  obtain ⟨U, s, hx, hs, hspan⟩ := hP x
  have hself : ForwardAsymptotic f x x := by
    simp [ForwardAsymptotic]
  let z : StableAsymptoticLeaf f x := ⟨x, hself⟩
  obtain ⟨T, hT, hr⟩ := native_leaf_frame_equiv N z (P x) (fun i ↦ s i x)
    (hs.2.2 x hx) (hspan x hx) (hbind x)
  exact hr


end HolomorphicAnosov.NativeLeafRankScratch

end

/-! Holomorphic product-box maps and their inverses are real smooth, with derivatives compatible
with scalar restriction. -/
namespace HolomorphicAnosov.Theorem12HolomorphicPlaqueSupport
open scoped ContDiff Manifold
open Set
noncomputable section
variable {d r c : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M]

/-- A holomorphic map to a complex product model is real smooth after restricting scalars. -/
private theorem holomorphic_product_box_real_smooth
    {e : M → ComplexModel r × ComplexModel c} {S : Set M}
    (he : ContMDiffOn (complexModel d)
      (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) ∞ e S) :
    ContMDiffOn (realModel d)
      (modelWithCornersSelf ℝ (ComplexModel r × ComplexModel c)) ∞ e S := by
  intro z hz
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (he z hz)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

/-- A holomorphic map from a complex product model is real smooth after restricting scalars. -/
private theorem holomorphic_product_box_inverse_real_smooth
    {e : ComplexModel r × ComplexModel c → M} {S : Set (ComplexModel r × ComplexModel c)}
    (he : ContMDiffOn (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c))
      (complexModel d) ∞ e S) :
    ContMDiffOn (modelWithCornersSelf ℝ (ComplexModel r × ComplexModel c))
      (realModel d) ∞ e S := by
  intro z hz
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (he z hz)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

/-- The real derivative of a holomorphic product-box map agrees with its complex derivative under
the complex-to-real tangent identification. -/
private theorem product_box_mfderiv_complex_to_real
    {e : M → ComplexModel r × ComplexModel c} {z : M}
    (he : MDifferentiableAt (complexModel d)
      (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) e z)
    (v : TangentSpace (complexModel d) z) :
    mfderiv (realModel d) (modelWithCornersSelf ℝ (ComplexModel r × ComplexModel c))
      e z (complexTangentToReal d z v) =
      mfderiv (complexModel d) (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c))
        e z v := by
  have hc := he.differentiableWithinAt_writtenInExtChartAt
  have hd : DifferentiableAt ℂ
      (writtenInExtChartAt (complexModel d)
        (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) z e)
      ((extChartAt (complexModel d) z) z) := by
    simpa only [complexModel, modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ] using hc
  have hr : MDifferentiableAt (realModel d)
      (modelWithCornersSelf ℝ (ComplexModel r × ComplexModel c)) e z := by
    apply (mdifferentiableAt_iff e z).mpr
    exact ⟨he.continuousAt, (hd.restrictScalars ℝ).differentiableWithinAt⟩
  rw [hr.mfderiv, he.mfderiv]
  simp only [realModel, complexModel, modelWithCornersSelf_coe, Set.range_id,
    fderivWithin_univ]
  change (fderiv ℝ (writtenInExtChartAt (complexModel d)
      (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) z e)
      ((extChartAt (complexModel d) z) z)) v =
    (fderiv ℂ (writtenInExtChartAt (complexModel d)
      (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) z e)
      ((extChartAt (complexModel d) z) z)) v
  exact congrArg (fun L ↦ L v) (hd.fderiv_restrictScalars (𝕜 := ℝ))

/-- A product chart flattening a complex distribution has zero transverse derivative on its
realification. -/
private theorem complex_flattening_real_horizontal
    {e : M → ComplexModel r × ComplexModel c} {S : Set M}
    (he : ContMDiffOn (complexModel d)
      (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) ∞ e S)
    (hS : IsOpen S)
    (P : (z : M) → Submodule ℂ (TangentSpace (complexModel d) z))
    (Q : RealTangentDistribution (realModel d) M)
    (hReal : ∀ z, ((P z).restrictScalars ℝ).map
      (complexTangentToReal d z).toLinearEquiv.toLinearMap = Q z)
    (hflat : ∀ z ∈ S, (P z).map
      (mfderiv (complexModel d) (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c))
        e z).toLinearMap = LinearMap.range (LinearMap.inl ℂ (ComplexModel r) (ComplexModel c))) :
    ∀ z ∈ S, ∀ v ∈ Q z,
      (mfderiv (realModel d) (modelWithCornersSelf ℝ (ComplexModel r × ComplexModel c))
        e z v).2 = 0 := by
  intro z hz v hv
  rw [← hReal z] at hv
  obtain ⟨w, hw, hwv⟩ := hv
  change complexTangentToReal d z w = v at hwv
  rw [← hwv, product_box_mfderiv_complex_to_real
    ((he.contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt (by simp))]
  have hm : mfderiv (complexModel d)
      (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) e z w ∈
      LinearMap.range (LinearMap.inl ℂ (ComplexModel r) (ComplexModel c)) := by
    rw [← hflat z hz]
    exact ⟨w, hw, rfl⟩
  obtain ⟨u, hu⟩ := hm
  exact congrArg Prod.snd hu.symm

section OriginalNative
variable {M₀ : Type*} [MetricSpace M₀] [ChartedSpace (ComplexModel d) M₀]
  [IsManifold (complexModel d) ∞ M₀] [IsManifold (realModel d) ∞ M₀]

/-- A holomorphic product box flattening the complex tangent distribution yields local horizontal
plaque charts on the intrinsic native leaf topology. -/
private theorem holomorphic_native_product_plaque_chart
    (f : M₀ ≃ₜ M₀)
    (P : (z : M₀) → Submodule ℂ (TangentSpace (complexModel d) z))
    (hP : IsHolomorphicTangentSubbundle r P)
    (Q : RealTangentDistribution (realModel d) M₀)
    (hReal : ∀ z, ((P z).restrictScalars ℝ).map
      (complexTangentToReal d z).toLinearEquiv.toLinearMap = Q z)
    (x : M₀) (D : NativeAsymptoticLeafDatum (realModel d) f Q x)
    (e : OpenPartialHomeomorph M₀ (ComplexModel r × ComplexModel c))
    (he : ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ e e.source)
    (hei : ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ e.symm e.target)
    (hflat : ∀ z ∈ e.source, (P z).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c)) e z).toLinearMap =
        LinearMap.range (LinearMap.inl ℂ (ComplexModel r) (ComplexModel c))) :
    letI : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
    ∀ a : StableAsymptoticLeaf f x, a.val ∈ e.source →
      ∃ k : OpenPartialHomeomorph (StableAsymptoticLeaf f x) (ComplexModel r),
        a ∈ k.source ∧
        (∀ z ∈ k.source, z.val ∈ e.source ∧ k z = (e z.val).1) ∧
        ∀ u ∈ k.target, (u, (e a.val).2) ∈ e.target ∧
          (k.symm u).val = e.symm (u, (e a.val).2) := by
  let : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
  let : ChartedSpace (Fin D.rank → ℝ) (StableAsymptoticLeaf f x) := D.charts
  obtain ⟨U, s, hx, hs, hspan⟩ := hP x
  have hself : ForwardAsymptotic f x x := by simp [ForwardAsymptotic]
  let z : StableAsymptoticLeaf f x := ⟨x, hself⟩
  obtain ⟨T, _, _⟩ := NativeLeafRankScratch.native_leaf_frame_equiv D z (P x)
    (fun i ↦ s i x) (hs.2.2 x hx) (hspan x hx) (hReal x)
  have he0 : ContMDiffOn (complexModel d)
      (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) ∞ e e.source := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact he
  have hei0 : ContMDiffOn (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c))
      (complexModel d) ∞ e.symm e.target := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hei
  have hflat0 : ∀ z ∈ e.source, (P z).map
      (mfderiv (complexModel d) (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c))
        e z).toLinearMap = LinearMap.range
          (LinearMap.inl ℂ (ComplexModel r) (ComplexModel c)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hflat
  exact Theorem12HorizontalSupport.nativeAsymptoticLeaf_product_plaque_chart
    (realModel d) f Q x D T e
    (holomorphic_product_box_real_smooth he0)
    (holomorphic_product_box_inverse_real_smooth hei0)
    (complex_flattening_real_horizontal he0 e.open_source P Q hReal hflat0)
end OriginalNative

end
end HolomorphicAnosov.Theorem12HolomorphicPlaqueSupport


namespace HolomorphicAnosov.NativeRegularFoliation
open Set Topology _root_.Topology TopologicalSpace
open scoped ContDiff Manifold
noncomputable section

universe u v

variable {d r c : ℕ} {M : Type u} [MetricSpace M]
  [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M] [IsManifold (realModel d) ∞ M]
  (f : M ≃ₜ M) (Q : RealTangentDistribution (realModel d) M)
  (D : ∀ x, NativeAsymptoticLeafDatum (realModel d) f Q x)
  {J : Type v}
  (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))

omit [SecondCountableTopology M] [IsManifold (complexModel d) ∞ M] in
/-- The point-preserving carrier identification transports local native plaque charts to
quotient-class charts. -/
private theorem class_local_chart
    (hcharts : ∀ x i, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x, a.val ∈ (box i).source →
        ∃ k : OpenPartialHomeomorph (StableAsymptoticLeaf f x) (ComplexModel r),
          a ∈ k.source ∧
          (∀ z ∈ k.source, z.val ∈ (box i).source ∧ k z = (box i z.val).1) ∧
          ∀ u ∈ k.target, (u, (box i a.val).2) ∈ (box i).target ∧
            (k.symm u).val = (box i).symm (u, (box i a.val).2))
    (q : Quotient (NativeBoxPartition.asymptoticSetoid f)) (i : J) :
    letI := NativeClassCarrier.classTopology f (NativeBoxPartition.asymptoticSetoid f)
      (fun _ _ ↦ Iff.rfl) q (D q.out).topology
    ∀ a : IntrinsicFoliationLeaf (NativeBoxPartition.asymptoticSetoid f) q,
      a.val ∈ (box i).source →
        ∃ k : OpenPartialHomeomorph
            (IntrinsicFoliationLeaf (NativeBoxPartition.asymptoticSetoid f) q) (ComplexModel r),
          a ∈ k.source ∧
          (∀ z ∈ k.source, z.val ∈ (box i).source ∧ k z = (box i z.val).1) ∧
          ∀ u ∈ k.target, (u, (box i a.val).2) ∈ (box i).target ∧
            (k.symm u).val = (box i).symm (u, (box i a.val).2) := by
  let _ := (D q.out).topology
  let _ := NativeClassCarrier.classTopology f (NativeBoxPartition.asymptoticSetoid f)
    (fun _ _ ↦ Iff.rfl) q (D q.out).topology
  let h := NativeClassCarrier.nativeExtractClassNativeHomeomorph f (NativeBoxPartition.asymptoticSetoid f)
    (fun _ _ ↦ Iff.rfl) q (D q.out).topology
  intro a ha
  obtain ⟨k, hk, hf, hi⟩ := hcharts q.out i (h a) ha
  exact ⟨h.transOpenPartialHomeomorph k, hk, fun z hz ↦ hf (h z) hz, hi⟩

omit [SecondCountableTopology M] [IsManifold (complexModel d) ∞ M] in
/-- The transverse box coordinate is constant on the source of a native inverse-slice chart. -/
private theorem native_constant_of_charts
    (hcharts : ∀ x i, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x, a.val ∈ (box i).source →
        ∃ k : OpenPartialHomeomorph (StableAsymptoticLeaf f x) (ComplexModel r),
          a ∈ k.source ∧
          (∀ z ∈ k.source, z.val ∈ (box i).source ∧ k z = (box i z.val).1) ∧
          ∀ u ∈ k.target, (u, (box i a.val).2) ∈ (box i).target ∧
            (k.symm u).val = (box i).symm (u, (box i a.val).2)) :
    ∀ x i, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x, a.val ∈ (box i).source →
        ∃ W : Set (StableAsymptoticLeaf f x), IsOpen W ∧ a ∈ W ∧
          W ⊆ Subtype.val ⁻¹' (box i).source ∧
            ∀ b ∈ W, (box i b.val).2 = (box i a.val).2 := by
  intro x i
  let _ := (D x).topology
  intro a ha
  obtain ⟨k, hk, hf, hi⟩ := hcharts x i a ha
  refine ⟨k.source, k.open_source, hk, fun z hz ↦ (hf z hz).1, ?_⟩
  intro z hz
  obtain ⟨ht, he⟩ := hi (k z) (k.map_source hz)
  rw [k.left_inv hz] at he
  rw [he, (box i).right_inv ht]

/-- A unit holomorphic product-box cover compatible with native plaque charts defines a regular
holomorphic foliation with the asymptotic partition and intrinsic native leaf topologies.
(Nisoli, Defs. 1.1.1–1.1.3, pp.9–10; HPS, §7, pp.115–116; Shub, Def. 2.1, pp.8–9) -/
private theorem native_regular_foliation_of_unit_boxes
    (hdim : d = r + c)
    (P : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (htarget : ∀ i, (box i).target =
      (complexFoliationDisk r : Set _) ×ˢ (complexFoliationDisk c : Set _))
    (hcover : ∀ x : M, ∃ i, x ∈ (box i).source)
    (he : ∀ i, ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ (box i) (box i).source)
    (hei : ∀ i, ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ (box i).symm (box i).target)
    (hflat : ∀ i x, x ∈ (box i).source → (P x).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c)) (box i) x).toLinearMap =
        (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (hcharts : ∀ x i, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x, a.val ∈ (box i).source →
        ∃ k : OpenPartialHomeomorph (StableAsymptoticLeaf f x) (ComplexModel r),
          a ∈ k.source ∧
          (∀ z ∈ k.source, z.val ∈ (box i).source ∧ k z = (box i z.val).1) ∧
          ∀ u ∈ k.target, (u, (box i a.val).2) ∈ (box i).target ∧
            (k.symm u).val = (box i).symm (u, (box i a.val).2)) :
    ∃ F : RegularHolomorphicFoliation.{u, v} d r c M,
      (∃ e : J ≃ F.boxIndex, ∀ i, F.box (e i) = box i) ∧
      F.partition = NativeBoxPartition.asymptoticSetoid f ∧
      HEq F.leafTopology
        (fun q : Quotient (NativeBoxPartition.asymptoticSetoid f) ↦
          NativeClassCarrier.classTopology f (NativeBoxPartition.asymptoticSetoid f)
            (fun _ _ ↦ Iff.rfl) q (D q.out).topology) := by
  let R := NativeBoxPartition.asymptoticSetoid f
  have hlift := NativeBoxPartition.slice_lifts_of_native_inverse_charts
    (realModel d) f Q D r c box (by
      intro i b a
      let x := (box i).symm (a.val, b.val)
      let _ := (D x).topology
      let z : StableAsymptoticLeaf f x := ⟨x, R.refl x⟩
      have ht : (a.val, b.val) ∈ (box i).target := by
        rw [htarget]
        exact ⟨a.property, b.property⟩
      obtain ⟨k, hk, hf, hi⟩ := hcharts x i z ((box i).map_target ht)
      refine ⟨k, hk, ?_, ?_⟩
      · exact (hf z hk).2.trans (congrArg Prod.fst ((box i).right_inv ht))
      · intro u hu
        have hh := (hi u hu).2
        simpa only [z, x, (box i).right_inv ht] using hh)
  have hconstant := native_constant_of_charts f Q D box hcharts
  have hlocal := NativeBoxPartition.same_slice_neighbourhoods_of_transverse_constant
    (realModel d) f Q D r c box htarget hcover hconstant
  have hgenerated := NativeBoxPartition.asymptotic_partition_generated
    (realModel d) f Q D r c box hlift hlocal
  let label := NativeBoxPartition.sliceLabel r c f box
  have hlabel := NativeBoxPartition.slice_label_eq r c f box hlift
  let LT : ∀ q : Quotient R, TopologicalSpace (IntrinsicFoliationLeaf R q) :=
    fun q ↦ NativeClassCarrier.classTopology f R (fun _ _ ↦ Iff.rfl) q (D q.out).topology
  let idx : ∀ q : Quotient R, IntrinsicFoliationLeaf R q → J :=
    fun _ p ↦ (hcover p.val).choose
  have hidx : ∀ q (p : IntrinsicFoliationLeaf R q), p.val ∈ (box (idx q p)).source :=
    fun _ p ↦ (hcover p.val).choose_spec
  let χ : ∀ q : Quotient R, letI := LT q
      IntrinsicFoliationLeaf R q →
        OpenPartialHomeomorph (IntrinsicFoliationLeaf R q) (ComplexModel r) :=
    fun q ↦ by
      letI := LT q
      exact fun p ↦ (class_local_chart f Q D box hcharts q (idx q p) p (hidx q p)).choose
  have hχ : ∀ q : Quotient R, letI := LT q
      ∀ p : IntrinsicFoliationLeaf R q,
        p ∈ (χ q p).source ∧
        (∀ z ∈ (χ q p).source,
          z.val ∈ (box (idx q p)).source ∧ χ q p z = (box (idx q p) z.val).1) ∧
        ∀ u ∈ (χ q p).target,
          (u, (box (idx q p) p.val).2) ∈ (box (idx q p)).target ∧
          ((χ q p).symm u).val = (box (idx q p)).symm (u, (box (idx q p) p.val).2) :=
    fun q p ↦ (class_local_chart f Q D box hcharts q (idx q p) p (hidx q p)).choose_spec
  let B : ∀ q : Quotient R, IntrinsicFoliationLeaf R q →
      OpenPartialHomeomorph M (ComplexModel r × ComplexModel c) :=
    fun q p ↦ box (idx q p)
  let t : ∀ q : Quotient R, IntrinsicFoliationLeaf R q → ComplexModel c :=
    fun q p ↦ (B q p p.val).2
  have hχs : ∀ q : Quotient R, letI := LT q
      ∀ p, p ∈ (χ q p).source := fun q p ↦ (hχ q p).1
  have hχm : ∀ q : Quotient R, letI := LT q
      ∀ p z, z ∈ (χ q p).target → (z, t q p) ∈ (B q p).target :=
    fun q p z hz ↦ ((hχ q p).2.2 z hz).1
  have hχi : ∀ q : Quotient R, letI := LT q
      ∀ p z, z ∈ (χ q p).target → ((χ q p).symm z).val = (B q p).symm (z, t q p) :=
    fun q p z hz ↦ ((hχ q p).2.2 z hz).2
  have he0 : ∀ i, ContMDiffOn (complexModel d)
      𝓘(ℂ, ComplexModel r × ComplexModel c) ∞ (box i) (box i).source := by
    intro i
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact he i
  have hei0 : ∀ i, ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel c)
      (complexModel d) ∞ (box i).symm (box i).target := by
    intro i
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hei i
  let LC : ∀ q : Quotient R, letI := LT q
      ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf R q) :=
    fun q ↦ NativeComplexAtlas.nativeChartedSpace (χ q) (hχs q)
  have hman : ∀ q : Quotient R, letI := LT q; letI := LC q
      IsManifold (complexModel r) ∞ (IntrinsicFoliationLeaf R q) :=
    fun q ↦ NativeComplexAtlas.native_isManifold Subtype.val (χ q) (hχs q)
      (B q) (t q) (hχm q) (hχi q) (fun p ↦ he0 (idx q p)) (fun p ↦ hei0 (idx q p))
  have hinclusion : ∀ q : Quotient R, letI := LT q; letI := LC q
      ContMDiff (complexModel r) (complexModel d) ∞
        (Subtype.val : IntrinsicFoliationLeaf R q → M) :=
    fun q ↦ NativeComplexAtlas.native_inclusion_contMDiff Subtype.val (χ q) (hχs q)
      (B q) (t q) (hχm q) (hχi q) (fun p ↦ he0 (idx q p)) (fun p ↦ hei0 (idx q p))
  have himmersion : ∀ q : Quotient R, letI := LT q; letI := LC q
      ∀ p, Function.Injective (mfderiv (complexModel r) (complexModel d)
        (Subtype.val : IntrinsicFoliationLeaf R q → M) p) :=
    fun q ↦ NativeComplexAtlas.native_inclusion_mfderiv_injective Subtype.val (χ q) (hχs q)
      (B q) (t q) (hχm q) (hχi q) (fun p ↦ he0 (idx q p)) (fun p ↦ hei0 (idx q p))
  have htop : ∀ q : Quotient R, letI := LT q
      T2Space (IntrinsicFoliationLeaf R q) ∧
      SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
      ConnectedSpace (IntrinsicFoliationLeaf R q) := fun q ↦
    NativeClassCarrier.class_topological_properties f R (fun _ _ ↦ Iff.rfl) q
      (D q.out).topology (D q.out).hausdorff (D q.out).secondCountable (D q.out).connected
  have hplaque : ∀ i b, letI := LT (label i b); letI := LC (label i b)
      ∃ U : Opens (IntrinsicFoliationLeaf R (label i b)),
        ∃ H : Diffeomorph (complexModel r) (complexModel r) (complexFoliationDisk r) U ∞,
          ∀ a, (H a).val.val = (box i).symm (a.val, b.val) := by
    intro i b
    let q := label i b
    let _ := LT q
    let _ := LC q
    let h : complexFoliationDisk r → IntrinsicFoliationLeaf R q :=
      fun a ↦ ⟨(box i).symm (a.val, b.val), hlabel i a b⟩
    have ht : ∀ a : complexFoliationDisk r, (a.val, b.val) ∈ (box i).target := by
      intro a
      rw [htarget]
      exact ⟨a.property, b.property⟩
    let k : complexFoliationDisk r →
        OpenPartialHomeomorph (IntrinsicFoliationLeaf R q) (ComplexModel r) :=
      fun a ↦ (class_local_chart f Q D box hcharts q i (h a)
        ((box i).map_target (ht a))).choose
    have hk a := (class_local_chart f Q D box hcharts q i (h a)
      ((box i).map_target (ht a))).choose_spec
    have hkforward : ∀ a, k a (h a) = a.val := by
      intro a
      exact (hk a).2.1 (h a) (hk a).1 |>.2 |>.trans
        (congrArg Prod.fst ((box i).right_inv (ht a)))
    have hkinverse : ∀ a u, u ∈ (k a).target →
        ((k a).symm u).val = (box i).symm (u, b.val) := by
      intro a u hu
      have hh := ((hk a).2.2 u hu).2
      simpa only [k, h, (box i).right_inv (ht a)] using hh
    obtain ⟨U, _, H, _, hH⟩ := WholePlaqueSupport.whole_plaque_diffeomorph
      (complexModel d) (complexFoliationDisk r) Subtype.val Subtype.val_injective
      (χ q) (hχs q) (B q) (t q) (hχm q) (hχi q)
      (fun p ↦ he0 (idx q p)) (fun p ↦ hei0 (idx q p))
      (box i) (he0 i) (hei0 i) b.val ht h (fun _ ↦ rfl)
      k (fun a ↦ (hk a).1) hkforward hkinverse
    exact ⟨U, H, hH⟩
  choose plaque H hH using hplaque
  have hopen : ∀ q i b (h : label i b = q), letI := LT q
      IsOpenEmbedding (fun a : complexFoliationDisk r ↦
        (⟨(box i).symm (a.val, b.val), (hlabel i a b).trans h⟩ :
          IntrinsicFoliationLeaf R q)) := by
    intro q i b h
    subst q
    let _ := LT (label i b)
    let _ := LC (label i b)
    have hh := (plaque i b).isOpen.isOpenEmbedding_subtypeVal.comp
      (H i b).toHomeomorph.isOpenEmbedding
    convert hh using 1
    funext a
    apply Subtype.ext
    exact (hH i b a).symm
  have hgeneratedTopology : ∀ q (W : Set (IntrinsicFoliationLeaf R q)), letI := LT q
      IsOpen W ↔ ∀ i b (h : label i b = q),
        IsOpen ((fun a : complexFoliationDisk r ↦
          (⟨(box i).symm (a.val, b.val), (hlabel i a b).trans h⟩ :
            IntrinsicFoliationLeaf R q)) ⁻¹' W) := by
    intro q W
    let _ := LT q
    constructor
    · intro hW i b h
      exact hW.preimage (hopen q i b h).continuous
    · intro hW
      rw [isOpen_iff_mem_nhds]
      intro z hz
      obtain ⟨i, hi⟩ := hcover z.val
      have ht := (box i).map_source hi
      rw [htarget] at ht
      let a : complexFoliationDisk r := ⟨(box i z.val).1, ht.1⟩
      let b : complexFoliationDisk c := ⟨(box i z.val).2, ht.2⟩
      have hab : (box i).symm (a.val, b.val) = z.val := (box i).left_inv hi
      have hl : label i b = q :=
        (hlabel i a b).symm.trans ((congrArg (Quotient.mk R) hab).trans z.property)
      let p : complexFoliationDisk r → IntrinsicFoliationLeaf R q :=
        fun a ↦ ⟨(box i).symm (a.val, b.val), (hlabel i a b).trans hl⟩
      have hpa : p a = z := Subtype.ext hab
      have hzimage : z ∈ p '' (p ⁻¹' W) := ⟨a, by
        change p a ∈ W
        rw [hpa]
        exact hz, hpa⟩
      apply Filter.mem_of_superset (((hopen q i b hl).isOpenMap _ (hW i b hl)).mem_nhds hzimage)
      rintro y ⟨u, hu, rfl⟩
      exact hu
  let F : RegularHolomorphicFoliation.{u, v} d r c M :=
    { dimension := hdim
      boxIndex := J
      box := box
      box_target := htarget
      cover := hcover
      box_holomorphic := he
      box_inverse_holomorphic := hei
      transverse_overlap := fun i j _ hi hj ↦
        FrobeniusSupport.holomorphic_product_charts_transverse_overlap (complexModel d)
          P (box i) (box j) (he i) (hei i) (he j) (hei j) (hflat i) (hflat j) hi hj
      partition := R
      partition_generated := hgenerated
      leafTopology := LT
      leafCharts := LC
      leafManifold := hman
      leafConnected := fun q ↦ (htop q).2.2
      leafHausdorff := fun q ↦ (htop q).1
      leafCountable := fun q ↦ (htop q).2.1
      label := label
      label_eq := hlabel
      plaque := plaque
      plaqueChart := H
      plaqueChart_eq := fun i a b ↦ hH i b a
      topology_generated := hgeneratedTopology
      inclusion_holomorphic := hinclusion
      inclusion_immersion := himmersion }
  exact ⟨F, ⟨Equiv.refl J, fun _ ↦ rfl⟩, rfl, HEq.rfl⟩


/-- A unit holomorphic box cover flattening the complex tangent distribution defines a regular
holomorphic foliation with the native asymptotic partition and leaf topologies. -/
private theorem native_regular_foliation_from_original_tangent
    (hdim : d = r + c)
    (P : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hP : IsHolomorphicTangentSubbundle r P)
    (hReal : ∀ z, ((P z).restrictScalars ℝ).map
      (complexTangentToReal d z).toLinearEquiv.toLinearMap = Q z)
    (htarget : ∀ i, (box i).target =
      (complexFoliationDisk r : Set _) ×ˢ (complexFoliationDisk c : Set _))
    (hcover : ∀ x : M, ∃ i, x ∈ (box i).source)
    (he : ∀ i, ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ (box i) (box i).source)
    (hei : ∀ i, ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ (box i).symm (box i).target)
    (hflat : ∀ i x, x ∈ (box i).source → (P x).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c)) (box i) x).toLinearMap =
        (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range) :
    ∃ F : RegularHolomorphicFoliation.{u, v} d r c M,
      (∃ e : J ≃ F.boxIndex, ∀ i, F.box (e i) = box i) ∧
      F.partition = NativeBoxPartition.asymptoticSetoid f ∧
      HEq F.leafTopology
        (fun q : Quotient (NativeBoxPartition.asymptoticSetoid f) ↦
          NativeClassCarrier.classTopology f (NativeBoxPartition.asymptoticSetoid f)
            (fun _ _ ↦ Iff.rfl) q (D q.out).topology) := by
  apply native_regular_foliation_of_unit_boxes f Q D box hdim P htarget hcover he hei hflat
  intro x i
  exact Theorem12HolomorphicPlaqueSupport.holomorphic_native_product_plaque_chart
    f P hP Q hReal x (D x) (box i) (he i) (hei i) (hflat i)


end
end HolomorphicAnosov.NativeRegularFoliation



namespace HolomorphicAnosov.NativeLeafRebase
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section

section CommonCharts
variable {A F X L N : Type*} [TopologicalSpace A] [TopologicalSpace F]
  [TopologicalSpace X] [TopologicalSpace L] [TopologicalSpace N]

/-- A point-preserving identification is continuous when both intrinsic spaces have local inverse
charts for the same ambient slices. -/
private theorem continuous_of_common_plaque_charts
    (ι : L → X) (j : N → X) (hj : Function.Injective j) (h : L → N)
    (hsame : ∀ p, j (h p) = ι p)
    (hw : ∀ p : L, ∃ e : OpenPartialHomeomorph X (A × F), ∃ b : F,
      ∃ k : OpenPartialHomeomorph L A, ∃ l : OpenPartialHomeomorph N A,
        p ∈ k.source ∧ h p ∈ l.source ∧ k p = l (h p) ∧
        (∀ u ∈ k.target, ι (k.symm u) = e.symm (u, b)) ∧
        (∀ u ∈ l.target, j (l.symm u) = e.symm (u, b))) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨e, b, k, l, hk, hl, heq, hki, hli⟩ := hw p
  have htarget : k p ∈ l.target := heq ▸ l.map_source hl
  have hc : ContinuousAt (fun z ↦ l.symm (k z)) p :=
    (l.continuousAt_symm htarget).comp (k.continuousAt hk)
  apply hc.congr
  filter_upwards [k.open_source.mem_nhds hk,
    (k.continuousAt hk).preimage_mem_nhds (l.open_target.mem_nhds htarget)] with z hzk hzl
  apply hj
  rw [hsame z, hli _ hzl, ← hki _ (k.map_source hzk), k.left_inv hzk]

/-- A point-preserving equivalence is a homeomorphism when both intrinsic spaces have compatible
local plaque charts. -/
private theorem homeomorph_of_common_plaque_charts
    (ι : L → X) (hι : Function.Injective ι) (j : N → X) (hj : Function.Injective j)
    (h : L ≃ N) (hsame : ∀ p, j (h p) = ι p)
    (hw : ∀ p : L, ∃ e : OpenPartialHomeomorph X (A × F), ∃ b : F,
      ∃ k : OpenPartialHomeomorph L A, ∃ l : OpenPartialHomeomorph N A,
        p ∈ k.source ∧ h p ∈ l.source ∧ k p = l (h p) ∧
        (∀ u ∈ k.target, ι (k.symm u) = e.symm (u, b)) ∧
        (∀ u ∈ l.target, j (l.symm u) = e.symm (u, b))) :
    ∃ H : L ≃ₜ N, H.toEquiv = h := by
  have hc := continuous_of_common_plaque_charts ι j hj h hsame hw
  have hs : ∀ p, ι (h.symm p) = j p := fun p ↦
    (hsame (h.symm p)).symm.trans (congrArg j (h.apply_symm_apply p))
  have hci := continuous_of_common_plaque_charts j ι hι h.symm hs (by
    intro p
    obtain ⟨e, b, k, l, hk, hl, heq, hki, hli⟩ := hw (h.symm p)
    rw [h.apply_symm_apply] at hl heq
    exact ⟨e, b, l, k, hl, hk, heq.symm, hli, hki⟩)
  exact ⟨{ h with continuous_toFun := hc, continuous_invFun := hci }, rfl⟩

end CommonCharts

section Native
universe u v
variable {d r c : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
  (f : M ≃ₜ M) (Q : RealTangentDistribution (realModel d) M)
  (D : ∀ x, NativeAsymptoticLeafDatum (realModel d) f Q x)
  {J : Type v} (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))

/-- The point-preserving equivalence between native asymptotic leaves based at asymptotically
equivalent points. -/
private def nativeRebaseEquiv {x y : M}
    (hxy : NativeBoxPartition.asymptoticSetoid f x y) :
    StableAsymptoticLeaf f x ≃ StableAsymptoticLeaf f y where
  toFun z := ⟨z.val, (NativeBoxPartition.asymptoticSetoid f).trans
    ((NativeBoxPartition.asymptoticSetoid f).symm hxy) z.property⟩
  invFun z := ⟨z.val, (NativeBoxPartition.asymptoticSetoid f).trans hxy z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Native leaves based at asymptotically equivalent points are homeomorphic by the point-preserving
identification. -/
private theorem native_rebase_homeomorph
    (hcover : ∀ z : M, ∃ i, z ∈ (box i).source)
    (hcharts : ∀ x i, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x, a.val ∈ (box i).source →
        ∃ k : OpenPartialHomeomorph (StableAsymptoticLeaf f x) (ComplexModel r),
          a ∈ k.source ∧
          (∀ z ∈ k.source, z.val ∈ (box i).source ∧ k z = (box i z.val).1) ∧
          ∀ u ∈ k.target, (u, (box i a.val).2) ∈ (box i).target ∧
            (k.symm u).val = (box i).symm (u, (box i a.val).2))
    {x y : M} (hxy : NativeBoxPartition.asymptoticSetoid f x y) :
    letI := (D x).topology
    letI := (D y).topology
    ∃ H : StableAsymptoticLeaf f x ≃ₜ StableAsymptoticLeaf f y,
      H.toEquiv = nativeRebaseEquiv f hxy ∧ ∀ z, (H z).val = z.val := by
  let _ := (D x).topology
  let _ := (D y).topology
  let h := nativeRebaseEquiv f hxy
  obtain ⟨H, hH⟩ := homeomorph_of_common_plaque_charts
    Subtype.val Subtype.val_injective Subtype.val Subtype.val_injective h (fun _ ↦ rfl) (by
      intro p
      obtain ⟨i, hi⟩ := hcover p.val
      obtain ⟨k, hk, hkf, hki⟩ := hcharts x i p hi
      obtain ⟨l, hl, hlf, hli⟩ := hcharts y i (h p) hi
      refine ⟨box i, (box i p.val).2, k, l, hk, hl,
        (hkf p hk).2.trans (hlf (h p) hl).2.symm,
        fun u hu ↦ (hki u hu).2, fun u hu ↦ (hli u hu).2⟩)
  refine ⟨H, hH, ?_⟩
  intro z
  change (H.toEquiv z).val = z.val
  rw [hH]
  rfl

/-- The quotient-class leaf is homeomorphic to the native leaf at its marked point, preserving
ambient values and the marked point. -/
private theorem class_native_marked_homeomorph
    (hcover : ∀ z : M, ∃ i, z ∈ (box i).source)
    (hcharts : ∀ x i, letI := (D x).topology
      ∀ a : StableAsymptoticLeaf f x, a.val ∈ (box i).source →
        ∃ k : OpenPartialHomeomorph (StableAsymptoticLeaf f x) (ComplexModel r),
          a ∈ k.source ∧
          (∀ z ∈ k.source, z.val ∈ (box i).source ∧ k z = (box i z.val).1) ∧
          ∀ u ∈ k.target, (u, (box i a.val).2) ∈ (box i).target ∧
            (k.symm u).val = (box i).symm (u, (box i a.val).2))
    (x : M) :
    let R := NativeBoxPartition.asymptoticSetoid f
    let q := Quotient.mk R x
    letI := NativeClassCarrier.classTopology f R (fun _ _ ↦ Iff.rfl) q (D q.out).topology
    letI := (D x).topology
    ∃ H : IntrinsicFoliationLeaf R q ≃ₜ StableAsymptoticLeaf f x,
      (∀ z, (H z).val = z.val) ∧
      (∀ z, (H.symm z).val = z.val) ∧
      H ⟨x, rfl⟩ = ⟨x, R.refl x⟩ := by
  let R := NativeBoxPartition.asymptoticSetoid f
  let q := Quotient.mk R x
  let _ := (D q.out).topology
  let _ := NativeClassCarrier.classTopology f R (fun _ _ ↦ Iff.rfl) q (D q.out).topology
  let _ := (D x).topology
  let C := NativeClassCarrier.nativeExtractClassNativeHomeomorph f R (fun _ _ ↦ Iff.rfl)
    q (D q.out).topology
  have hqx : R q.out x := Quotient.mk_out x
  obtain ⟨B, _, hB⟩ := native_rebase_homeomorph f Q D box hcover hcharts hqx
  let H := C.trans B
  have hH : ∀ z, (H z).val = z.val := fun z ↦ hB (C z)
  refine ⟨H, hH, ?_, ?_⟩
  · intro z
    exact (hH (H.symm z)).symm.trans (congrArg Subtype.val (H.apply_symm_apply z))
  · exact Subtype.ext (hH ⟨x, rfl⟩)

end Native

section OriginalBinding
universe u v
variable {d r c : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  [IsManifold (realModel d) ∞ M]
  (f : M ≃ₜ M) (Q : RealTangentDistribution (realModel d) M)
  (D : ∀ x, NativeAsymptoticLeafDatum (realModel d) f Q x)
  {J : Type v} (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))

/-- Holomorphic flattening boxes and native tangent data give a point-preserving homeomorphism from
the quotient-class leaf to the native leaf at its marked point. (HPS, §7, pp.115–116; Nisoli,
Defs. 1.1.1–1.1.3, pp.9–10) -/
private theorem original_tangent_class_native_homeomorph
    (P : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hP : IsHolomorphicTangentSubbundle r P)
    (hReal : ∀ z, ((P z).restrictScalars ℝ).map
      (complexTangentToReal d z).toLinearEquiv.toLinearMap = Q z)
    (hcover : ∀ z : M, ∃ i, z ∈ (box i).source)
    (he : ∀ i, ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ (box i) (box i).source)
    (hei : ∀ i, ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ (box i).symm (box i).target)
    (hflat : ∀ i z, z ∈ (box i).source → (P z).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c)) (box i) z).toLinearMap =
        (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (x : M) :
    let R := NativeBoxPartition.asymptoticSetoid f
    let q := Quotient.mk R x
    letI := NativeClassCarrier.classTopology f R (fun _ _ ↦ Iff.rfl) q (D q.out).topology
    letI := (D x).topology
    ∃ H : IntrinsicFoliationLeaf R q ≃ₜ StableAsymptoticLeaf f x,
      (∀ z, (H z).val = z.val) ∧
      (∀ z, (H.symm z).val = z.val) ∧
      H ⟨x, rfl⟩ = ⟨x, R.refl x⟩ := by
  apply class_native_marked_homeomorph f Q D box hcover ?_ x
  intro z i
  exact Theorem12HolomorphicPlaqueSupport.holomorphic_native_product_plaque_chart
    f P hP Q hReal z (D z) (box i) (he i) (hei i) (hflat i)

variable [SecondCountableTopology M]

/-- A unit holomorphic flattening-box cover defines a regular holomorphic foliation whose leaves are
point-preservingly homeomorphic to the native leaves at their marked points. -/
theorem original_tangent_regular_foliation_native_homeomorph
    (hdim : d = r + c)
    (P : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hP : IsHolomorphicTangentSubbundle r P)
    (hReal : ∀ z, ((P z).restrictScalars ℝ).map
      (complexTangentToReal d z).toLinearEquiv.toLinearMap = Q z)
    (htarget : ∀ i, (box i).target =
      (complexFoliationDisk r : Set _) ×ˢ (complexFoliationDisk c : Set _))
    (hcover : ∀ z : M, ∃ i, z ∈ (box i).source)
    (he : ∀ i, ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ (box i) (box i).source)
    (hei : ∀ i, ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ (box i).symm (box i).target)
    (hflat : ∀ i z, z ∈ (box i).source → (P z).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c)) (box i) z).toLinearMap =
        (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range) :
    ∃ F : RegularHolomorphicFoliation.{u, v} d r c M,
      (∃ e : J ≃ F.boxIndex, ∀ i, F.box (e i) = box i) ∧
      F.partition = NativeBoxPartition.asymptoticSetoid f ∧
      ∀ x : M, letI := F.leafTopology (Quotient.mk F.partition x)
        letI := (D x).topology
        ∃ H : F.Leaf x ≃ₜ StableAsymptoticLeaf f x,
          (∀ z, (H z).val = z.val) ∧
          (∀ z, (H.symm z).val = z.val) ∧
          H ⟨x, rfl⟩ = ⟨x, (NativeBoxPartition.asymptoticSetoid f).refl x⟩ := by
  obtain ⟨F, heq, hp, ht⟩ :=
    NativeRegularFoliation.native_regular_foliation_from_original_tangent
      f Q D box hdim P hP hReal htarget hcover he hei hflat
  refine ⟨F, heq, hp, ?_⟩
  cases F
  cases hp
  have htop := eq_of_heq ht
  cases htop
  intro x
  exact original_tangent_class_native_homeomorph f Q D box P hP hReal hcover he hei hflat x

end OriginalBinding

end
end HolomorphicAnosov.NativeLeafRebase
