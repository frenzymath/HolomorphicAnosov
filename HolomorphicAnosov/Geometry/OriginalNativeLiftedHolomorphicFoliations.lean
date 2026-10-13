import HolomorphicAnosov.Geometry.ComplementaryComplexFrame
import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRangeHomeomorph
import HolomorphicAnosov.Geometry.NativeLeafRebase
import HolomorphicAnosov.Geometry.Manifold.VectorField.ImmersionChartTangentRange
import HolomorphicAnosov.Geometry.Manifold.VectorField.LieBracketMemLinearRange
import HolomorphicAnosov.Geometry.Manifold.VectorField.ImmersionChartBracketTangent
import HolomorphicAnosov.Geometry.Manifold.VectorField.ChartInverseMPullbackEq
import HolomorphicAnosov.Geometry.Manifold.VectorField.ImmersionMLieBracketTangent
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ProductBallTransverseIndependence
import HolomorphicAnosov.Geometry.TransverseCompMFDerivZero
import HolomorphicAnosov.Geometry.LocalBiholomorphicSheets
import HolomorphicAnosov.Geometry.TranslatedImage
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentLocalFrame
import HolomorphicAnosov.Geometry.ComplexToRealManifold
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
import HolomorphicAnosov.Geometry.SmoothLocalFlow
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import HolomorphicAnosov.Paper.Zhang.Anosov
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Data.List.FinRange
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf
import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRange
import Mathlib.Topology.UnitInterval
import Mathlib.Logic.Relation
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.LocallyPathConnected
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ImmersionDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! This file constructs regular holomorphic foliations from holomorphic Anosov tangent bundles and
intrinsic asymptotic leaves, and lifts them to holomorphic coverings. It identifies lifted
leaves with marked intrinsic path-lift ranges and their tangents with the pullback
distributions. (Zhang, Thm 1.2, p.11) -/





/-! Native plaque charts compatible with ambient holomorphic product boxes define complex atlases
and holomorphic leaf inclusions. (Demailly, I §1.A, pp.7–8 and I §7, p.60) -/

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

/-- The charted-space structure on a native leaf defined by its plaque charts. -/
@[local instance_reducible] private def nativeChartedSpace (c : L → OpenPartialHomeomorph L E)
    (hc : ∀ p, p ∈ (c p).source) : ChartedSpace E L where
  atlas := Set.range c
  chartAt := c
  mem_chart_source := hc
  chart_mem_atlas p := ⟨p, rfl⟩

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- The native chart coordinate equals the first projection of the ambient product box. -/
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

/-- Native chart transitions compatible with holomorphic ambient product boxes are holomorphic. -/
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

/-- Compatible native plaque charts define a complex manifold structure on the leaf. -/
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

/-- The derivative of the native leaf inclusion is injective. -/
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

/-- Compatible local plaque charts give a native leaf a complex manifold structure with holomorphic
inclusion and injective derivative. -/
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

/-! Local inverse plaque charts give whole plaques open images and biholomorphic parametrizations. -/
namespace HolomorphicAnosov.WholePlaqueSupport
open TopologicalSpace Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
section Topological
variable {A F X L : Type*} [TopologicalSpace A] [TopologicalSpace F]
  [TopologicalSpace X] [TopologicalSpace L]

/-- A plaque map with local inverse charts at every point is an open embedding. -/
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

/-- The plaque range is intrinsically open and homeomorphic to its coordinate domain. -/
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

/-- The whole plaque map is holomorphic in the native atlas. -/
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

/-- The inverse plaque homeomorphism is holomorphic. -/
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

/-- The whole plaque is intrinsically open and complex diffeomorphic to its coordinate disk. -/
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


/-! Asymptotic quotient classes are identified pointwise with native leaves and equipped with their
intrinsic topologies and complex atlases. (HPS, §7, pp.115–116; Ghys, §2, pp.588–589; Demailly,
I §1.A, pp.7–8) -/

open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
namespace HolomorphicAnosov.NativeClassCarrier

universe u v w

section Carrier
variable {M : Type u} [MetricSpace M] (f : M ≃ₜ M) (R : Setoid M)
  (hR : ∀ x y, R x y ↔ ForwardAsymptotic f x y) (q : Quotient R)

include hR in
/-- Equality of quotient labels is equivalent to asymptoticity. -/
private theorem class_label_iff (x y : M) :
    Quotient.mk R y = Quotient.mk R x ↔ ForwardAsymptotic f x y := by
  rw [Quotient.eq]
  exact ⟨fun h ↦ (hR x y).mp (R.symm h),
    fun h ↦ R.symm ((hR x y).mpr h)⟩

/-- The point-preserving equivalence between a partition class and its native asymptotic leaf. -/
private def classNativeEquiv : IntrinsicFoliationLeaf R q ≃ StableAsymptoticLeaf f q.out where
  toFun z := ⟨z.val, (hR q.out z.val).mp
    (R.symm (Quotient.mk_eq_iff_out.mp z.property))⟩
  invFun z := ⟨z.val, Quotient.mk_eq_iff_out.mpr
    (R.symm ((hR q.out z.val).mpr z.property))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[local simp] private theorem classNativeEquiv_val (z : IntrinsicFoliationLeaf R q) :
    (classNativeEquiv f R hR q z).val = z.val := rfl

@[local simp] private theorem classNativeEquiv_symm_val (z : StableAsymptoticLeaf f q.out) :
    ((classNativeEquiv f R hR q).symm z).val = z.val := rfl

/-- The topology on a partition class transported from its native asymptotic leaf. -/
@[local instance_reducible] private def classTopology (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out)) :
    TopologicalSpace (IntrinsicFoliationLeaf R q) :=
  letI := nativeTopology
  (classNativeEquiv f R hR q).topologicalSpace

/-- The point-preserving homeomorphism from a partition class to its native leaf. -/
private def classNativeHomeomorph
    (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out)) :
    letI := nativeTopology
    letI := classTopology f R hR q nativeTopology
    IntrinsicFoliationLeaf R q ≃ₜ StableAsymptoticLeaf f q.out :=
  letI := nativeTopology
  (classNativeEquiv f R hR q).homeomorph

@[local simp] private theorem classNativeHomeomorph_val
    (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out))
    (z : IntrinsicFoliationLeaf R q) :
    letI := nativeTopology
    letI := classTopology f R hR q nativeTopology
    (classNativeHomeomorph f R hR q nativeTopology z).val = z.val := rfl

@[local simp] private theorem classNativeHomeomorph_symm_val
    (nativeTopology : TopologicalSpace (StableAsymptoticLeaf f q.out))
    (z : StableAsymptoticLeaf f q.out) :
    letI := nativeTopology
    letI := classTopology f R hR q nativeTopology
    ((classNativeHomeomorph f R hR q nativeTopology).symm z).val = z.val := rfl

/-- The transported class topology is Hausdorff, second countable, and connected. -/
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
  let h := classNativeHomeomorph f R hR q nativeTopology
  exact ⟨h.symm.t2Space, h.secondCountableTopology,
    h.symm.surjective.connectedSpace h.symm.continuous⟩

end Carrier

section ChartTransport
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {C : Type u} {L : Type w} [TopologicalSpace C] [TopologicalSpace L]
  [ChartedSpace E L]

/-- The charted-space structure transported along a homeomorphism. -/
@[local instance_reducible] private def carriedChartedSpace (h : C ≃ₜ L) : ChartedSpace E C where
  atlas := Set.range (fun p : C ↦ h.transOpenPartialHomeomorph (chartAt E (h p)))
  chartAt p := h.transOpenPartialHomeomorph (chartAt E (h p))
  mem_chart_source p := mem_chart_source E (h p)
  chart_mem_atlas p := ⟨p, rfl⟩

omit [NormedSpace ℂ E] in
/-- Transported chart transitions equal the corresponding native chart transitions. -/
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

/-- The transported atlas defines a complex manifold structure. -/
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

/-- The transporting homeomorphism is holomorphic in the transported atlas. -/
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

/-- The inverse transporting homeomorphism is holomorphic. -/
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

/-- The derivative of the transporting homeomorphism is injective. -/
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

/-- An asymptotic partition class carries the native leaf's complex manifold structure and has a
holomorphic inclusion with injective derivative. -/
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
  let h := classNativeHomeomorph f R hR q D.topology
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


/-! Raw product-box slices generate asymptotic partitions and determine their quotient labels.
(Shub, Def 2.1, pp.8–9; HPS, pp.114–116; Nisoli, pp.9–10) -/

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

/-- An equivalence relation with related open neighborhoods on a preconnected space relates every pair of points. -/
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

/-- A connected parametrized plaque with local lifts into native asymptotic leaves has pairwise
asymptotic points. -/
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

/-- A unit complex disk plaque with local native lifts has pairwise asymptotic points. -/
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

/-- The setoid of forward asymptoticity for a homeomorphism. -/
private def asymptoticSetoid {M : Type*} [MetricSpace M] (f : M ≃ₜ M) : Setoid M :=
  ⟨ForwardAsymptotic f, asymptotic_equivalence f⟩

/-- The relation of lying in one horizontal slice of a product box. (Nisoli, Defs 1.1.1–1.1.3,
pp.9–10) -/
private def sameBoxSlice {M J : Type*} [TopologicalSpace M] (r c : ℕ)
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (x y : M) : Prop :=
  ∃ i, ∃ w : complexFoliationDisk c, ∃ a b : complexFoliationDisk r,
    (box i).symm (a.val, w.val) = x ∧ (box i).symm (b.val, w.val) = y

/-- Native inverse plaque charts provide local lifts of coordinate slices into native leaves. -/
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

/-- Native neighborhoods with constant transverse coordinate lie in a single product-box slice. -/
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

/-- The equivalence relation generated by raw box slices is the asymptotic relation. -/
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

/-- The origin in the unit complex foliation disk. -/
private def diskZero (r : ℕ) : complexFoliationDisk r :=
  ⟨0, Metric.mem_ball_self zero_lt_one⟩

/-- The asymptotic quotient label of a slice, represented by its horizontal origin. -/
private def sliceLabel {M J : Type*} [MetricSpace M] (r c : ℕ) (f : M ≃ₜ M)
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (i : J) (w : complexFoliationDisk c) : Quotient (asymptoticSetoid f) :=
  Quotient.mk _ ((box i).symm ((diskZero r).val, w.val))

/-- A slice's quotient label is independent of its horizontal coordinate. -/
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

/-- The point-preserving equivalence between a native asymptotic carrier and its quotient class. -/
private def nativeCarrierEquiv {M : Type*} [MetricSpace M] (f : M ≃ₜ M) (x : M) :
    IntrinsicFoliationLeaf (asymptoticSetoid f) (Quotient.mk (asymptoticSetoid f) x) ≃
      StableAsymptoticLeaf f x where
  toFun y := ⟨y.val, (asymptotic_equivalence f).symm (Quotient.exact y.property)⟩
  invFun y := ⟨y.val, Quotient.sound ((asymptotic_equivalence f).symm y.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The native carrier equivalence preserves ambient points. -/
private theorem nativeCarrierEquiv_val {M : Type*} [MetricSpace M] (f : M ≃ₜ M) (x : M)
    (y : IntrinsicFoliationLeaf (asymptoticSetoid f)
      (Quotient.mk (asymptoticSetoid f) x)) : (nativeCarrierEquiv f x y).val = y.val := rfl

end
end HolomorphicAnosov.NativeBoxPartition


/-! Transitions between charts flattening the same distribution have locally horizontally constant
transverse coordinates. (Nisoli, Defs 1.1.1–1.1.3, pp.9–10) -/

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

/-- Differentiable product charts flattening the same tangent distribution have locally horizontally
constant transverse transitions. (Nisoli, Defs 1.1.1–1.1.3, pp.9–10) -/
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
  obtain ⟨ε, hε, hsub, hconst⟩ :=
    HolomorphicAnosov.FrobeniusSupport.exists_product_ball_transverse_independent hU
    (fun q ↦ (t q).2) ht'.snd hzero ⟨hz₁, hz₂⟩
  refine ⟨Metric.ball z.1 ε ×ˢ Metric.ball z.2 ε,
    Metric.isOpen_ball.prod Metric.isOpen_ball, ⟨Metric.mem_ball_self hε,
      Metric.mem_ball_self hε⟩, hsub, ?_⟩
  exact hconst


/-- Holomorphic product charts flattening the same distribution satisfy the local transverse overlap
law. -/
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


/-! Transverse coordinates annihilating the native leaf tangent are constant on intrinsic coordinate
neighborhoods. -/

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

/-- The transverse coordinate derivative of a flattening product chart annihilates the distribution. -/
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


variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- A native asymptotic leaf lies in one product plaque on an intrinsic open neighborhood. -/
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
/-- A function with invertible derivative on a native leaf gives a local chart equal to that
function on its source. -/
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
/-- The horizontal derivative is bijective when the inclusion is injective on tangents, the
transverse derivative vanishes, and the dimensions agree. -/
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

/-- A native leaf has local horizontal coordinates whose inverse agrees with the ambient inverse
chart on a fixed transverse slice. -/
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
      (fun z hz ↦ Theorem12PlaqueSupport.transverse_comp_mfderiv_zero I j
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
/-- A native asymptotic leaf admits local horizontal plaque charts compatible with its intrinsic
atlas. -/
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

/-- An injective derivative whose range has a specified frame gives a frame equivalence for its
source tangent space. -/
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
/-- A native leaf tangent space is identified with the frame coordinates of its complex tangent
image. -/
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


/-- A holomorphic tangent frame determines the real dimension of a native leaf tangent space. -/
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

/-! Scalar restriction relates complex product-box derivatives to derivatives on the underlying real
manifolds. -/
namespace HolomorphicAnosov.Theorem12HolomorphicPlaqueSupport
open scoped ContDiff Manifold
open Set
noncomputable section
variable {d r c : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M]

/-- A holomorphic product box is smooth on the underlying real manifold. -/
private theorem holomorphic_product_box_real_smooth
    {e : M → ComplexModel r × ComplexModel c} {S : Set M}
    (he : ContMDiffOn (complexModel d)
      (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c)) ∞ e S) :
    ContMDiffOn (realModel d)
      (modelWithCornersSelf ℝ (ComplexModel r × ComplexModel c)) ∞ e S := by
  intro z hz
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (he z hz)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

/-- The inverse of a holomorphic product box is smooth on the underlying real manifold. -/
private theorem holomorphic_product_box_inverse_real_smooth
    {e : ComplexModel r × ComplexModel c → M} {S : Set (ComplexModel r × ComplexModel c)}
    (he : ContMDiffOn (modelWithCornersSelf ℂ (ComplexModel r × ComplexModel c))
      (complexModel d) ∞ e S) :
    ContMDiffOn (modelWithCornersSelf ℝ (ComplexModel r × ComplexModel c))
      (realModel d) ∞ e S := by
  intro z hz
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (he z hz)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

/-- The complex product-box derivative agrees with its real derivative under tangent realification. -/
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

/-- A chart flattening a complex distribution sends its realification into the real horizontal
subspace. -/
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

/-- A holomorphic product box flattening a native leaf's tangent distribution gives an intrinsic
horizontal plaque chart. -/
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
/-- Pointwise identification transports a native plaque chart to its partition class. -/
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
  let h := NativeClassCarrier.classNativeHomeomorph f (NativeBoxPartition.asymptoticSetoid f)
    (fun _ _ ↦ Iff.rfl) q (D q.out).topology
  intro a ha
  obtain ⟨k, hk, hf, hi⟩ := hcharts q.out i (h a) ha
  exact ⟨h.transOpenPartialHomeomorph k, hk, fun z hz ↦ hf (h z) hz, hi⟩

omit [SecondCountableTopology M] [IsManifold (complexModel d) ∞ M] in
/-- A native inverse-slice chart has constant transverse coordinate on its source. -/
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

/-- Unit holomorphic boxes and compatible native plaque charts define a regular holomorphic
foliation with intrinsic native leaf topologies. (Nisoli, Defs 1.1.1–1.1.3, pp.9–10; HPS, §7,
pp.115–116; Shub, Def 2.1, pp.8–9) -/
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


/-- Unit holomorphic boxes flattening a holomorphic distribution with native real leaves define a
regular holomorphic foliation. -/
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










/-! Holomorphic tangent subbundles yield holomorphic coordinate frames in manifold charts.
(Demailly, II §3.1, pp.85–86 and V §11, p.267) -/

open Set Bundle Filter
open scoped Topology _root_.Topology ContDiff

namespace HolomorphicAnosov.Theorem12NativeHolomorphicFrame

universe u

variable {d r : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- A holomorphic tangent subbundle admits a local holomorphic coordinate frame spanning its chart
derivative image. -/
private theorem exists_native_holomorphic_coordinate_frame
    (P : (y : X) → Submodule ℂ (TangentSpace (complexModel d) y))
    (hP : IsHolomorphicTangentSubbundle r P) (x : X) :
    ∃ (V : Set X) (s : Fin r → (y : X) → TangentSpace (complexModel d) y)
      (Y : Fin r → ComplexModel d → ComplexModel d),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (chartAt (ComplexModel d) x).source ∧
      IsHolomorphicTangentFrame V s ∧
      (∀ y ∈ V, Submodule.span ℂ (Set.range (fun i ↦ s i y)) = P y) ∧
      let Ω := (chartAt (ComplexModel d) x).target ∩
        (chartAt (ComplexModel d) x).symm ⁻¹' V
      IsOpen Ω ∧ chartAt (ComplexModel d) x x ∈ Ω ∧
      (∀ i, ContDiffOn ℂ ∞ (Y i) Ω) ∧
      (∀ z ∈ Ω, LinearIndependent ℂ (fun i ↦ Y i z)) ∧
      (∀ z ∈ Ω, ∀ i,
        Y i z = (mfderiv (complexModel d) (complexModel d)
          (extChartAt (complexModel d) x) ((chartAt (ComplexModel d) x).symm z))
          (s i ((chartAt (ComplexModel d) x).symm z))) ∧
      (∀ z ∈ Ω, Submodule.span ℂ (Set.range (fun i ↦ Y i z)) =
        (P ((chartAt (ComplexModel d) x).symm z)).map
          (mfderiv (complexModel d) (complexModel d) (extChartAt (complexModel d) x)
            ((chartAt (ComplexModel d) x).symm z)).toLinearMap) := by
  obtain ⟨U, s, hxU, hs, hspan⟩ := hP x
  let c := chartAt (ComplexModel d) x
  let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let V := U ∩ c.source
  let Ω := c.target ∩ c.symm ⁻¹' V
  let Y : Fin r → ComplexModel d → ComplexModel d :=
    fun i z ↦ (e ⟨c.symm z, s i (c.symm z)⟩).2
  have hV : IsOpen V := hs.1.inter c.open_source
  have hxV : x ∈ V := ⟨hxU, mem_chart_source (ComplexModel d) x⟩
  have hVs : V ⊆ c.source := inter_subset_right
  have hframe : IsHolomorphicTangentFrame V s :=
    ⟨hV, fun i ↦ (hs.2.1 i).mono inter_subset_left, fun y hy ↦ hs.2.2 y hy.1⟩
  have hspanV : ∀ y ∈ V, Submodule.span ℂ (Set.range (fun i ↦ s i y)) = P y :=
    fun y hy ↦ hspan y hy.1
  have hΩ : IsOpen Ω := c.isOpen_inter_preimage_symm hV
  have hxΩ : c x ∈ Ω := by
    refine ⟨c.map_source hxV.2, ?_⟩
    change c.symm (c x) ∈ V
    rw [c.left_inv hxV.2]
    exact hxV
  have hb : ∀ z ∈ Ω, c.symm z ∈ V := fun z hz ↦ hz.2
  have hcoord : ∀ z ∈ Ω, ∀ i, Y i z =
      (mfderiv (complexModel d) (complexModel d) (extChartAt (complexModel d) x)
        (c.symm z)) (s i (c.symm z)) := by
    intro z hz i
    have hbase : c.symm z ∈ e.baseSet := by
      simpa [e, TangentBundle.trivializationAt_baseSet] using (hb z hz).2
    change (e ⟨c.symm z, s i (c.symm z)⟩).2 = _
    rw [← e.continuousLinearMapAt_apply_of_mem ℂ hbase]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := complexModel d) (hb z hz).2]
    rfl
  have hY : ∀ i, ContDiffOn ℂ ∞ (Y i) Ω := by
    intro i
    have hcoeff : ContMDiffOn (complexModel d) (complexModel d) ∞
        (fun y ↦ (e ⟨y, s i y⟩).2) V := by
      apply (e.contMDiffOn_section_iff hV ?_).mp (hframe.2.1 i)
      intro y hy
      simpa [e, TangentBundle.trivializationAt_baseSet] using hy.2
    have hinv : ContMDiffOn (complexModel d) (complexModel d) ∞ c.symm Ω :=
      (contMDiffOn_chart_symm (I := complexModel d) (x := x)).mono inter_subset_left
    exact (hcoeff.comp hinv (fun z hz ↦ hb z hz)).contDiffOn
  have hLI : ∀ z ∈ Ω, LinearIndependent ℂ (fun i ↦ Y i z) := by
    intro z hz
    have hsource : c.symm z ∈ (extChartAt (complexModel d) x).source := by
      simpa only [extChartAt_source] using (hb z hz).2
    have hi := isInvertible_mfderiv_extChartAt (I := complexModel d) (x := x) hsource
    have hm := (hframe.2.2 (c.symm z) (hb z hz)).map'
      (mfderiv (complexModel d) (complexModel d) (extChartAt (complexModel d) x)
        (c.symm z)).toLinearMap
      (LinearMap.ker_eq_bot.mpr hi.bijective.injective)
    have heq : (fun i ↦ Y i z) = (fun i ↦
        (mfderiv (complexModel d) (complexModel d) (extChartAt (complexModel d) x)
          (c.symm z)) (s i (c.symm z))) := funext (hcoord z hz)
    rw [heq]
    exact hm
  refine ⟨V, s, Y, hV, hxV, hVs, hframe, hspanV, hΩ, hxΩ, hY, hLI, hcoord, ?_⟩
  intro z hz
  rw [← hspanV (c.symm z) (hb z hz), Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext i
  exact hcoord z hz i

end HolomorphicAnosov.Theorem12NativeHolomorphicFrame



/-! Projection normalization converts local involutive holomorphic frames into commuting frames.
(Lee, Thm 19.10, pp.501–502; Demailly, III, p.142) -/

open Set Filter
open scoped Topology _root_.Topology ContDiff

namespace HolomorphicAnosov.Theorem12NormalizedFrame

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The projected derivative vanishes when the projected field is locally constant. -/
private theorem projection_comp_fderiv_eq_zero (p : E →L[𝕜] F) {V : E → E} {x : E}
    (hV : DifferentiableAt 𝕜 V x) {c : F}
    (hc : (fun y ↦ p (V y)) =ᶠ[𝓝 x] (fun _ ↦ c)) :
    p.comp (fderiv 𝕜 V x) = 0 := by
  have hchain := (p.hasFDerivAt.comp x hV.hasFDerivAt).fderiv
  have hzero : fderiv 𝕜 (fun y ↦ p (V y)) x = 0 := by
    rw [hc.fderiv_eq]
    exact fderiv_const_apply c
  exact hchain.symm.trans hzero

/-- The projection of a Lie bracket vanishes when both projected fields are locally constant. -/
private theorem projection_lieBracket_eq_zero (p : E →L[𝕜] F) {V W : E → E} {x : E}
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) {v w : F}
    (hv : (fun y ↦ p (V y)) =ᶠ[𝓝 x] (fun _ ↦ v))
    (hw : (fun y ↦ p (W y)) =ᶠ[𝓝 x] (fun _ ↦ w)) :
    p (VectorField.lieBracket 𝕜 V W x) = 0 := by
  have hV0 := projection_comp_fderiv_eq_zero p hV hv
  have hW0 := projection_comp_fderiv_eq_zero p hW hw
  simp only [VectorField.lieBracket, map_sub]
  change (p.comp (fderiv 𝕜 W x)) (V x) - (p.comp (fderiv 𝕜 V x)) (W x) = 0
  rw [hV0, hW0]
  simp

/-- A bracket in a distribution vanishes if its projection is zero and the projection is injective
on that distribution. -/
private theorem lieBracket_eq_zero_of_projection (p : E →L[𝕜] F) (D : Submodule 𝕜 E)
    {V W : E → E} {x : E}
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) {v w : F}
    (hv : (fun y ↦ p (V y)) =ᶠ[𝓝 x] (fun _ ↦ v))
    (hw : (fun y ↦ p (W y)) =ᶠ[𝓝 x] (fun _ ↦ w))
    (hbracket : VectorField.lieBracket 𝕜 V W x ∈ D)
    (hinj : Set.InjOn p D) : VectorField.lieBracket 𝕜 V W x = 0 := by
  apply hinj hbracket D.zero_mem
  simpa using projection_lieBracket_eq_zero p hV hW hv hw

/-- The frame operator normalized by the inverse of its projected operator. -/
private noncomputable def normalizedOperator (p : E →L[𝕜] F) (s : E → F →L[𝕜] E)
    (x : E) : F →L[𝕜] E :=
  (s x).comp (p.comp (s x)).inverse

/-- The projection of the normalized frame is the identity where the projected operator is
invertible. -/
private theorem projection_normalizedOperator (p : E →L[𝕜] F) (s : E → F →L[𝕜] E)
    {x : E} (h : (p.comp (s x)).IsInvertible) (v : F) :
    p (normalizedOperator p s x v) = v := by
  exact h.self_apply_inverse v

/-- Normalization preserves the range of the frame operator. -/
private theorem range_normalizedOperator (p : E →L[𝕜] F) (s : E → F →L[𝕜] E)
    {x : E} (h : (p.comp (s x)).IsInvertible) :
    LinearMap.range (normalizedOperator p s x).toLinearMap = LinearMap.range (s x).toLinearMap := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(p.comp (s x)).inverse v, rfl⟩
  · rintro ⟨v, rfl⟩
    refine ⟨p (s x v), ?_⟩
    change s x ((p.comp (s x)).inverse ((p.comp (s x)) v)) = s x v
    rw [h.inverse_apply_self]

/-- The projection is injective on the frame range where the projected operator is invertible. -/
private theorem projection_injOn_range (p : E →L[𝕜] F) (s : E → F →L[𝕜] E)
    {x : E} (h : (p.comp (s x)).IsInvertible) :
    Set.InjOn p (LinearMap.range (s x).toLinearMap) := by
  rintro u ⟨a, rfl⟩ v ⟨b, rfl⟩ hab
  have hab' : (p.comp (s x)) a = (p.comp (s x)) b := hab
  exact congrArg (s x) (h.bijective.injective hab')

section Regularity

variable [CompleteSpace F]

/-- The normalized frame operator is complex smooth at points of invertibility. -/
private theorem normalizedOperator_contDiffAt (p : E →L[𝕜] F) (s : E → F →L[𝕜] E)
    {x : E} (hs : ContDiffAt 𝕜 ∞ s x) (h : (p.comp (s x)).IsInvertible) :
    ContDiffAt 𝕜 ∞ (normalizedOperator p s) x := by
  have hA : ContDiffAt 𝕜 ∞ (fun y ↦ p.comp (s y)) x :=
    contDiffAt_const.clm_comp hs
  have hinv : ContDiffAt 𝕜 ∞ ContinuousLinearMap.inverse (p.comp (s x)) :=
    h.contDiffAt_map_inverse
  have hi : ContDiffAt 𝕜 ∞ (fun y ↦ (p.comp (s y)).inverse) x :=
    by simpa only [Function.comp_def] using hinv.comp x hA
  exact hs.clm_comp hi

/-- Invertibility of the projected frame persists on an open neighborhood. -/
private theorem exists_open_normalization_domain (p : E →L[𝕜] F) (s : E → F →L[𝕜] E)
    {Ω : Set E} (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω)
    (hs : ContDiffOn 𝕜 ∞ s Ω) (h : (p.comp (s x)).IsInvertible) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      (∀ y ∈ V, (p.comp (s y)).IsInvertible) ∧
      ContDiffOn 𝕜 ∞ (normalizedOperator p s) V := by
  have hA : ContinuousAt (fun y ↦ p.comp (s y)) x :=
    (contDiffAt_const.clm_comp (hs.contDiffAt (hΩ.mem_nhds hx))).continuousAt
  have hi : ∀ᶠ y in 𝓝 x, (p.comp (s y)).IsInvertible :=
    hA.tendsto.eventually h.eventually_nhds
  have hgood : {y | y ∈ Ω ∧ (p.comp (s y)).IsInvertible} ∈ 𝓝 x := by
    filter_upwards [hΩ.mem_nhds hx, hi] with y hy hiy
    exact ⟨hy, hiy⟩
  rcases mem_nhds_iff.mp hgood with ⟨V, hVsub, hV, hxV⟩
  refine ⟨V, hV, hxV, fun y hy ↦ (hVsub hy).1, fun y hy ↦ (hVsub hy).2, ?_⟩
  intro y hy
  exact (normalizedOperator_contDiffAt p s
    (hs.contDiffAt (hΩ.mem_nhds (hVsub hy).1)) (hVsub hy).2).contDiffWithinAt

/-- Normalized fields are complex smooth and have constant projected components on the normalization
domain. -/
private theorem normalizedField_contDiffOn (p : E →L[𝕜] F) (s : E → F →L[𝕜] E)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : ContDiffOn 𝕜 ∞ s Ω)
    (hi : ∀ y ∈ Ω, (p.comp (s y)).IsInvertible) (v : F) :
    ContDiffOn 𝕜 ∞ (fun y ↦ normalizedOperator p s y v) Ω := by
  intro y hy
  exact ((normalizedOperator_contDiffAt p s
    (hs.contDiffAt (hΩ.mem_nhds hy)) (hi y hy)).clm_apply contDiffAt_const).contDiffWithinAt

/-- Normalized fields of an involutive distribution commute. -/
private theorem normalized_fields_commute (p : E →L[𝕜] F) (s : E → F →L[𝕜] E)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : ContDiffOn 𝕜 ∞ s Ω)
    (hi : ∀ y ∈ Ω, (p.comp (s y)).IsInvertible)
    (hinvol : ∀ V W : E → E,
      DifferentiableOn 𝕜 V Ω → DifferentiableOn 𝕜 W Ω →
      (∀ y ∈ Ω, V y ∈ LinearMap.range (s y).toLinearMap) →
      (∀ y ∈ Ω, W y ∈ LinearMap.range (s y).toLinearMap) →
      ∀ y ∈ Ω, VectorField.lieBracket 𝕜 V W y ∈ LinearMap.range (s y).toLinearMap)
    (v w : F) {x : E} (hx : x ∈ Ω) :
    VectorField.lieBracket 𝕜 (fun y ↦ normalizedOperator p s y v)
      (fun y ↦ normalizedOperator p s y w) x = 0 := by
  have hV := (normalizedField_contDiffOn p s hΩ hs hi v).differentiableOn (by simp)
  have hW := (normalizedField_contDiffOn p s hΩ hs hi w).differentiableOn (by simp)
  have hVmem : ∀ y ∈ Ω, normalizedOperator p s y v ∈ LinearMap.range (s y).toLinearMap :=
    fun y _ ↦ ⟨(p.comp (s y)).inverse v, rfl⟩
  have hWmem : ∀ y ∈ Ω, normalizedOperator p s y w ∈ LinearMap.range (s y).toLinearMap :=
    fun y _ ↦ ⟨(p.comp (s y)).inverse w, rfl⟩
  apply lieBracket_eq_zero_of_projection p (LinearMap.range (s x).toLinearMap)
    (hV.differentiableAt (hΩ.mem_nhds hx)) (hW.differentiableAt (hΩ.mem_nhds hx))
    (v := v) (w := w)
  · filter_upwards [hΩ.mem_nhds hx] with y hy
    exact projection_normalizedOperator p s (hi y hy) v
  · filter_upwards [hΩ.mem_nhds hx] with y hy
    exact projection_normalizedOperator p s (hi y hy) w
  · exact hinvol _ _ hV hW hVmem hWmem x hx
  · exact projection_injOn_range p s (hi x hx)

/-- An injective finite-dimensional frame admits a fixed continuous linear projection and an open
normalization domain. -/
private theorem exists_projection_and_normalization_domain [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (s : E → F →L[𝕜] E)
    {Ω : Set E} (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω)
    (hs : ContDiffOn 𝕜 ∞ s Ω) (hinj : Function.Injective (s x)) :
    ∃ (p : E →L[𝕜] F) (V : Set E),
      p.comp (s x) = ContinuousLinearMap.id 𝕜 F ∧
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      (∀ y ∈ V, (p.comp (s y)).IsInvertible) ∧
      ContDiffOn 𝕜 ∞ (normalizedOperator p s) V := by
  obtain ⟨p, hp⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  have hcomp : p.comp (s x) = ContinuousLinearMap.id 𝕜 F := by
    ext v
    exact hp v
  have hi : (p.comp (s x)).IsInvertible := by
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 F, rfl⟩
  obtain ⟨V, hV, hxV, hVsub, hiV, hsV⟩ := exists_open_normalization_domain p s hΩ hx hs hi
  exact ⟨p, V, hcomp, hV, hxV, hVsub, hiV, hsV⟩

end Regularity

section FiniteFrames

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuous linear operator taking frame coordinates to their finite linear combination. -/
private def frameOperator (Y : ι → E → E) (x : E) : (ι → 𝕜) →L[𝕜] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (Y i x)

omit [DecidableEq ι] in
@[local simp] private theorem frameOperator_apply (Y : ι → E → E) (x : E) (c : ι → 𝕜) :
    frameOperator (𝕜 := 𝕜) Y x c = ∑ i, c i • Y i x := by
  simp [frameOperator]

/-- The frame operator range is the span of the frame vectors. -/
private theorem frameOperator_range (Y : ι → E → E) (x : E) :
    LinearMap.range (frameOperator (𝕜 := 𝕜) Y x).toLinearMap =
      Submodule.span 𝕜 (Set.range (fun i ↦ Y i x)) := by
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    rw [ContinuousLinearMap.coe_coe, frameOperator_apply]
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp

omit [DecidableEq ι] in
/-- A linearly independent frame has an injective coordinate operator. -/
private theorem frameOperator_injective (Y : ι → E → E) {x : E}
    (hY : LinearIndependent 𝕜 (fun i ↦ Y i x)) : Function.Injective (frameOperator (𝕜 := 𝕜) Y x) := by
  intro a b hab
  have hzero : frameOperator (𝕜 := 𝕜) Y x (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [frameOperator_apply] at hzero
  have hc := Fintype.linearIndependent_iff.mp hY (a - b) hzero
  ext i
  exact sub_eq_zero.mp (hc i)

omit [DecidableEq ι] in
/-- A finite family of holomorphic fields defines a complex smooth frame operator. -/
private theorem frameOperator_contDiffOn (Y : ι → E → E) {Ω : Set E}
    (hY : ∀ i, ContDiffOn 𝕜 ∞ (Y i) Ω) : ContDiffOn 𝕜 ∞ (frameOperator (𝕜 := 𝕜) Y) Ω := by
  exact ContDiffOn.sum (fun i _ ↦ contDiffOn_const.smulRight (hY i))

omit [DecidableEq ι] in
/-- A finite holomorphic frame admits a fixed projection and an open normalization domain near a
point of independence. -/
private theorem finite_frame_normalization [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    (Y : ι → E → E) {Ω : Set E} (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω)
    (hY : ∀ i, ContDiffOn 𝕜 ∞ (Y i) Ω)
    (hind : LinearIndependent 𝕜 (fun i ↦ Y i x)) :
    ∃ (p : E →L[𝕜] (ι → 𝕜)) (V : Set E),
      p.comp (frameOperator (𝕜 := 𝕜) Y x) = ContinuousLinearMap.id 𝕜 (ι → 𝕜) ∧
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      (∀ y ∈ V, (p.comp (frameOperator (𝕜 := 𝕜) Y y)).IsInvertible) ∧
      ContDiffOn 𝕜 ∞ (normalizedOperator p (frameOperator (𝕜 := 𝕜) Y)) V :=
  exists_projection_and_normalization_domain (frameOperator (𝕜 := 𝕜) Y) hΩ hx
    (frameOperator_contDiffOn Y hY) (frameOperator_injective Y hind)

/-- A locally involutive holomorphic frame admits a commuting holomorphic normalization spanning the
same distribution. -/
private theorem exists_commuting_normalized_frame [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    (Y : ι → E → E) {Ω : Set E} (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω)
    (hY : ∀ i, ContDiffOn 𝕜 ∞ (Y i) Ω)
    (hind : LinearIndependent 𝕜 (fun i ↦ Y i x))
    (hinvol : ∀ y ∈ Ω, ∀ A B : E → E,
      DifferentiableAt 𝕜 A y → DifferentiableAt 𝕜 B y →
      (∀ᶠ z in 𝓝 y, A z ∈ Submodule.span 𝕜 (Set.range (fun i ↦ Y i z))) →
      (∀ᶠ z in 𝓝 y, B z ∈ Submodule.span 𝕜 (Set.range (fun i ↦ Y i z))) →
      VectorField.lieBracket 𝕜 A B y ∈ Submodule.span 𝕜 (Set.range (fun i ↦ Y i y))) :
    ∃ (p : E →L[𝕜] (ι → 𝕜)) (V : Set E), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ContDiffOn 𝕜 ∞ (normalizedOperator p (frameOperator (𝕜 := 𝕜) Y)) V ∧
      (∀ y ∈ V, LinearMap.range (normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) y).toLinearMap =
        Submodule.span 𝕜 (Set.range (fun i ↦ Y i y))) ∧
      (∀ y ∈ V, ∀ v, p (normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) y v) = v) ∧
      (∀ y ∈ V, ∀ v w,
        VectorField.lieBracket 𝕜
          (fun z ↦ normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) z v)
          (fun z ↦ normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) z w) y = 0) := by
  obtain ⟨p, V, _, hV, hxV, hVΩ, hiV, hsV⟩ :=
    finite_frame_normalization Y hΩ hx hY hind
  refine ⟨p, V, hV, hxV, hVΩ, hsV, ?_, ?_, ?_⟩
  · intro y hy
    rw [range_normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) (hiV y hy)]
    exact frameOperator_range Y y
  · intro y hy v
    exact projection_normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) (hiV y hy) v
  · intro y hy v w
    have hA : DifferentiableAt 𝕜
        (fun z ↦ normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) z v) y :=
      ((hsV.contDiffAt (hV.mem_nhds hy)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hB : DifferentiableAt 𝕜
        (fun z ↦ normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) z w) y :=
      ((hsV.contDiffAt (hV.mem_nhds hy)).clm_apply contDiffAt_const).differentiableAt (by simp)
    apply lieBracket_eq_zero_of_projection p
      (Submodule.span 𝕜 (Set.range (fun i ↦ Y i y))) hA hB (v := v) (w := w)
    · filter_upwards [hV.mem_nhds hy] with z hz
      exact projection_normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) (hiV z hz) v
    · filter_upwards [hV.mem_nhds hy] with z hz
      exact projection_normalizedOperator p (frameOperator (𝕜 := 𝕜) Y) (hiV z hz) w
    · apply hinvol y (hVΩ hy) _ _ hA hB
      · filter_upwards [hV.mem_nhds hy] with z hz
        rw [← frameOperator_range Y z]
        exact ⟨(p.comp (frameOperator (𝕜 := 𝕜) Y z)).inverse v, rfl⟩
      · filter_upwards [hV.mem_nhds hy] with z hz
        rw [← frameOperator_range Y z]
        exact ⟨(p.comp (frameOperator (𝕜 := 𝕜) Y z)).inverse w, rfl⟩
    · rw [← frameOperator_range Y y]
      exact projection_injOn_range p (frameOperator (𝕜 := 𝕜) Y) (hiV y hy)

end FiniteFrames

section ComplexRealBinding

variable {G : Type*} [NormedAddCommGroup G]
  [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]

/-- The real and complex Lie brackets of complex-differentiable fields agree. -/
private theorem real_lieBracket_eq_complex {V W : G → G} {x : G}
    (hV : DifferentiableAt ℂ V x) (hW : DifferentiableAt ℂ W x) :
    VectorField.lieBracket ℝ V W x = VectorField.lieBracket ℂ V W x := by
  simp only [VectorField.lieBracket, hV.fderiv_restrictScalars ℝ,
    hW.fderiv_restrictScalars ℝ]
  rfl

/-- Real bracket membership in the underlying real submodule implies complex bracket membership in
the complex submodule. -/
private theorem complex_bracket_mem_of_real {V W : G → G} {x : G} (D : Submodule ℂ G)
    (hV : DifferentiableAt ℂ V x) (hW : DifferentiableAt ℂ W x)
    (h : VectorField.lieBracket ℝ V W x ∈ D.restrictScalars ℝ) :
    VectorField.lieBracket ℂ V W x ∈ D := by
  change VectorField.lieBracket ℝ V W x ∈ D at h
  rwa [real_lieBracket_eq_complex hV hW] at h

end ComplexRealBinding

end HolomorphicAnosov.Theorem12NormalizedFrame








/-! Ordered complex flows from a transverse slice give local product coordinates. (Lee, Thm 19.10,
pp.501–502) -/

open Set Filter
open scoped Topology _root_.Topology ContDiff

namespace HolomorphicAnosov.Theorem12FlowCoordinates

noncomputable section

variable {E T ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup T] [NormedSpace ℂ T] [Fintype ι]

/-- The continuous linear sum equivalence of two injective complementary finite frames. -/
private def complementaryFrameEquiv [FiniteDimensional ℂ E] {r c : ℕ}
    (S : (Fin r → ℂ) →L[ℂ] E) (A : (Fin c → ℂ) →L[ℂ] E)
    (hS : Function.Injective S) (hA : Function.Injective A)
    (hcompl : IsCompl (LinearMap.range S.toLinearMap) (LinearMap.range A.toLinearMap)) :
    ((Fin r → ℂ) × (Fin c → ℂ)) ≃L[ℂ] E :=
  (((LinearEquiv.ofInjective S.toLinearMap hS).prodCongr
    (LinearEquiv.ofInjective A.toLinearMap hA)).trans
      (Submodule.prodEquivOfIsCompl _ _ hcompl)).toContinuousLinearEquiv

@[local simp] private theorem complementaryFrameEquiv_apply [FiniteDimensional ℂ E] {r c : ℕ}
    (S : (Fin r → ℂ) →L[ℂ] E) (A : (Fin c → ℂ) →L[ℂ] E)
    (hS : Function.Injective S) (hA : Function.Injective A)
    (hcompl : IsCompl (LinearMap.range S.toLinearMap) (LinearMap.range A.toLinearMap))
    (p : (Fin r → ℂ) × (Fin c → ℂ)) :
    complementaryFrameEquiv S A hS hA hcompl p = S p.1 + A p.2 := rfl

/-- A finite frame operator evaluates as the sum of its coordinate columns. -/
private theorem finite_frame_apply [DecidableEq ι] (S : (ι → ℂ) →L[ℂ] E) (u : ι → ℂ) :
    S u = ∑ i, u i • S (Pi.single i 1) := by
  have hu : u = ∑ i, u i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hu]
  simp

/-- The composition of listed flows from an affine transverse slice, with the head flow applied
last. -/
private def orderedMap (flow : ι → ℂ × E → E) (A : T →L[ℂ] E) (x : E) :
    List ι → ((ι → ℂ) × T) → E
  | [], p => x + A p.2
  | i :: L, p => flow i (p.1 i, orderedMap flow A x L p)

/-- The domain where every intermediate evaluation belongs to its flow's domain. -/
private def orderedDomain (flow : ι → ℂ × E → E) (A : T →L[ℂ] E) (x : E)
    (domain : ι → Set (ℂ × E)) : List ι → Set ((ι → ℂ) × T)
  | [] => univ
  | i :: L => orderedDomain flow A x domain L ∩
      (fun p => (p.1 i, orderedMap flow A x L p)) ⁻¹' domain i

/-- The combined operator of the ordered frame and transverse inclusion. -/
private def orderedDerivative (Y : ι → E) (A : T →L[ℂ] E) :
    List ι → ((ι → ℂ) × T) →L[ℂ] E
  | [] => A.comp (ContinuousLinearMap.snd ℂ (ι → ℂ) T)
  | i :: L => ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℂ (ι → ℂ) T)).smulRight (Y i) + orderedDerivative Y A L

/-- At zero time, the joint flow derivative is the sum of the spatial identity and the
time-direction vector field. -/
private theorem flow_hasFDerivAt_zero (φ : ℂ × E → E) (x v : E)
    (hφ : DifferentiableAt ℂ φ (0, x))
    (hzero : (fun y => φ (0, y)) =ᶠ[𝓝 x] id)
    (htime : HasDerivAt (fun t => φ (t, x)) v 0) :
    HasFDerivAt φ
      ((ContinuousLinearMap.fst ℂ ℂ E).smulRight v +
        ContinuousLinearMap.snd ℂ ℂ E) (0, x) := by
  have hd := hφ.hasFDerivAt
  have hleft := hd.comp (0 : ℂ) (hasFDerivAt_prodMk_left (𝕜 := ℂ) (0 : ℂ) x)
  have hright := hd.comp x (hasFDerivAt_prodMk_right (𝕜 := ℂ) (0 : ℂ) x)
  have hl := hleft.unique htime.hasFDerivAt
  have hr := hright.unique ((hasFDerivAt_id x).congr_of_eventuallyEq hzero)
  have heq : fderiv ℂ φ (0, x) =
      (ContinuousLinearMap.fst ℂ ℂ E).smulRight v +
        ContinuousLinearMap.snd ℂ ℂ E := by
    apply ContinuousLinearMap.ext
    intro p
    have hp : p = (p.1, (0 : E)) + (0, p.2) := by simp
    rw [hp, map_add]
    have hlp := congrArg (fun D : ℂ →L[ℂ] E => D p.1) hl
    have hrp := congrArg (fun D : E →L[ℂ] E => D p.2) hr
    simpa using congrArg₂ (fun a b : E => a + b) hlp hrp
  exact heq ▸ hd

/-- The ordered flow domain is open, and the ordered composition is complex smooth there. -/
private theorem orderedDomain_open_smooth (flow : ι → ℂ × E → E) (A : T →L[ℂ] E) (x : E)
    (domain : ι → Set (ℂ × E)) (hopen : ∀ i, IsOpen (domain i))
    (hsmooth : ∀ i, ContDiffOn ℂ ∞ (flow i) (domain i)) (L : List ι) :
    IsOpen (orderedDomain flow A x domain L) ∧
      ContDiffOn ℂ ∞ (orderedMap flow A x L) (orderedDomain flow A x domain L) := by
  induction L with
  | nil =>
    exact ⟨isOpen_univ, (contDiff_const.add (A.contDiff.comp contDiff_snd)).contDiffOn⟩
  | cons i L ih =>
    have hc : ContDiffOn ℂ ∞
        (fun p : (ι → ℂ) × T => (p.1 i, orderedMap flow A x L p))
        (orderedDomain flow A x domain L) :=
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).contDiff.comp
        contDiff_fst).contDiffOn).prodMk ih.2
    refine ⟨hc.continuousOn.isOpen_inter_preimage ih.1 (hopen i), ?_⟩
    exact (hsmooth i).comp (hc.mono inter_subset_left) (fun p hp => hp.2)

omit [Fintype ι] in
/-- The ordered flow map sends zero coordinates to the base point. -/
private theorem orderedMap_zero (flow : ι → ℂ × E → E) (A : T →L[ℂ] E) (x : E)
    (hzero : ∀ i, flow i (0, x) = x) (L : List ι) :
    orderedMap flow A x L 0 = x := by
  induction L with
  | nil => simp [orderedMap]
  | cons i L ih => simpa [orderedMap, ih] using hzero i

omit [Fintype ι] in
/-- The origin belongs to the ordered flow domain. -/
private theorem zero_mem_orderedDomain (flow : ι → ℂ × E → E) (A : T →L[ℂ] E) (x : E)
    (domain : ι → Set (ℂ × E)) (hmem : ∀ i, (0, x) ∈ domain i)
    (hzero : ∀ i, flow i (0, x) = x) (L : List ι) :
    0 ∈ orderedDomain flow A x domain L := by
  induction L with
  | nil => trivial
  | cons i L ih =>
    exact ⟨ih, by simpa [orderedMap_zero flow A x hzero] using hmem i⟩

/-- The derivative of the ordered flow map at zero is the combined frame and transverse operator. -/
private theorem orderedMap_hasFDerivAt_zero (flow : ι → ℂ × E → E) (Y : ι → E)
    (A : T →L[ℂ] E) (x : E)
    (hφ : ∀ i, DifferentiableAt ℂ (flow i) (0, x))
    (hzero : ∀ i, (fun y => flow i (0, y)) =ᶠ[𝓝 x] id)
    (htime : ∀ i, HasDerivAt (fun t => flow i (t, x)) (Y i) 0) (L : List ι) :
    HasFDerivAt (orderedMap flow A x L) (orderedDerivative Y A L) 0 := by
  have hz : ∀ i, flow i (0, x) = x := fun i => (hzero i).self_of_nhds
  induction L with
  | nil =>
    change HasFDerivAt (fun p : (ι → ℂ) × T => x + A p.2)
      (A.comp (ContinuousLinearMap.snd ℂ (ι → ℂ) T)) 0
    convert! (A.comp (ContinuousLinearMap.snd ℂ (ι → ℂ) T)).hasFDerivAt.const_add x
  | cons i L ih =>
    have hp := (((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℂ (ι → ℂ) T)).hasFDerivAt (x := 0)).prodMk ih
    have houter : HasFDerivAt (flow i)
        ((ContinuousLinearMap.fst ℂ ℂ E).smulRight (Y i) +
          ContinuousLinearMap.snd ℂ ℂ E)
        ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.fst ℂ (ι → ℂ) T) 0, orderedMap flow A x L 0) := by
      simpa [orderedMap_zero flow A x hz L] using
        flow_hasFDerivAt_zero (flow i) x (Y i) (hφ i) (hzero i) (htime i)
    have hf := houter.comp (0 : (ι → ℂ) × T) hp
    convert hf using 1 <;> ext p <;> simp [orderedMap, orderedDerivative]

omit [Fintype ι] in
/-- The ordered derivative evaluates as the frame sum plus the transverse inclusion. -/
private theorem orderedDerivative_apply (Y : ι → E) (A : T →L[ℂ] E)
    (L : List ι) (p : (ι → ℂ) × T) :
    orderedDerivative Y A L p = (L.map (fun i => p.1 i • Y i)).sum + A p.2 := by
  induction L with
  | nil => simp [orderedDerivative]
  | cons i L ih => simp [orderedDerivative, ih, add_assoc]

/-- Ordered complex flows with an invertible combined frame and transverse operator define a local
complex product chart. (Lee, Thms 18.6 and 19.10, pp.471–472 and 501–502) -/
private theorem exists_ordered_flow_chart [CompleteSpace E] [CompleteSpace T]
    (flow : ι → ℂ × E → E) (Y : ι → E) (A : T →L[ℂ] E) (x : E)
    (domain : ι → Set (ℂ × E)) (hopen : ∀ i, IsOpen (domain i))
    (hmem : ∀ i, (0, x) ∈ domain i)
    (hsmooth : ∀ i, ContDiffOn ℂ ∞ (flow i) (domain i))
    (hzero : ∀ i, (fun y => flow i (0, y)) =ᶠ[𝓝 x] id)
    (htime : ∀ i, HasDerivAt (fun t => flow i (t, x)) (Y i) 0)
    (L : List ι) (e : ((ι → ℂ) × T) ≃L[ℂ] E)
    (hcomplement : ∀ p, e p = (L.map (fun i => p.1 i • Y i)).sum + A p.2) :
    ∃ (U : Set (ι → ℂ)) (W : Set T)
      (c : OpenPartialHomeomorph ((ι → ℂ) × T) E),
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ 0 ∈ W ∧
      c.source = U ×ˢ W ∧ c.source ⊆ orderedDomain flow A x domain L ∧
      (c : ((ι → ℂ) × T) → E) = orderedMap flow A x L ∧ c 0 = x ∧
      x ∈ c.target ∧ ContDiffOn ℂ ∞ c c.source ∧
      ContDiffOn ℂ ∞ c.symm c.target ∧
      HasFDerivAt (orderedMap flow A x L) (e : ((ι → ℂ) × T) →L[ℂ] E) 0 := by
  have hz : ∀ i, flow i (0, x) = x := fun i => (hzero i).self_of_nhds
  have hbase := zero_mem_orderedDomain flow A x domain hmem hz L
  obtain ⟨hDopen, hDdiff⟩ := orderedDomain_open_smooth flow A x domain hopen hsmooth L
  have hAt := hDdiff.contDiffAt (hDopen.mem_nhds hbase)
  have hderiv := orderedMap_hasFDerivAt_zero flow Y A x
    (fun i => ((hsmooth i).contDiffAt ((hopen i).mem_nhds (hmem i))).differentiableAt
      (by simp)) hzero htime L
  have hop : orderedDerivative Y A L = (e : ((ι → ℂ) × T) →L[ℂ] E) := by
    apply ContinuousLinearMap.ext
    intro p
    exact (orderedDerivative_apply Y A L p).trans (hcomplement p).symm
  rw [hop] at hderiv
  let c₀ := hAt.toOpenPartialHomeomorph (orderedMap flow A x L) hderiv (by simp)
  have h₀ : (0 : (ι → ℂ) × T) ∈ c₀.source :=
    hAt.mem_toOpenPartialHomeomorph_source hderiv (by simp)
  have hinv : (fderiv ℂ (orderedMap flow A x L) 0).IsInvertible := by
    rw [hderiv.fderiv]
    exact ⟨e, rfl⟩
  have hnear : ∀ᶠ p in 𝓝 (0 : (ι → ℂ) × T),
      (fderiv ℂ (orderedMap flow A x L) p).IsInvertible :=
    (hAt.continuousAt_fderiv (by simp)).eventually hinv.eventually_nhds
  have hgood : {p | p ∈ c₀.source ∧ p ∈ orderedDomain flow A x domain L ∧
      (fderiv ℂ (orderedMap flow A x L) p).IsInvertible} ∈ 𝓝 (0 : (ι → ℂ) × T) := by
    filter_upwards [c₀.open_source.mem_nhds h₀, hDopen.mem_nhds hbase, hnear]
      with p hp hdp hip
    exact ⟨hp, hdp, hip⟩
  obtain ⟨U, W, hU, h0U, hW, h0W, hprod⟩ := mem_nhds_prod_iff'.mp hgood
  let c := c₀.restrOpen (U ×ˢ W) (hU.prod hW)
  have hsub : U ×ˢ W ⊆ c₀.source := fun p hp => (hprod hp).1
  have hsource : c.source = U ×ˢ W := by
    exact inter_eq_right.mpr hsub
  have hcoe : (c : ((ι → ℂ) × T) → E) = orderedMap flow A x L := rfl
  have h0c : (0 : (ι → ℂ) × T) ∈ c.source := by rw [hsource]; exact ⟨h0U, h0W⟩
  have hcx : c 0 = x := orderedMap_zero flow A x hz L
  refine ⟨U, W, c, hU, h0U, hW, h0W, hsource, ?_, hcoe, hcx, ?_, ?_, ?_, hderiv⟩
  · intro p hp
    exact (hprod (hsource ▸ hp)).2.1
  · rw [← hcx]
    exact c.map_source h0c
  · exact hcoe ▸ hDdiff.mono (fun p hp => (hprod (hsource ▸ hp)).2.1)
  · intro y hy
    have hq : c.symm y ∈ U ×ˢ W := hsource ▸ c.map_target hy
    have hqD := (hprod hq).2.1
    have hqs := hDdiff.contDiffAt (hDopen.mem_nhds hqD)
    obtain ⟨eqv, heqv⟩ := (hprod hq).2.2
    have hqd : HasFDerivAt c (eqv : ((ι → ℂ) × T) →L[ℂ] E) (c.symm y) := by
      rw [hcoe, heqv]
      exact hqs.differentiableAt (by simp) |>.hasFDerivAt
    exact (c.contDiffAt_symm hy hqd (hcoe ▸ hqs)).contDiffWithinAt

/-- A finite ordered family of complex flows defines a local product chart when its frame and
transverse directions are complementary. -/
private theorem exists_finite_flow_chart [CompleteSpace E] [CompleteSpace T] {n : ℕ}
    (flow : Fin n → ℂ × E → E) (Y : Fin n → E) (A : T →L[ℂ] E) (x : E)
    (domain : Fin n → Set (ℂ × E)) (hopen : ∀ i, IsOpen (domain i))
    (hmem : ∀ i, (0, x) ∈ domain i)
    (hsmooth : ∀ i, ContDiffOn ℂ ∞ (flow i) (domain i))
    (hzero : ∀ i, (fun y => flow i (0, y)) =ᶠ[𝓝 x] id)
    (htime : ∀ i, HasDerivAt (fun t => flow i (t, x)) (Y i) 0)
    (e : ((Fin n → ℂ) × T) ≃L[ℂ] E)
    (hcomplement : ∀ p, e p = (∑ i, p.1 i • Y i) + A p.2) :
    ∃ (U : Set (Fin n → ℂ)) (W : Set T)
      (c : OpenPartialHomeomorph ((Fin n → ℂ) × T) E),
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ 0 ∈ W ∧
      c.source = U ×ˢ W ∧
      c.source ⊆ orderedDomain flow A x domain (List.ofFn id) ∧
      (c : ((Fin n → ℂ) × T) → E) = orderedMap flow A x (List.ofFn id) ∧
      c 0 = x ∧ x ∈ c.target ∧ ContDiffOn ℂ ∞ c c.source ∧
      ContDiffOn ℂ ∞ c.symm c.target ∧
      HasFDerivAt (orderedMap flow A x (List.ofFn id))
        (e : ((Fin n → ℂ) × T) →L[ℂ] E) 0 := by
  apply exists_ordered_flow_chart flow Y A x domain hopen hmem hsmooth hzero htime
    (List.ofFn id) e
  intro p
  simpa [List.map_ofFn, List.sum_ofFn] using hcomplement p

omit [NormedSpace ℂ E] in
/-- The zero-time identity holds as a germ near an interior point of the flow domain. -/
private theorem zero_time_germ (φ : ℂ × E → E) {D : Set (ℂ × E)} (hD : IsOpen D)
    {x : E} (hx : (0, x) ∈ D) (hzero : ∀ y, (0, y) ∈ D → φ (0, y) = y) :
    (fun y => φ (0, y)) =ᶠ[𝓝 x] id := by
  have hc : ContinuousAt (fun y : E => ((0 : ℂ), y)) x :=
    continuousAt_const.prodMk continuousAt_id
  filter_upwards [hc.eventually (hD.mem_nhds hx)] with y hy
  exact hzero y hy

/-- With an empty frame, the ordered map is the affine transverse map. -/
private theorem orderedMap_rank_zero (flow : Fin 0 → ℂ × E → E)
    (A : T →L[ℂ] E) (x : E) (p : (Fin 0 → ℂ) × T) :
    orderedMap flow A x (List.ofFn id) p = x + A p.2 := by
  simp [orderedMap]

/-- Complex flows of complementary finite frames give local complex product coordinates. -/
private theorem exists_finite_flow_chart_of_complementary_frames
    [FiniteDimensional ℂ E] {r c : ℕ}
    (S : (Fin r → ℂ) →L[ℂ] E) (A : (Fin c → ℂ) →L[ℂ] E)
    (hS : Function.Injective S) (hA : Function.Injective A)
    (hcompl : IsCompl (LinearMap.range S.toLinearMap) (LinearMap.range A.toLinearMap))
    (flow : Fin r → ℂ × E → E) (x : E)
    (domain : Fin r → Set (ℂ × E)) (hopen : ∀ i, IsOpen (domain i))
    (hmem : ∀ i, (0, x) ∈ domain i)
    (hsmooth : ∀ i, ContDiffOn ℂ ∞ (flow i) (domain i))
    (hzero : ∀ i, (fun y => flow i (0, y)) =ᶠ[𝓝 x] id)
    (htime : ∀ i, HasDerivAt (fun t => flow i (t, x)) (S (Pi.single i 1)) 0) :
    ∃ (U : Set (Fin r → ℂ)) (W : Set (Fin c → ℂ))
      (chart : OpenPartialHomeomorph ((Fin r → ℂ) × (Fin c → ℂ)) E),
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ 0 ∈ W ∧
      chart.source = U ×ˢ W ∧
      chart.source ⊆ orderedDomain flow A x domain (List.ofFn id) ∧
      (chart : ((Fin r → ℂ) × (Fin c → ℂ)) → E) =
        orderedMap flow A x (List.ofFn id) ∧
      chart 0 = x ∧ x ∈ chart.target ∧
      ContDiffOn ℂ ∞ chart chart.source ∧ ContDiffOn ℂ ∞ chart.symm chart.target ∧
      HasFDerivAt (orderedMap flow A x (List.ofFn id)) (S.coprod A) 0 := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  let e := complementaryFrameEquiv S A hS hA hcompl
  have he : ∀ p, e p = (∑ i, p.1 i • S (Pi.single i 1)) + A p.2 := by
    intro p
    exact congrArg (fun v => v + A p.2) (finite_frame_apply S p.1)
  obtain ⟨U, W, chart, hU, h0U, hW, h0W, hsource, hvalid, hcoe, hcx,
      hx, hdiff, hinv, hderiv⟩ := exists_finite_flow_chart flow
        (fun i => S (Pi.single i 1)) A x domain hopen hmem hsmooth hzero htime e he
  have heq : (e : ((Fin r → ℂ) × (Fin c → ℂ)) →L[ℂ] E) = S.coprod A := rfl
  rw [heq] at hderiv
  exact ⟨U, W, chart, hU, h0U, hW, h0W, hsource, hvalid, hcoe, hcx,
    hx, hdiff, hinv, hderiv⟩

end
end HolomorphicAnosov.Theorem12FlowCoordinates



/-! Ordered flows preserving the frame fields straighten their distribution. (Lee, Thms 18.6 and
19.10, pp.471–472 and 501–502) -/

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Theorem12FlowStraightening
noncomputable section

variable {E T ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup T] [NormedSpace ℂ T] [Fintype ι] [DecidableEq ι]

open HolomorphicAnosov.Theorem12FlowCoordinates

/-- The joint flow derivative in the time direction equals the vector field. -/
private theorem joint_time_derivative (φ : ℂ × E → E) {t : ℂ} {x v : E}
    (hφ : DifferentiableAt ℂ φ (t, x))
    (ht : HasDerivAt (fun s => φ (s, x)) v t) :
    fderiv ℂ φ (t, x) (1, 0) = v := by
  have h := hφ.hasFDerivAt.comp t (hasFDerivAt_prodMk_left (𝕜 := ℂ) t x)
  have he := h.unique ht.hasFDerivAt
  simpa using congrArg (fun D : ℂ →L[ℂ] E => D 1) he

/-- The joint flow derivative in a spatial direction equals the spatial slice derivative. -/
private theorem joint_spatial_derivative (φ : ℂ × E → E) {t : ℂ} {x : E}
    (hφ : DifferentiableAt ℂ φ (t, x)) (v : E) :
    fderiv ℂ φ (t, x) (0, v) = fderiv ℂ (fun y => φ (t, y)) x v := by
  have h := hφ.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℂ) t x)
  exact (congrArg (fun D : E →L[ℂ] E => D v) h.fderiv).symm

/-- Composition preserves a vector field when both differentiable maps preserve it. -/
private theorem field_preservation_comp (φ ψ : E → E) (Y : E → E) {x : E}
    (hφ : DifferentiableAt ℂ φ (ψ x)) (hψ : DifferentiableAt ℂ ψ x)
    (hpresφ : fderiv ℂ φ (ψ x) (Y (ψ x)) = Y (φ (ψ x)))
    (hpresψ : fderiv ℂ ψ x (Y x) = Y (ψ x)) :
    fderiv ℂ (φ ∘ ψ) x (Y x) = Y (φ (ψ x)) := by
  rw [(hφ.hasFDerivAt.comp x hψ.hasFDerivAt).fderiv]
  change fderiv ℂ φ (ψ x) (fderiv ℂ ψ x (Y x)) = _
  rw [hpresψ, hpresφ]

section RealBinding
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- A real field-preservation identity also holds for the complex derivative of a
complex-differentiable map. -/
private theorem complex_field_preservation_of_real (φ Y : E → E) {x : E}
    (hφ : DifferentiableAt ℂ φ x)
    (hreal : fderiv ℝ φ x (Y x) = Y (φ x)) :
    fderiv ℂ φ x (Y x) = Y (φ x) := by
  rw [hφ.fderiv_restrictScalars ℝ] at hreal
  exact hreal

end RealBinding

/-- For a list of distinct flow indices, each listed horizontal derivative column equals its field
at the final point, and unlisted columns vanish. -/
private theorem orderedMap_horizontal_derivative
    (flow : ι → ℂ × E → E) (Y : ι → E → E) (A : T →L[ℂ] E) (x : E)
    (domain : ι → Set (ℂ × E))
    (hjoint : ∀ i q, q ∈ domain i → DifferentiableAt ℂ (flow i) q)
    (hODE : ∀ i q, q ∈ domain i →
      HasDerivAt (fun t => flow i (t, q.2)) (Y i (flow i q)) q.1)
    (hpreserve : ∀ i j, i ≠ j → ∀ q, q ∈ domain i →
      fderiv ℂ (fun y => flow i (q.1, y)) q.2 (Y j q.2) = Y j (flow i q))
    (L : List ι) (hL : L.Nodup) {p : (ι → ℂ) × T}
    (hp : p ∈ orderedDomain flow A x domain L) :
    DifferentiableAt ℂ (orderedMap flow A x L) p ∧
      ∀ j, fderiv ℂ (orderedMap flow A x L) p (Pi.single j 1, 0) =
        if j ∈ L then Y j (orderedMap flow A x L p) else 0 := by
  induction L generalizing p with
  | nil =>
    have hd : HasFDerivAt (orderedMap flow A x [])
        (A.comp (ContinuousLinearMap.snd ℂ (ι → ℂ) T)) p := by
      convert! (A.comp (ContinuousLinearMap.snd ℂ (ι → ℂ) T)).hasFDerivAt.const_add x
    refine ⟨hd.differentiableAt, fun j => ?_⟩
    rw [hd.fderiv]
    simp
  | cons i L ih =>
    obtain ⟨hiL, hL⟩ := List.nodup_cons.mp hL
    obtain ⟨hdt, hcol⟩ := ih hL hp.1
    have hpair := (((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℂ (ι → ℂ) T)).hasFDerivAt (x := p)).prodMk
        hdt.hasFDerivAt
    have hd : HasFDerivAt (orderedMap flow A x (i :: L))
        ((fderiv ℂ (flow i) (p.1 i, orderedMap flow A x L p)).comp
          (((ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.fst ℂ (ι → ℂ) T)).prod
              (fderiv ℂ (orderedMap flow A x L) p))) p := by
      convert! (hjoint i _ hp.2).hasFDerivAt.comp p hpair
    refine ⟨hd.differentiableAt, fun j => ?_⟩
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.proj_apply]
    change fderiv ℂ (flow i) (p.1 i, orderedMap flow A x L p)
      ((Pi.single j 1 : ι → ℂ) i,
        fderiv ℂ (orderedMap flow A x L) p (Pi.single j 1, 0)) = _
    by_cases hji : j = i
    · subst j
      rw [hcol]
      simp only [hiL, ↓reduceIte]
      simpa [orderedMap] using joint_time_derivative (flow i) (hjoint i _ hp.2)
        (hODE i _ hp.2)
    · have hij : i ≠ j := Ne.symm hji
      rw [Pi.single_eq_of_ne hij, hcol]
      by_cases hjL : j ∈ L
      · simp only [hjL, ↓reduceIte]
        rw [joint_spatial_derivative (flow i) (hjoint i _ hp.2)]
        simpa [orderedMap, hji, hjL] using hpreserve i j hij _ hp.2
      · simp [hjL, hji]
        exact map_zero _

/-- The range of a finite coordinate operator is the span of its columns. -/
private theorem range_eq_span_of_columns (D : (ι → ℂ) →L[ℂ] E) (Y : ι → E)
    (hcol : ∀ i, D (Pi.single i 1) = Y i) :
    LinearMap.range D.toLinearMap = Submodule.span ℂ (Set.range Y) := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    have hu : u = ∑ i, u i • Pi.single i 1 := by
      ext j
      simp [Pi.single_apply]
    change D u ∈ Submodule.span ℂ (Set.range Y)
    rw [hu, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul, hcol]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact ⟨Pi.single i 1, hcol i⟩

/-- The finite ordered flow derivative maps the horizontal tangent space onto the span of the fields
at its image. -/
private theorem finite_orderedMap_horizontal_range {n : ℕ}
    (flow : Fin n → ℂ × E → E) (Y : Fin n → E → E) (A : T →L[ℂ] E) (x : E)
    (domain : Fin n → Set (ℂ × E))
    (hjoint : ∀ i q, q ∈ domain i → DifferentiableAt ℂ (flow i) q)
    (hODE : ∀ i q, q ∈ domain i →
      HasDerivAt (fun t => flow i (t, q.2)) (Y i (flow i q)) q.1)
    (hpreserve : ∀ i j, i ≠ j → ∀ q, q ∈ domain i →
      fderiv ℂ (fun y => flow i (q.1, y)) q.2 (Y j q.2) = Y j (flow i q))
    {p : (Fin n → ℂ) × T}
    (hp : p ∈ orderedDomain flow A x domain (List.ofFn id)) :
    DifferentiableAt ℂ (orderedMap flow A x (List.ofFn id)) p ∧
      LinearMap.range ((fderiv ℂ (orderedMap flow A x (List.ofFn id)) p).comp
        (ContinuousLinearMap.inl ℂ (Fin n → ℂ) T)).toLinearMap =
      Submodule.span ℂ (Set.range (fun i => Y i (orderedMap flow A x (List.ofFn id) p))) := by
  have hnodup : (List.ofFn (id : Fin n → Fin n)).Nodup :=
    List.nodup_ofFn_ofInjective Function.injective_id
  obtain ⟨hd, hc⟩ := orderedMap_horizontal_derivative flow Y A x domain hjoint hODE
    hpreserve (List.ofFn id) hnodup hp
  refine ⟨hd, range_eq_span_of_columns _ _ (fun i => ?_)⟩
  simpa using hc i

omit [Fintype ι] [DecidableEq ι] in
/-- A left inverse maps the image of the horizontal subspace back onto that subspace. -/
private theorem inverse_maps_horizontal_range (D : ((ι → ℂ) × T) →L[ℂ] E)
    (B : E →L[ℂ] ((ι → ℂ) × T))
    (hleft : B.comp D = ContinuousLinearMap.id ℂ ((ι → ℂ) × T)) :
    (LinearMap.range (D.comp (ContinuousLinearMap.inl ℂ (ι → ℂ) T)).toLinearMap).map
      B.toLinearMap = LinearMap.range (ContinuousLinearMap.inl ℂ (ι → ℂ) T).toLinearMap := by
  ext v
  constructor
  · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
    refine ⟨u, ?_⟩
    exact (congrArg (fun C : ((ι → ℂ) × T) →L[ℂ] ((ι → ℂ) × T) => C (u, 0)) hleft).symm
  · rintro ⟨u, rfl⟩
    refine ⟨D (u, 0), ⟨u, rfl⟩, ?_⟩
    exact congrArg (fun C : ((ι → ℂ) × T) →L[ℂ] ((ι → ℂ) × T) => C (u, 0)) hleft

omit [DecidableEq ι] in
/-- The derivatives of a chart and its inverse compose to the identity. -/
private theorem chart_derivatives_left_inverse
    (c : OpenPartialHomeomorph ((ι → ℂ) × T) E) {p : (ι → ℂ) × T}
    (hp : p ∈ c.source) (hc : DifferentiableAt ℂ c p)
    (hinv : DifferentiableAt ℂ c.symm (c p)) :
    (fderiv ℂ c.symm (c p)).comp (fderiv ℂ c p) =
      ContinuousLinearMap.id ℂ ((ι → ℂ) × T) := by
  have hd := hinv.hasFDerivAt.comp p hc.hasFDerivAt
  exact hd.unique ((hasFDerivAt_id p).congr_of_eventuallyEq (c.eventually_left_inverse hp))

/-- The inverse finite flow chart sends the field distribution to the horizontal tangent space
throughout its domain. -/
private theorem finite_flow_chart_inverse_straightens {n : ℕ}
    (flow : Fin n → ℂ × E → E) (Y : Fin n → E → E) (A : T →L[ℂ] E) (x : E)
    (domain : Fin n → Set (ℂ × E))
    (hjoint : ∀ i q, q ∈ domain i → DifferentiableAt ℂ (flow i) q)
    (hODE : ∀ i q, q ∈ domain i →
      HasDerivAt (fun t => flow i (t, q.2)) (Y i (flow i q)) q.1)
    (hpreserve : ∀ i j, i ≠ j → ∀ q, q ∈ domain i →
      fderiv ℂ (fun y => flow i (q.1, y)) q.2 (Y j q.2) = Y j (flow i q))
    (c : OpenPartialHomeomorph ((Fin n → ℂ) × T) E)
    (hmap : (c : ((Fin n → ℂ) × T) → E) = orderedMap flow A x (List.ofFn id))
    (hguards : c.source ⊆ orderedDomain flow A x domain (List.ofFn id))
    (hinv : DifferentiableOn ℂ c.symm c.target)
    (P : E → Submodule ℂ E)
    (hspan : ∀ y ∈ c.target, P y = Submodule.span ℂ (Set.range (fun i => Y i y)))
    {y : E} (hy : y ∈ c.target) :
    (P y).map (fderiv ℂ c.symm y).toLinearMap =
      LinearMap.range (ContinuousLinearMap.inl ℂ (Fin n → ℂ) T).toLinearMap := by
  have hp := c.map_target hy
  obtain ⟨hd, hrange⟩ := finite_orderedMap_horizontal_range flow Y A x domain
    hjoint hODE hpreserve (hguards hp)
  have hc : DifferentiableAt ℂ c (c.symm y) := hmap ▸ hd
  have hi := hinv.differentiableAt (c.open_target.mem_nhds hy)
  have hleft := chart_derivatives_left_inverse c hp hc
    (by simpa only [c.right_inv hy] using hi)
  have hlinear := inverse_maps_horizontal_range (fderiv ℂ c (c.symm y))
    (fderiv ℂ c.symm y) (by simpa only [c.right_inv hy] using hleft)
  rw [hmap] at hlinear
  rw [hrange] at hlinear
  simpa only [← hmap, c.right_inv hy, ← hspan y hy] using hlinear

end
end HolomorphicAnosov.Theorem12FlowStraightening



/-! Affine restrictions normalize holomorphic product charts to unit product boxes. (Nisoli,
pp.9–10) -/

open Set
open scoped Topology _root_.Topology ContDiff Manifold

namespace HolomorphicAnosov.Theorem12UnitProductBox

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Translation followed by the same positive complex-linear dilation in both factors. -/
private noncomputable def blockAffine (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) :
    (E × F) ≃ₜ (E × F) where
  toFun z := (ρ : ℂ)⁻¹ • (z - a)
  invFun z := a + (ρ : ℂ) • z
  left_inv z := by
    have hc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
    change a + (ρ : ℂ) • ((ρ : ℂ)⁻¹ • (z - a)) = z
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    abel
  right_inv z := by
    have hc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
    change (ρ : ℂ)⁻¹ • (a + (ρ : ℂ) • z - a) = z
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[local simp] private theorem blockAffine_apply (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) (z) :
    blockAffine a ρ hρ z = (ρ : ℂ)⁻¹ • (z - a) := rfl

@[local simp] private theorem blockAffine_symm_apply (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) (z) :
    (blockAffine a ρ hρ).symm z = a + (ρ : ℂ) • z := rfl

 private theorem blockAffine_contDiff (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℂ ∞ (blockAffine a ρ hρ) :=
  by
    change ContDiff ℂ ∞ (fun z : E × F ↦ (ρ : ℂ)⁻¹ • (z - a))
    fun_prop

 private theorem blockAffine_symm_contDiff (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℂ ∞ (blockAffine a ρ hρ).symm :=
  by
    change ContDiff ℂ ∞ (fun z : E × F ↦ a + (ρ : ℂ) • z)
    fun_prop

/-- Block-affine normalization preserves equality of transverse coordinates. -/
private theorem blockAffine_transverse_eq_iff (a : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    (z w : E × F) :
    (blockAffine a ρ hρ z).2 = (blockAffine a ρ hρ w).2 ↔ z.2 = w.2 := by
  have hc : (ρ : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne')
  change (ρ : ℂ)⁻¹ • (z.2 - a.2) = (ρ : ℂ)⁻¹ • (w.2 - a.2) ↔ _
  rw [smul_right_inj hc, sub_left_inj]

/-- The derivative of block-affine normalization is uniform dilation. -/
private theorem blockAffine_hasFDerivAt (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) (z : E × F) :
    HasFDerivAt (blockAffine a ρ hρ)
      ((ρ : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (E × F)) z :=
  ((hasFDerivAt_id z).sub_const a).const_smul (ρ : ℂ)⁻¹

/-- Block-affine dilation preserves the horizontal tangent subspace. -/
private theorem blockAffine_horizontal_iff (a : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    (z v : E × F) :
    (fderiv ℂ (blockAffine a ρ hρ) z v).2 = 0 ↔ v.2 = 0 := by
  rw [(blockAffine_hasFDerivAt a ρ hρ z).fderiv]
  change (ρ : ℂ)⁻¹ • v.2 = 0 ↔ v.2 = 0
  exact smul_eq_zero_iff_right (inv_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne'))

/-- Every open product neighborhood contains a block-affine image of the unit product. -/
private theorem exists_blockAffine_unit_subset (T : Set (E × F)) (hT : IsOpen T)
    (a : E × F) (ha : a ∈ T) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ),
      (blockAffine a ρ hρ).symm '' (Metric.ball 0 1 ×ˢ Metric.ball 0 1) ⊆ T := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hT a ha
  refine ⟨ρ, hρ, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  apply hball
  rw [Metric.mem_ball, blockAffine_symm_apply, dist_eq_norm, add_sub_cancel_left,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hz' : ‖z‖ < 1 := by
    change max ‖z.1‖ ‖z.2‖ < 1
    exact max_lt (by simpa using hz.1) (by simpa using hz.2)
  nlinarith

/-- The product of the open unit balls in the two complex factors. -/
private def unitProduct : Set (E × F) := Metric.ball 0 1 ×ˢ Metric.ball 0 1

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
private theorem unitProduct_isOpen : IsOpen (unitProduct (E := E) (F := F)) :=
  Metric.isOpen_ball.prod Metric.isOpen_ball

variable {X : Type*} [TopologicalSpace X]

/-- The unit product subchart obtained by block-affine restriction. -/
private noncomputable def unitSubchart (e : OpenPartialHomeomorph X (E × F))
    (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) : OpenPartialHomeomorph X (E × F) :=
  (((e.trans (blockAffine a ρ hρ).toOpenPartialHomeomorph).symm).restrOpen
    unitProduct unitProduct_isOpen).symm

@[local simp] private theorem unitSubchart_apply (e : OpenPartialHomeomorph X (E × F))
    (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) (x : X) :
    unitSubchart e a ρ hρ x = blockAffine a ρ hρ (e x) := rfl

@[local simp] private theorem unitSubchart_symm_apply (e : OpenPartialHomeomorph X (E × F))
    (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) (z : E × F) :
    (unitSubchart e a ρ hρ).symm z = e.symm ((blockAffine a ρ hρ).symm z) := rfl

/-- The unit subchart sends its base point to the origin. -/
@[local simp] private theorem unitSubchart_center (e : OpenPartialHomeomorph X (E × F))
    (x : X) (ρ : ℝ) (hρ : 0 < ρ) : unitSubchart e (e x) ρ hρ x = 0 := by
  simp

@[local simp] private theorem unitSubchart_symm_zero (e : OpenPartialHomeomorph X (E × F))
    (x : X) (hx : x ∈ e.source) (ρ : ℝ) (hρ : 0 < ρ) :
    (unitSubchart e (e x) ρ hρ).symm 0 = x := by
  simp only [unitSubchart_symm_apply, blockAffine_symm_apply, smul_zero, add_zero]
  exact e.left_inv hx

/-- Unit restriction preserves horizontal plaque equivalence, with relabelled transverse
coordinates. -/
private theorem unitSubchart_same_plaque_iff (e : OpenPartialHomeomorph X (E × F))
    (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) (x y : X) :
    (unitSubchart e a ρ hρ x).2 = (unitSubchart e a ρ hρ y).2 ↔
      (e x).2 = (e y).2 :=
  blockAffine_transverse_eq_iff a ρ hρ (e x) (e y)

 private theorem unitSubchart_source_subset (e : OpenPartialHomeomorph X (E × F))
    (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) :
    (unitSubchart e a ρ hρ).source ⊆ e.source := by
  intro x hx
  change x ∈ (e.trans (blockAffine a ρ hρ).toOpenPartialHomeomorph).source ∩ _ at hx
  exact hx.1.1

 private theorem unitSubchart_target (e : OpenPartialHomeomorph X (E × F))
    (a : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    (hsub : (blockAffine a ρ hρ).symm '' unitProduct ⊆ e.target) :
    (unitSubchart e a ρ hρ).target = unitProduct := by
  change (e.trans (blockAffine a ρ hρ).toOpenPartialHomeomorph).target ∩
    unitProduct = unitProduct
  apply inter_eq_right.mpr
  intro z hz
  change z ∈ Set.univ ∩ _
  exact ⟨mem_univ _, hsub ⟨z, hz, rfl⟩⟩

 private theorem mem_unitSubchart_source (e : OpenPartialHomeomorph X (E × F))
    (x : X) (hx : x ∈ e.source) (ρ : ℝ) (hρ : 0 < ρ) :
    x ∈ (unitSubchart e (e x) ρ hρ).source := by
  change x ∈ (e.trans (blockAffine (e x) ρ hρ).toOpenPartialHomeomorph).source ∩ _
  refine ⟨⟨hx, mem_univ _⟩, ?_⟩
  change blockAffine (e x) ρ hρ (e x) ∈ unitProduct
  simp [unitProduct]

/-- Unit restriction preserves the local transverse overlap law. -/
private theorem unitSubchart_transverse_overlap
    (e f : OpenPartialHomeomorph X (E × F))
    (ae af : E × F) (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hsub : (blockAffine ae ρ hρ).symm '' unitProduct ⊆ e.target)
    (hlaw : ∀ z, z ∈ e.target → e.symm z ∈ f.source →
      ∃ W, IsOpen W ∧ z ∈ W ∧ W ⊆ e.target ∩ e.symm ⁻¹' f.source ∧
        ∀ a ∈ W, ∀ b ∈ W, a.2 = b.2 → (f (e.symm a)).2 = (f (e.symm b)).2)
    (z : E × F) (hz : z ∈ (unitSubchart e ae ρ hρ).target)
    (hzf : (unitSubchart e ae ρ hρ).symm z ∈ (unitSubchart f af σ hσ).source) :
    ∃ W, IsOpen W ∧ z ∈ W ∧
      W ⊆ (unitSubchart e ae ρ hρ).target ∩
        (unitSubchart e ae ρ hρ).symm ⁻¹' (unitSubchart f af σ hσ).source ∧
      ∀ a ∈ W, ∀ b ∈ W, a.2 = b.2 →
        (unitSubchart f af σ hσ ((unitSubchart e ae ρ hρ).symm a)).2 =
          (unitSubchart f af σ hσ ((unitSubchart e ae ρ hρ).symm b)).2 := by
  let be := unitSubchart e ae ρ hρ
  let bf := unitSubchart f af σ hσ
  let A := blockAffine ae ρ hρ
  have hzt : A.symm z ∈ e.target := by
    apply hsub
    exact ⟨z, (unitSubchart_target e ae ρ hρ hsub) ▸ hz, rfl⟩
  obtain ⟨W, hWo, hzW, hWsub, hWeq⟩ := hlaw (A.symm z) hzt
    (unitSubchart_source_subset f af σ hσ hzf)
  refine ⟨(be.target ∩ be.symm ⁻¹' bf.source) ∩ A.symm ⁻¹' W, ?_,
    ⟨⟨hz, hzf⟩, hzW⟩, inter_subset_left, ?_⟩
  · exact (be.isOpen_inter_preimage_symm bf.open_source).inter
      (hWo.preimage A.symm.continuous)
  · intro u hu v hv huv
    have hp : (A.symm u).2 = (A.symm v).2 := by
      apply (blockAffine_transverse_eq_iff ae ρ hρ (A.symm u) (A.symm v)).mp
      change (A (A.symm u)).2 = (A (A.symm v)).2
      simpa only [Homeomorph.apply_symm_apply] using huv
    change (blockAffine af σ hσ (f (e.symm (A.symm u)))).2 =
      (blockAffine af σ hσ (f (e.symm (A.symm v)))).2
    apply (blockAffine_transverse_eq_iff af σ hσ _ _).mpr
    exact hWeq _ hu.2 _ hv.2 hp

section Manifold

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [TopologicalSpace H] {I : ModelWithCorners ℂ G H} [ChartedSpace H X]

/-- A unit subchart and its inverse are holomorphic. -/
private theorem unitSubchart_holomorphic (e : OpenPartialHomeomorph X (E × F))
    (he : ContMDiffOn I 𝓘(ℂ, E × F) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℂ, E × F) I ∞ e.symm e.target)
    (a : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    (hsub : (blockAffine a ρ hρ).symm '' unitProduct ⊆ e.target) :
    ContMDiffOn I 𝓘(ℂ, E × F) ∞ (unitSubchart e a ρ hρ)
      (unitSubchart e a ρ hρ).source ∧
    ContMDiffOn 𝓘(ℂ, E × F) I ∞ (unitSubchart e a ρ hρ).symm
      (unitSubchart e a ρ hρ).target := by
  constructor
  · exact (blockAffine_contDiff a ρ hρ).contMDiff.comp_contMDiffOn
      (he.mono (unitSubchart_source_subset e a ρ hρ))
  · change ContMDiffOn 𝓘(ℂ, E × F) I ∞
      (e.symm ∘ (blockAffine a ρ hρ).symm) _
    apply hei.comp (blockAffine_symm_contDiff a ρ hρ).contMDiff.contMDiffOn
    intro z hz
    rw [unitSubchart_target e a ρ hρ hsub] at hz
    exact hsub ⟨z, hz, rfl⟩

/-- Unit normalization preserves horizontal tangent membership under the chart derivative. -/
private theorem unitSubchart_horizontal_iff (e : OpenPartialHomeomorph X (E × F))
    (he : ContMDiffOn I 𝓘(ℂ, E × F) ∞ e e.source)
    (a : E × F) (ρ : ℝ) (hρ : 0 < ρ) (x : X)
    (hx : x ∈ (unitSubchart e a ρ hρ).source) (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℂ, E × F) (unitSubchart e a ρ hρ) x v).2 = 0 ↔
      (mfderiv I 𝓘(ℂ, E × F) e x v).2 = 0 := by
  have hex : MDifferentiableAt I 𝓘(ℂ, E × F) e x :=
    (he.mdifferentiableOn (by simp) x (unitSubchart_source_subset e a ρ hρ hx)).mdifferentiableAt
      (e.open_source.mem_nhds (unitSubchart_source_subset e a ρ hρ hx))
  change (mfderiv I 𝓘(ℂ, E × F) (blockAffine a ρ hρ ∘ e) x v).2 = 0 ↔ _
  rw [mfderiv_comp x ((blockAffine_contDiff a ρ hρ).contMDiff.mdifferentiableAt (by simp)) hex]
  rw [mfderiv_eq_fderiv]
  exact blockAffine_horizontal_iff a ρ hρ (e x) _

/-- Every point of a biholomorphic product chart admits a holomorphic unit product subchart centered
there. -/
private theorem exists_unitProduct_subchart (e : OpenPartialHomeomorph X (E × F))
    (he : ContMDiffOn I 𝓘(ℂ, E × F) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℂ, E × F) I ∞ e.symm e.target)
    (x : X) (hx : x ∈ e.source) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ),
      let b := unitSubchart e (e x) ρ hρ
      x ∈ b.source ∧ IsOpen b.source ∧ b.source ⊆ e.source ∧
      b.target = unitProduct ∧
      ContMDiffOn I 𝓘(ℂ, E × F) ∞ b b.source ∧
      ContMDiffOn 𝓘(ℂ, E × F) I ∞ b.symm b.target := by
  obtain ⟨ρ, hρ, hsub⟩ := exists_blockAffine_unit_subset e.target e.open_target
    (e x) (e.map_source hx)
  refine ⟨ρ, hρ, mem_unitSubchart_source e x hx ρ hρ, ?_⟩
  exact ⟨(unitSubchart e (e x) ρ hρ).open_source,
    unitSubchart_source_subset e (e x) ρ hρ,
    unitSubchart_target e (e x) ρ hρ hsub,
    unitSubchart_holomorphic e he hei (e x) ρ hρ hsub⟩

end Manifold

/-- A holomorphic product chart admits a subchart with target the product of complex foliation
disks. -/
private theorem exists_complexFoliationDisk_subchart {d r c : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (e : OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (he : ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ e e.source)
    (hei : ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ e.symm e.target) (x : M) (hx : x ∈ e.source) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ),
      let b := unitSubchart e (e x) ρ hρ
      x ∈ b.source ∧ IsOpen b.source ∧ b.source ⊆ e.source ∧
      b.target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)) ∧
      ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
        ∞ b b.source ∧
      ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
        ∞ b.symm b.target := by
  simp_rw +instances [complexModel, ← modelWithCornersSelf_prod,
    chartedSpaceSelf_prod] at he hei ⊢
  simpa only [unitProduct, complexFoliationDisk, TopologicalSpace.Opens.coe_mk] using
    exists_unitProduct_subchart e he hei x hx

/-- The normalized complex product chart preserves the horizontal derivative membership law. -/
private theorem unitSubchart_complex_horizontal_iff {d r c : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (e : OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (he : ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ e e.source)
    (a : ComplexModel r × ComplexModel c) (ρ : ℝ) (hρ : 0 < ρ)
    (x : M) (hx : x ∈ (unitSubchart e a ρ hρ).source)
    (v : TangentSpace (complexModel d) x) :
    (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
      (unitSubchart e a ρ hρ) x v).2 = 0 ↔
    (mfderiv (complexModel d) ((complexModel r).prod (complexModel c)) e x v).2 = 0 := by
  have hex := (he.mdifferentiableOn (by simp) x
    (unitSubchart_source_subset e a ρ hρ hx)).mdifferentiableAt
      (e.open_source.mem_nhds (unitSubchart_source_subset e a ρ hρ hx))
  have h1 := (hex.fst.hasMFDerivAt.sub
    (hasMFDerivAt_const (I := complexModel d) a.1 x)).const_smul (ρ : ℂ)⁻¹
  have h2 := (hex.snd.hasMFDerivAt.sub
    (hasMFDerivAt_const (I := complexModel d) a.2 x)).const_smul (ρ : ℂ)⁻¹
  have hb := h1.prodMk h2
  have hfun : (fun y : M ↦ ((ρ : ℂ)⁻¹ • ((e y).1 - a.1),
      (ρ : ℂ)⁻¹ • ((e y).2 - a.2))) = unitSubchart e a ρ hρ := rfl
  erw [← hfun, hb.mfderiv]
  change (ρ : ℂ)⁻¹ • ((mfderiv (complexModel d) (complexModel c)
    (Prod.snd ∘ e) x) v - 0) = 0 ↔ _
  rw [mfderiv_comp x mdifferentiableAt_snd hex, mfderiv_snd]
  change (ρ : ℂ)⁻¹ • ((mfderiv (complexModel d)
    ((complexModel r).prod (complexModel c)) e x v).2 - 0) = 0 ↔ _
  rw [sub_zero]
  exact smul_eq_zero_iff_right (inv_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne'))

/-- The rank-zero complex foliation disk is the whole singleton space. -/
private theorem complexFoliationDisk_zero :
    (complexFoliationDisk 0 : Set (ComplexModel 0)) = Set.univ := by
  ext z
  have hz : z = 0 := Subsingleton.elim _ _
  simp [complexFoliationDisk, hz]


end HolomorphicAnosov.Theorem12UnitProductBox



/-! Native immersed plaques imply Lie bracket tangency of their real tangent distribution. (HPS, §7,
pp.115–116) -/

open Set Filter Function
open scoped Topology _root_.Topology ContDiff Manifold Bundle

namespace HolomorphicAnosov.Theorem12NativePlaque

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace E L] [ChartedSpace H M]






section AmbientFields
variable [CompleteSpace H] [IsManifold (modelWithCornersSelf ℝ H) ∞ M]


end AmbientFields

/-- The real tangent distribution of native asymptotic leaves is locally involutive. -/
private theorem nativeAsymptoticLeaf_mlieBracket_tangent
    {N : Type*} [MetricSpace N] [ChartedSpace H N]
    [IsManifold (modelWithCornersSelf ℝ H) ∞ N] [CompleteSpace H]
    (f : N ≃ₜ N) (P : RealTangentDistribution (modelWithCornersSelf ℝ H) N)
    {b : N} (D : NativeAsymptoticLeafDatum (modelWithCornersSelf ℝ H) f P b)
    (z : StableAsymptoticLeaf f b)
    {V W : ∀ p : N, TangentSpace (modelWithCornersSelf ℝ H) p}
    (hV : MDifferentiableAt (modelWithCornersSelf ℝ H)
      ((modelWithCornersSelf ℝ H).prod (modelWithCornersSelf ℝ H)) (T% V) z.val)
    (hW : MDifferentiableAt (modelWithCornersSelf ℝ H)
      ((modelWithCornersSelf ℝ H).prod (modelWithCornersSelf ℝ H)) (T% W) z.val)
    (hVtan : ∀ᶠ p in 𝓝 z.val, V p ∈ P p)
    (hWtan : ∀ᶠ p in 𝓝 z.val, W p ∈ P p) :
    VectorField.mlieBracket (modelWithCornersSelf ℝ H) V W z.val ∈ P z.val := by
  let := D.topology
  let := D.charts
  let := D.smoothAtlas
  exact immersion_mlieBracket_tangent (D.inclusion_immersion z) P D.tangent_image hV hW
    ((D.inclusion_smooth.continuous.tendsto z).eventually hVtan)
    ((D.inclusion_smooth.continuous.tendsto z).eventually hWtan)


end HolomorphicAnosov.Theorem12NativePlaque


/-! Complex-to-real tangent compatibility preserves derivatives, invariant distributions, and
complementary splittings. (Zhang, Thm 1.2, pp.11–13; Demailly, I §3.C, p.23) -/

noncomputable section
open scoped ContDiff Manifold

namespace HolomorphicAnosov.Theorem12SupportW10

attribute [local instance] complex_isManifold_real

universe u v

variable {d e : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]

/-- The realification `f.toReal` has the same forward map as `f`. (Demailly, I §3.C, p.23) -/
private theorem toReal_apply (f : Biholomorph d e X Y) (x : X) : f.toReal x = f x := rfl

/-- The inverse of `f.toReal` has the same map as `f.symm`. (Demailly, I §3.C, p.23) -/
private theorem toReal_symm_apply (f : Biholomorph d e X Y) (y : Y) :
    f.toReal.symm y = f.symm y := rfl

/-- The manifold derivative commutes with tangent realification. (Demailly, I §3.C, p.23) -/
private theorem mfderiv_complex_to_real {f : X → Y} {x : X}
    (hf : MDifferentiableAt (complexModel d) (complexModel e) f x)
    (v : TangentSpace (complexModel d) x) :
    mfderiv (realModel d) (realModel e) f x (complexTangentToReal d x v) =
      complexTangentToReal e (f x) (mfderiv (complexModel d) (complexModel e) f x v) := by
  have hc := hf.differentiableWithinAt_writtenInExtChartAt
  have hd : DifferentiableAt ℂ
      (writtenInExtChartAt (complexModel d) (complexModel e) x f)
      ((extChartAt (complexModel d) x) x) := by
    simpa only [complexModel, modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ] using hc
  have hr : MDifferentiableAt (realModel d) (realModel e) f x := by
    apply (mdifferentiableAt_iff f x).mpr
    exact ⟨hf.continuousAt, (hd.restrictScalars ℝ).differentiableWithinAt⟩
  rw [hr.mfderiv, hf.mfderiv]
  simp only [realModel, complexModel, modelWithCornersSelf_coe, Set.range_id,
    fderivWithin_univ]
  change (fderiv ℝ (writtenInExtChartAt (complexModel d) (complexModel e) x f)
      ((extChartAt (complexModel d) x) x)) v =
    (fderiv ℂ (writtenInExtChartAt (complexModel d) (complexModel e) x f)
      ((extChartAt (complexModel d) x) x)) v
  exact congrArg (fun L ↦ L v) (hd.fderiv_restrictScalars (𝕜 := ℝ))

/-- A biholomorphism's complex derivative agrees with its realified derivative. (Demailly, I §3.C,
p.23; Zhang, Thm 1.2, p.11) -/
private theorem biholomorph_mfderiv_toReal (f : Biholomorph d e X Y) (x : X)
    (v : TangentSpace (complexModel d) x) :
    mfderiv (realModel d) (realModel e) f.toReal x (complexTangentToReal d x v) =
      complexTangentToReal e (f x) (mfderiv (complexModel d) (complexModel e) f x v) :=
  mfderiv_complex_to_real (f.contMDiff.mdifferentiableAt (by simp)) v

/-- The inverse biholomorphism's derivative agrees with its realified derivative over `f.symm y`.
(Demailly, I §3.C, p.23; Zhang, Thm 1.2, p.11) -/
private theorem biholomorph_mfderiv_toReal_symm (f : Biholomorph d e X Y) (y : Y)
    (v : TangentSpace (complexModel e) y) :
    mfderiv (realModel e) (realModel d) f.toReal.symm y (complexTangentToReal e y v) =
      complexTangentToReal d (f.symm y)
        (mfderiv (complexModel e) (complexModel d) f.symm y v) :=
  mfderiv_complex_to_real (f.symm.contMDiff.mdifferentiableAt (by simp)) v

/-- Membership in a complex tangent subspace is equivalent to membership of its realification.
(Demailly, I §3.C, p.23; Zhang, Thm 1.2) -/
private theorem mem_realified_submodule (x : X)
    (P : Submodule ℂ (TangentSpace (complexModel d) x))
    (v : TangentSpace (realModel d) x) :
    v ∈ (P.restrictScalars ℝ).map (complexTangentToReal d x).toLinearEquiv.toLinearMap ↔
      (complexTangentToReal d x).symm v ∈ P := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    change complexTangentToReal d x w = v at hwv
    rw [← hwv, ContinuousLinearEquiv.symm_apply_apply]
    exact hw
  · intro hv
    exact ⟨(complexTangentToReal d x).symm v, hv,
      (complexTangentToReal d x).apply_symm_apply v⟩

/-- Derivative images commute with tangent subspace realification. (Demailly, I §3.C, p.23; Zhang,
Thm 1.2) -/
private theorem realified_derivative_image {f : X → Y} {x : X}
    (hf : MDifferentiableAt (complexModel d) (complexModel e) f x)
    (P : Submodule ℂ (TangentSpace (complexModel d) x)) :
    ((P.restrictScalars ℝ).map (complexTangentToReal d x).toLinearEquiv.toLinearMap).map
        (mfderiv (realModel d) (realModel e) f x).toLinearMap =
      ((P.map (mfderiv (complexModel d) (complexModel e) f x).toLinearMap).restrictScalars
        ℝ).map (complexTangentToReal e (f x)).toLinearEquiv.toLinearMap := by
  ext w
  simp only [Submodule.mem_map, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨v, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨mfderiv (complexModel d) (complexModel e) f x z, ⟨z, hz, rfl⟩,
      (mfderiv_complex_to_real hf z).symm⟩
  · rintro ⟨v, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨complexTangentToReal d x z, ⟨z, hz, rfl⟩, mfderiv_complex_to_real hf z⟩

/-- Invariance of a realified distribution implies invariance of its complex distribution. (Zhang,
Thm 1.2, pp.3 and 11) -/
private theorem complex_invariance_of_realification (f : Biholomorph d d X X)
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (Q : RealTangentDistribution (realModel d) X)
    (hReal : ∀ x, ((P x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = Q x)
    (hInv : ∀ x, (Q x).map (mfderiv (realModel d) (realModel d) f.toReal x).toLinearMap =
      Q (f x)) (x : X) :
    (P x).map (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = P (f x) := by
  apply Submodule.restrictScalars_injective ℝ ℂ _
  apply Submodule.map_injective_of_injective (complexTangentToReal d (f x)).injective
  rw [← realified_derivative_image (f.contMDiff.mdifferentiableAt (by simp)),
    hReal x, hReal (f x)]
  exact hInv x

/-- The stable complex distribution is invariant under the biholomorphism's derivative. (Zhang, Thm
1.2, pp.3 and 11) -/
private theorem target_stable_complex_invariance [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (AD : AnosovDatum f)
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hReal : ∀ x, ((P x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        AD.splitting.stable.toDistribution x) (x : X) :
    (P x).map (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = P (f x) :=
  complex_invariance_of_realification f P AD.splitting.stable.toDistribution hReal
    AD.splitting.stable_map x

/-- The unstable complex distribution is invariant under the biholomorphism's derivative. (Zhang,
Thm 1.2, pp.3 and 11) -/
private theorem target_unstable_complex_invariance [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (AD : AnosovDatum f)
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hReal : ∀ x, ((P x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        AD.splitting.unstable.toDistribution x) (x : X) :
    (P x).map (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = P (f x) :=
  complex_invariance_of_realification f P AD.splitting.unstable.toDistribution hReal
    AD.splitting.unstable_map x

/-- The complex stable and unstable subspaces are complementary when their realifications form the
Anosov splitting. (Zhang, Thm 1.2, p.3; Demailly, I §3.C, p.23) -/
private theorem target_complex_splitting [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (AD : AnosovDatum f)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hS : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        AD.splitting.stable.toDistribution x)
    (hU : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        AD.splitting.unstable.toDistribution x) (x : X) : IsCompl (S x) (U x) := by
  apply (Submodule.isCompl_restrictScalars_iff ℝ).mp
  apply (Submodule.orderIsoMapComap (complexTangentToReal d x).toLinearEquiv).isCompl_iff.mpr
  change IsCompl (((S x).restrictScalars ℝ).map
    (complexTangentToReal d x).toLinearEquiv.toLinearMap)
    (((U x).restrictScalars ℝ).map (complexTangentToReal d x).toLinearEquiv.toLinearMap)
  rw [hS x, hU x]
  exact AD.splitting.isCompl x


end HolomorphicAnosov.Theorem12SupportW10




/-! Native real leaves induce involutivity of holomorphic coordinate frames. (Demailly, II §3.1,
pp.85–86 and V §11, p.267) -/

open Set Bundle Filter
open scoped Topology _root_.Topology ContDiff




namespace HolomorphicAnosov.Theorem12NativeComplex

open Set Filter
open scoped Topology _root_.Topology ContDiff Manifold Bundle

set_option backward.isDefEq.respectTransparency false in
/-- Differentiability of a real model field gives differentiability of its tangent-bundle section. -/
private theorem model_section_mdifferentiableAt {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {V : ∀ x : H, TangentSpace (modelWithCornersSelf ℝ H) x} {y : H}
    (hV : DifferentiableAt ℝ V y) :
    MDifferentiableAt (modelWithCornersSelf ℝ H)
      ((modelWithCornersSelf ℝ H).prod (modelWithCornersSelf ℝ H)) (T% V) y := by
  apply (mdifferentiableAt_section (E := TangentSpace (modelWithCornersSelf ℝ H))
    (modelWithCornersSelf ℝ H) V).2
  simpa only [trivializationAt_model_space_apply, mdifferentiableAt_iff_differentiableAt] using hV

set_option backward.isDefEq.respectTransparency false in
/-- Native leaf tangency implies local involutivity of the real coordinate distribution. -/
private theorem native_coordinate_real_involutive
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {X : Type*} [MetricSpace X] [ChartedSpace H X]
    [IsManifold (modelWithCornersSelf ℝ H) ∞ X]
    (f : X ≃ₜ X) (Q : RealTangentDistribution (modelWithCornersSelf ℝ H) X)
    (D : ∀ b, NativeAsymptoticLeafDatum (modelWithCornersSelf ℝ H) f Q b)
    (c : OpenPartialHomeomorph X H)
    (hc : c.MDifferentiable (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H))
    (hc2 : ContMDiffOn (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) ∞ c c.source)
    {p : X} (hp : p ∈ c.source) {V W : H → H}
    (hV : DifferentiableAt ℝ V (c p)) (hW : DifferentiableAt ℝ W (c p))
    (hVtan : ∀ᶠ y in 𝓝 (c p), V y ∈ (Q (c.symm y)).map
      (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
        c (c.symm y)).toLinearMap)
    (hWtan : ∀ᶠ y in 𝓝 (c p), W y ∈ (Q (c.symm y)).map
      (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
        c (c.symm y)).toLinearMap) :
    VectorField.lieBracket ℝ V W (c p) ∈ (Q p).map
      (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c p).toLinearMap := by
  let Vr := VectorField.mpullback (modelWithCornersSelf ℝ H)
    (modelWithCornersSelf ℝ H) c V
  let Wr := VectorField.mpullback (modelWithCornersSelf ℝ H)
    (modelWithCornersSelf ℝ H) c W
  have hcI (q : X) (hq : q ∈ c.source) :
      (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c q).IsInvertible :=
    ⟨hc.mfderiv hq, rfl⟩
  have hcp := hc2.contMDiffAt (c.open_source.mem_nhds hp)
  have hVr : MDifferentiableAt (modelWithCornersSelf ℝ H)
      ((modelWithCornersSelf ℝ H).prod (modelWithCornersSelf ℝ H)) (T% Vr) p :=
    (model_section_mdifferentiableAt hV).mpullback_vectorField hcp (hcI p hp) (by simp)
  have hWr : MDifferentiableAt (modelWithCornersSelf ℝ H)
      ((modelWithCornersSelf ℝ H).prod (modelWithCornersSelf ℝ H)) (T% Wr) p :=
    (model_section_mdifferentiableAt hW).mpullback_vectorField hcp (hcI p hp) (by simp)
  have hVrTan : ∀ᶠ q in 𝓝 p, Vr q ∈ Q q := by
    filter_upwards [(hc.mdifferentiableAt hp).continuousAt.tendsto.eventually hVtan,
      c.open_source.mem_nhds hp] with q hq hqs
    rw [c.left_inv hqs] at hq
    rcases hq with ⟨a, ha, he⟩
    change (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c q).inverse
      (V (c q)) ∈ Q q
    rw [← he]
    change (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c q).inverse
      ((mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c q) a) ∈ Q q
    rw [(hcI q hqs).inverse_apply_self]
    exact ha
  have hWrTan : ∀ᶠ q in 𝓝 p, Wr q ∈ Q q := by
    filter_upwards [(hc.mdifferentiableAt hp).continuousAt.tendsto.eventually hWtan,
      c.open_source.mem_nhds hp] with q hq hqs
    rw [c.left_inv hqs] at hq
    rcases hq with ⟨a, ha, he⟩
    change (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c q).inverse
      (W (c q)) ∈ Q q
    rw [← he]
    change (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c q).inverse
      ((mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c q) a) ∈ Q q
    rw [(hcI q hqs).inverse_apply_self]
    exact ha
  have hself : ForwardAsymptotic f p p := by
    simp [ForwardAsymptotic]
  have ht := Theorem12NativePlaque.nativeAsymptoticLeaf_mlieBracket_tangent f Q (D p)
    (⟨p, hself⟩ : StableAsymptoticLeaf f p) hVr hWr hVrTan hWrTan
  let : IsManifold (modelWithCornersSelf ℝ H) (minSmoothness ℝ 2) X :=
    IsManifold.of_le (n := ∞) (by simp)
  have hb := VectorField.mpullback_mlieBracket (model_section_mdifferentiableAt hV)
    (model_section_mdifferentiableAt hW) hcp (by simp)
  have hmodel : VectorField.mlieBracket (modelWithCornersSelf ℝ H) V W (c p) =
      VectorField.lieBracket ℝ V W (c p) := by
    rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin_univ]
  change (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c p).inverse
    (VectorField.mlieBracket (modelWithCornersSelf ℝ H) V W (c p)) =
    VectorField.mlieBracket (modelWithCornersSelf ℝ H) Vr Wr p at hb
  rw [hmodel] at hb
  refine ⟨VectorField.mlieBracket (modelWithCornersSelf ℝ H) Vr Wr p, ht, ?_⟩
  change (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c p)
    (VectorField.mlieBracket (modelWithCornersSelf ℝ H) Vr Wr p) = _
  rw [← hb]
  exact (hcI p hp).self_apply_inverse _

section ComplexBinding

attribute [local instance] complex_isManifold_real

variable {d : ℕ} {X : Type*} [MetricSpace X]
  [ChartedSpace (ComplexModel d) X]

/-- A complex smooth chart expression is smooth after restriction to real scalars. -/
private theorem contMDiffOn_real_of_complex {S : Set X} {φ : X → ComplexModel d}
    (hφ : ContMDiffOn (complexModel d) (complexModel d) ∞ φ S) :
    ContMDiffOn (realModel d) (realModel d) ∞ φ S := by
  intro p hp
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hφ p hp)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

/-- A chart maps the realified distribution to the underlying real submodule of its complex
derivative image. -/
private theorem chart_realified_image
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (Q : RealTangentDistribution (realModel d) X)
    (hReal : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    {φ : X → ComplexModel d} {p : X}
    (hφ : MDifferentiableAt (complexModel d) (complexModel d) φ p) :
    (Q p).map (mfderiv (realModel d) (realModel d) φ p).toLinearMap =
      ((P p).map (mfderiv (complexModel d) (complexModel d) φ p).toLinearMap).restrictScalars
        ℝ := by
  rw [← hReal p]
  have hd (a : TangentSpace (complexModel d) p) :
      mfderiv (realModel d) (realModel d) φ p (complexTangentToReal d p a) =
      mfderiv (complexModel d) (complexModel d) φ p a :=
    Theorem12SupportW10.mfderiv_complex_to_real hφ a
  ext w
  simp only [Submodule.mem_map, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨v, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (hd a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨complexTangentToReal d p a, ⟨a, ha, rfl⟩, hd a⟩

/-- The real and complex Lie brackets of complex-differentiable coordinate fields agree. -/
private theorem real_lieBracket_eq_complex {V W : ComplexModel d → ComplexModel d} {z : ComplexModel d}
    (hV : DifferentiableAt ℂ V z) (hW : DifferentiableAt ℂ W z) :
    VectorField.lieBracket ℝ V W z = VectorField.lieBracket ℂ V W z := by
  simp only [VectorField.lieBracket, hV.fderiv_restrictScalars ℝ,
    hW.fderiv_restrictScalars ℝ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Native real leaves and tangent realification imply involutivity of the complex coordinate
distribution. -/
private theorem native_coordinate_complex_involutive [IsManifold (complexModel d) ∞ X]
    (f : X ≃ₜ X)
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (Q : RealTangentDistribution (realModel d) X)
    (hReal : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (D : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (x : X) {z : ComplexModel d} (hz : z ∈ (chartAt (ComplexModel d) x).target)
    {V W : ComplexModel d → ComplexModel d}
    (hV : DifferentiableAt ℂ V z) (hW : DifferentiableAt ℂ W z)
    (hVtan : ∀ᶠ y in 𝓝 z, V y ∈
      (P ((chartAt (ComplexModel d) x).symm y)).map
        (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
          ((chartAt (ComplexModel d) x).symm y)).toLinearMap)
    (hWtan : ∀ᶠ y in 𝓝 z, W y ∈
      (P ((chartAt (ComplexModel d) x).symm y)).map
        (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
          ((chartAt (ComplexModel d) x).symm y)).toLinearMap) :
    VectorField.lieBracket ℂ V W z ∈
      (P ((chartAt (ComplexModel d) x).symm z)).map
        (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
          ((chartAt (ComplexModel d) x).symm z)).toLinearMap := by
  let c := chartAt (ComplexModel d) x
  have hcz : c (c.symm z) = z := c.right_inv hz
  have hpc := c.map_target hz
  have hcr : ContMDiffOn (realModel d) (realModel d) ∞ c c.source :=
    contMDiffOn_real_of_complex (contMDiffOn_chart (n := ∞) (I := complexModel d))
  have hcir : ContMDiffOn (realModel d) (realModel d) ∞ c.symm c.target := by
    intro y hy
    obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp
      ((contMDiffOn_chart_symm (n := ∞) (I := complexModel d) (x := x)) y hy)
    exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
  have hc : c.MDifferentiable (realModel d) (realModel d) :=
    ⟨hcr.mdifferentiableOn (by simp), hcir.mdifferentiableOn (by simp)⟩
  have himage (q : X) (hq : q ∈ c.source) :
      (Q q).map (mfderiv (realModel d) (realModel d) c q).toLinearMap =
      ((P q).map (mfderiv (complexModel d) (complexModel d) c q).toLinearMap).restrictScalars
        ℝ := by
    apply chart_realified_image P Q hReal
    exact ((contMDiffOn_chart (n := ∞) (I := complexModel d)) q hq).contMDiffAt
      (c.open_source.mem_nhds hq) |>.mdifferentiableAt (by simp)
  have hVr : DifferentiableAt ℝ V (c (c.symm z)) := by
    rw [hcz]
    exact hV.restrictScalars ℝ
  have hWr : DifferentiableAt ℝ W (c (c.symm z)) := by
    rw [hcz]
    exact hW.restrictScalars ℝ
  have hVrtan : ∀ᶠ y in 𝓝 (c (c.symm z)), V y ∈ (Q (c.symm y)).map
      (mfderiv (realModel d) (realModel d) c (c.symm y)).toLinearMap := by
    rw [hcz]
    filter_upwards [hVtan, c.open_target.mem_nhds hz] with y hy hyt
    rw [himage (c.symm y) (c.map_target hyt)]
    exact hy
  have hWrtan : ∀ᶠ y in 𝓝 (c (c.symm z)), W y ∈ (Q (c.symm y)).map
      (mfderiv (realModel d) (realModel d) c (c.symm y)).toLinearMap := by
    rw [hcz]
    filter_upwards [hWtan, c.open_target.mem_nhds hz] with y hy hyt
    rw [himage (c.symm y) (c.map_target hyt)]
    exact hy
  have ht := native_coordinate_real_involutive f Q D c hc hcr hpc hVr hWr hVrtan hWrtan
  rw [hcz, himage (c.symm z) hpc, real_lieBracket_eq_complex hV hW] at ht
  exact ht

/-- A holomorphic subbundle with native real leaves admits a local holomorphic frame spanning an
involutive coordinate distribution. -/
private theorem exists_native_holomorphic_involutive_frame [IsManifold (complexModel d) ∞ X]
    {r : ℕ} (f : X ≃ₜ X)
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P)
    (Q : RealTangentDistribution (realModel d) X)
    (hReal : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (D : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b) (x : X) :
    ∃ (Ω : Set (ComplexModel d)) (Y : Fin r → ComplexModel d → ComplexModel d),
      IsOpen Ω ∧ chartAt (ComplexModel d) x x ∈ Ω ∧
      Ω ⊆ (chartAt (ComplexModel d) x).target ∧
      (∀ i, ContDiffOn ℂ ∞ (Y i) Ω) ∧
      (∀ z ∈ Ω, LinearIndependent ℂ (fun i ↦ Y i z)) ∧
      (∀ z ∈ Ω, Submodule.span ℂ (Set.range (fun i ↦ Y i z)) =
        (P ((chartAt (ComplexModel d) x).symm z)).map
          (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
            ((chartAt (ComplexModel d) x).symm z)).toLinearMap) ∧
      (∀ z ∈ Ω, ∀ A B : ComplexModel d → ComplexModel d,
        DifferentiableAt ℂ A z → DifferentiableAt ℂ B z →
        (∀ᶠ y in 𝓝 z, A y ∈ Submodule.span ℂ (Set.range (fun i ↦ Y i y))) →
        (∀ᶠ y in 𝓝 z, B y ∈ Submodule.span ℂ (Set.range (fun i ↦ Y i y))) →
        VectorField.lieBracket ℂ A B z ∈ Submodule.span ℂ (Set.range (fun i ↦ Y i z))) := by
  obtain ⟨U, s, Y, hU, hxU, hUs, hs, hspan, hΩ, hxΩ, hY, hLI, hcoord, himage⟩ :=
    Theorem12NativeHolomorphicFrame.exists_native_holomorphic_coordinate_frame P hP x
  let Ω := (chartAt (ComplexModel d) x).target ∩
    (chartAt (ComplexModel d) x).symm ⁻¹' U
  have himage' : ∀ z ∈ Ω, Submodule.span ℂ (Set.range (fun i ↦ Y i z)) =
      (P ((chartAt (ComplexModel d) x).symm z)).map
        (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
          ((chartAt (ComplexModel d) x).symm z)).toLinearMap := by
    exact himage
  refine ⟨Ω, Y, hΩ, hxΩ, inter_subset_left, hY, hLI, himage', ?_⟩
  intro z hz A B hA hB hAtan hBtan
  rw [himage' z hz]
  apply native_coordinate_complex_involutive f P Q hReal D x hz.1 hA hB
  · filter_upwards [hAtan, hΩ.mem_nhds hz] with y hy hyΩ
    rwa [himage' y hyΩ] at hy
  · filter_upwards [hBtan, hΩ.mem_nhds hz] with y hy hyΩ
    rwa [himage' y hyΩ] at hy



end ComplexBinding


end HolomorphicAnosov.Theorem12NativeComplex


/-! Smooth fields on open domains admit local real flows on those domains. -/

open Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace LocalFlowExistenceBinding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the inclusion of an open domain is the identity in its inherited coordinates. -/
private theorem hasMFDerivAt_open_inclusion (Ω : Opens E) (x : Ω) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : Ω → E) x
      (ContinuousLinearMap.id ℝ E) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [mfld_simps]
  have heq : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) x (Subtype.val : Ω → E)
      =ᶠ[nhds (x : E)] id := by
    simpa only [writtenInExtChartAt, chartAt_self_eq, mfld_simps] using
      (Opens.chartAt_subtype_val_symm_eventuallyEq (H := E) Ω (x := x)).symm
  exact ((hasFDerivAt_id (x : E)).congr_of_eventuallyEq heq).hasFDerivWithinAt

/-- A smooth field on an open domain defines a smooth tangent section on that domain. -/
private theorem smooth_open_field (Ω : Opens E) (X : E → E)
    (hX : ContDiffOn ℝ ∞ X Ω) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x : Ω ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) Ω)) := by
  intro x
  apply Bundle.contMDiffAt_section x |>.mpr
  have h := (hX x x.property).contDiffAt (Ω.isOpen.mem_nhds x.property)
  have hc := (contMDiffAt_subtype_iff (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (U := Ω)).mpr h.contMDiffAt
  convert hc using 1
  funext y
  rw [TangentBundle.trivializationAt_apply]
  have he : chartAt E x = chartAt E y := by
    simp only [Opens.chartAt_eq, chartAt_self_eq]
  have hex : extChartAt 𝓘(ℝ, E) x = extChartAt 𝓘(ℝ, E) y :=
    congrArg (fun e : OpenPartialHomeomorph Ω E ↦ e.extend 𝓘(ℝ, E)) he
  change (fderivWithin ℝ (extChartAt 𝓘(ℝ, E) x ∘ (extChartAt 𝓘(ℝ, E) y).symm)
    (range 𝓘(ℝ, E)) (extChartAt 𝓘(ℝ, E) y y)) (X y) = X y
  rw [hex, fderivWithin_extChartAt_comp_extChartAt_symm_range]
  rfl

/-- A smooth field on an open subtype admits a local real flow satisfying its ambient differential
equation. -/
private theorem exists_subtype_local_real_flow [FiniteDimensional ℝ E]
    (Ω : Opens E) (X : E → E) (hX : ContDiffOn ℝ ∞ X Ω) (x : Ω) :
    ∃ (V : Set Ω) (δ : ℝ) (Ψ : Ω × ℝ → Ω),
      IsOpen V ∧ x ∈ V ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ Ψ (V ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ V, Ψ (y, 0) = y) ∧
      (∀ y ∈ V, ∀ t ∈ Ioo (-δ) δ,
        HasDerivAt (fun s ↦ (Ψ (y, s) : E)) (X (Ψ (y, t))) t) ∧
      (∀ y ∈ V, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
        s + t ∈ Ioo (-δ) δ → Ψ (y, s) ∈ V →
        Ψ (Ψ (y, s), t) = Ψ (y, s + t)) := by
  obtain ⟨V, δ, Ψ, hV, hxV, hδ, hΨ, hinit, hODE, _, hgroup, _⟩ :=
    HolomorphicAnosov.exists_smoothLocalFlow 𝓘(ℝ, E)
      (fun y : Ω ↦ X y) (smooth_open_field Ω X hX) x
  refine ⟨V, δ, Ψ, hV, hxV, hδ, hΨ, hinit, ?_, hgroup⟩
  intro y hy t ht
  have hd := (hasMFDerivAt_open_inclusion Ω (Ψ (y, t))).comp_hasMFDerivWithinAt t
    (hODE y hy t ht)
  have hf := (hd.hasMFDerivAt (isOpen_Ioo.mem_nhds ht)).hasFDerivAt
  have hf' : HasFDerivAt (fun s ↦ (Ψ (y, s) : E))
      ((ContinuousLinearMap.id ℝ E).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (Ψ (y, t))))) t := hf
  simpa using hf'.hasDerivAt

/-- Product charts of an open subtype equal the ambient coordinate inclusion. -/
private theorem open_prod_chart_apply (Ω : Opens E) (p q : Ω × ℝ) :
    extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) p q = ((q.1 : E), q.2) := by
  rfl

/-- The product chart source of an open subtype is the whole subtype. -/
private theorem open_prod_chart_source (Ω : Opens E) (p : Ω × ℝ) :
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) p).source = univ := by
  simp [prodChartedSpace_chartAt, Opens.chartAt_eq, chartAt_self_eq]

/-- Product charts of an open subtype coincide as partial equivalences. -/
private theorem open_prod_chart_eq (Ω : Opens E) (p q : Ω × ℝ) :
    extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) p =
      extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) q := by
  simp only [extChartAt, prodChartedSpace_chartAt, Opens.chartAt_eq, chartAt_self_eq]

/-- The ambient coordinate expression of a native real flow is real smooth on its chart image. -/
private theorem ambient_flow_contDiffOn
    (Ω : Opens E) (x : Ω) (V : Set Ω) (hV : IsOpen V) (δ : ℝ)
    (Ψ : Ω × ℝ → Ω)
    (hΨ : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ Ψ
      (V ×ˢ Ioo (-δ) δ)) :
    ContDiffOn ℝ ∞
      (fun p : E × ℝ ↦ (Ψ ((extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (x, 0)).symm p) : E))
      ((Subtype.val '' V) ×ˢ Ioo (-δ) δ) := by
  rintro ⟨y, t⟩ ⟨⟨u, hu, rfl⟩, ht⟩
  have hψat := (hΨ (u, t) ⟨hu, ht⟩).contMDiffAt
    ((hV.prod isOpen_Ioo).mem_nhds ⟨hu, ht⟩)
  have hreg := (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := Ω)).contMDiffAt.comp
    (u, t) hψat
  have hr := (contMDiffAt_iff.mp hreg).2
  rw [open_prod_chart_eq Ω (u, t) (x, 0)] at hr
  have hr' : ContDiffAt ℝ ∞
      (fun p : E × ℝ ↦ (Ψ ((extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (x, 0)).symm p) : E))
      ((u : E), t) := by
    simpa only [Opens.chartAt_eq, chartAt_self_eq, mfld_simps, Function.comp_def,
      ← modelWithCornersSelf_prod, contDiffWithinAt_univ, Set.domRestrict_apply, id_eq] using hr
  exact hr'.contDiffWithinAt

/-- A smooth field on an open domain admits a local real flow on an open coordinate rectangle inside
that domain. -/
private theorem exists_ambient_local_real_flow [FiniteDimensional ℝ E]
    (Ω : Opens E) (X : E → E) (hX : ContDiffOn ℝ ∞ X Ω) (x : E) (hx : x ∈ Ω) :
    ∃ (A : Set E) (δ : ℝ) (Φ : E × ℝ → E),
      IsOpen A ∧ x ∈ A ∧ A ⊆ Ω ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (A ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ A, Φ (y, 0) = y) ∧
      (∀ p ∈ A ×ˢ Ioo (-δ) δ, Φ p ∈ Ω) ∧
      (∀ p ∈ A ×ˢ Ioo (-δ) δ,
        HasDerivAt (fun s ↦ Φ (p.1, s)) (X (Φ p)) p.2) ∧
      (∀ y ∈ A, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
        s + t ∈ Ioo (-δ) δ → Φ (y, s) ∈ A →
        Φ (Φ (y, s), t) = Φ (y, s + t)) := by
  let xΩ : Ω := ⟨x, hx⟩
  obtain ⟨V, δ, Ψ, hV, hxV, hδ, hΨ, hinit, hODE, hgroup⟩ :=
    exists_subtype_local_real_flow Ω X hX xΩ
  let c := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (xΩ, (0 : ℝ))
  let Φ : E × ℝ → E := fun p ↦ Ψ (c.symm p)
  have hcoord (u : Ω) (t : ℝ) : Φ ((u : E), t) = (Ψ (u, t) : E) := by
    have hsrc : (u, t) ∈ c.source := by rw [open_prod_chart_source]; trivial
    have hc : c.symm ((u : E), t) = (u, t) := by
      exact c.left_inv hsrc
    simp only [Φ, hc]
  have hA : IsOpen (Subtype.val '' V : Set E) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isOpenMap V hV
  refine ⟨Subtype.val '' V, δ, Φ, hA, ⟨xΩ, hxV, rfl⟩,
    (by rintro y ⟨u, _, rfl⟩; exact u.property), hδ,
    ambient_flow_contDiffOn Ω xΩ V hV δ Ψ hΨ, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨u, hu, rfl⟩
    rw [hcoord, hinit u hu]
  · rintro ⟨y, t⟩ ⟨⟨u, hu, rfl⟩, ht⟩
    rw [hcoord]
    exact (Ψ (u, t)).property
  · rintro ⟨y, t⟩ ⟨⟨u, hu, rfl⟩, ht⟩
    rw [funext (hcoord u), hcoord u t]
    exact hODE u hu t ht
  · rintro y ⟨u, hu, rfl⟩ s hs t ht hst hreceiving
    rw [hcoord u s] at hreceiving
    obtain ⟨v, hv, hval⟩ := hreceiving
    have hvEq : v = Ψ (u, s) := Subtype.val_injective hval
    have hrecv : Ψ (u, s) ∈ V := hvEq ▸ hv
    rw [hcoord u s, hcoord (Ψ (u, s)) t, hcoord u (s + t),
      hgroup u hu s hs t ht hst hrecv]


section ComplexField

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- A complex smooth field on an open domain admits a local real smooth flow. -/
private theorem exists_ambient_real_flow_of_complex_smooth
    (Ω : Opens F) (X : F → F) (hX : ContDiffOn ℂ ∞ X Ω) (x : F) (hx : x ∈ Ω) :
    ∃ (A : Set F) (δ : ℝ) (Φ : F × ℝ → F),
      IsOpen A ∧ x ∈ A ∧ A ⊆ Ω ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (A ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ A, Φ (y, 0) = y) ∧
      (∀ p ∈ A ×ˢ Ioo (-δ) δ, Φ p ∈ Ω) ∧
      (∀ p ∈ A ×ˢ Ioo (-δ) δ,
        HasDerivAt (fun s ↦ Φ (p.1, s)) (X (Φ p)) p.2) ∧
      (∀ y ∈ A, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
        s + t ∈ Ioo (-δ) δ → Φ (y, s) ∈ A →
        Φ (Φ (y, s), t) = Φ (y, s + t)) := by
  exact exists_ambient_local_real_flow Ω X (hX.restrict_scalars ℝ) x hx


end ComplexField

end LocalFlowExistenceBinding

namespace HolomorphicAnosov.Theorem12FrobeniusLocalAssembly

open Set Filter
open scoped Topology _root_.Topology ContDiff Manifold
open Theorem12NormalizedFrame

attribute [local instance] complex_isManifold_real

variable {d r : ℕ} {X : Type*} [MetricSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Native leaves and a holomorphic tangent subbundle yield local commuting normalized coordinate
fields. -/
theorem exists_native_commuting_frame
    (f : X ≃ₜ X)
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P)
    (Q : RealTangentDistribution (realModel d) X)
    (hReal : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (D : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b) (x : X) :
    ∃ (V : Set (ComplexModel d)) (p : ComplexModel d →L[ℂ] (Fin r → ℂ))
      (N : ComplexModel d → (Fin r → ℂ) →L[ℂ] ComplexModel d),
      IsOpen V ∧ chartAt (ComplexModel d) x x ∈ V ∧
      V ⊆ (chartAt (ComplexModel d) x).target ∧ ContDiffOn ℂ ∞ N V ∧
      (∀ z ∈ V, LinearMap.range (N z).toLinearMap =
        (P ((chartAt (ComplexModel d) x).symm z)).map
          (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
            ((chartAt (ComplexModel d) x).symm z)).toLinearMap) ∧
      (∀ z ∈ V, ∀ v, p (N z v) = v) ∧
      (∀ z ∈ V, Function.Injective (N z)) ∧
      (∀ z ∈ V, ∀ v w, VectorField.lieBracket ℂ
        (fun y ↦ N y v) (fun y ↦ N y w) z = 0) := by
  obtain ⟨Ω, Y, hΩ, hxΩ, hΩtarget, hY, hLI, himage, hinvol⟩ :=
    Theorem12NativeComplex.exists_native_holomorphic_involutive_frame f P hP Q hReal D x
  obtain ⟨p, V, hV, hxV, hVΩ, hN, hrange, hproj, hcommute⟩ :=
    exists_commuting_normalized_frame Y hΩ hxΩ hY (hLI _ hxΩ) hinvol
  refine ⟨V, p, normalizedOperator p (frameOperator (𝕜 := ℂ) Y),
    hV, hxV, hVΩ.trans hΩtarget, hN, ?_, hproj, ?_, hcommute⟩
  · intro z hz
    exact (hrange z hz).trans (himage z (hVΩ hz))
  · intro z hz v w hvw
    have hpvw := congrArg p hvw
    simpa only [hproj z hz] using hpvw

/-- Complementary holomorphic bundles with native leaves admit commuting frames on a common
coordinate neighborhood. -/
private theorem exists_native_complementary_commuting_frames {c : ℕ}
    (f : X ≃ₜ X)
    (P R : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P) (hR : IsHolomorphicTangentSubbundle c R)
    (hcompl : ∀ q, IsCompl (P q) (R q))
    (Q T : RealTangentDistribution (realModel d) X)
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (hRealR : ∀ q, ((R q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = T q)
    (DP : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (DR : ∀ b, NativeAsymptoticLeafDatum (realModel d) f.symm T b) (x : X) :
    ∃ (V : Set (ComplexModel d))
      (S : ComplexModel d → (Fin r → ℂ) →L[ℂ] ComplexModel d)
      (U : ComplexModel d → (Fin c → ℂ) →L[ℂ] ComplexModel d),
      IsOpen V ∧ chartAt (ComplexModel d) x x ∈ V ∧
      V ⊆ (chartAt (ComplexModel d) x).target ∧
      ContDiffOn ℂ ∞ S V ∧ ContDiffOn ℂ ∞ U V ∧
      (∀ z ∈ V, Function.Injective (S z)) ∧
      (∀ z ∈ V, Function.Injective (U z)) ∧
      (∀ z ∈ V, LinearMap.range (S z).toLinearMap =
        (P ((chartAt (ComplexModel d) x).symm z)).map
          (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
            ((chartAt (ComplexModel d) x).symm z)).toLinearMap) ∧
      (∀ z ∈ V, LinearMap.range (U z).toLinearMap =
        (R ((chartAt (ComplexModel d) x).symm z)).map
          (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
            ((chartAt (ComplexModel d) x).symm z)).toLinearMap) ∧
      (∀ z ∈ V, IsCompl (LinearMap.range (S z).toLinearMap)
        (LinearMap.range (U z).toLinearMap)) ∧
      (∀ z ∈ V, ∀ v w, VectorField.lieBracket ℂ
        (fun y ↦ S y v) (fun y ↦ S y w) z = 0) ∧
      (∀ z ∈ V, ∀ v w, VectorField.lieBracket ℂ
        (fun y ↦ U y v) (fun y ↦ U y w) z = 0) := by
  obtain ⟨VS, _, S, hVS, hxS, hVSt, hS, hSr, _, hSi, hSc⟩ :=
    exists_native_commuting_frame f P hP Q hRealP DP x
  obtain ⟨VU, _, U, hVU, hxU, hVUt, hU, hUr, _, hUi, hUc⟩ :=
    exists_native_commuting_frame f.symm R hR T hRealR DR x
  refine ⟨VS ∩ VU, S, U, hVS.inter hVU, ⟨hxS, hxU⟩,
    inter_subset_left.trans hVSt, hS.mono inter_subset_left,
    hU.mono inter_subset_right, (fun z hz ↦ hSi z hz.1),
    (fun z hz ↦ hUi z hz.2), (fun z hz ↦ hSr z hz.1),
    (fun z hz ↦ hUr z hz.2), ?_, (fun z hz ↦ hSc z hz.1),
    (fun z hz ↦ hUc z hz.2)⟩
  intro z hz
  rw [hSr z hz.1, hUr z hz.2]
  let k := chartAt (ComplexModel d) x
  have hc : k.MDifferentiable (complexModel d) (complexModel d) :=
    ⟨(contMDiffOn_chart (n := ∞) (I := complexModel d)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (n := ∞) (I := complexModel d) (x := x)).mdifferentiableOn
        (by simp)⟩
  have hd : (mfderiv (complexModel d) (complexModel d) k (k.symm z)).IsInvertible :=
    ⟨hc.mfderiv (k.map_target (hVSt hz.1)), rfl⟩
  exact Submodule.isCompl_map
    (LinearEquiv.ofBijective
      (mfderiv (complexModel d) (complexModel d) k (k.symm z)).toLinearMap hd.bijective)
    (hcompl (k.symm z))

/-- Normalized directions and their imaginary multiples are real smooth and have vanishing real
brackets. -/
private theorem normalized_directions_real_smooth_commuting
    (N : ComplexModel d → (Fin r → ℂ) →L[ℂ] ComplexModel d)
    {V : Set (ComplexModel d)} (hV : IsOpen V) (hN : ContDiffOn ℂ ∞ N V)
    (hcommute : ∀ z ∈ V, ∀ v w, VectorField.lieBracket ℂ
      (fun y ↦ N y v) (fun y ↦ N y w) z = 0) (v w : Fin r → ℂ) :
    ContDiffOn ℝ ∞ (fun y ↦ N y v) V ∧
    ContDiffOn ℝ ∞ (fun y ↦ N y w) V ∧
    ∀ z ∈ V, VectorField.lieBracket ℝ
      (fun y ↦ N y v) (fun y ↦ N y w) z = 0 := by
  have hv : ContDiffOn ℂ ∞ (fun y ↦ N y v) V := hN.clm_apply contDiffOn_const
  have hw : ContDiffOn ℂ ∞ (fun y ↦ N y w) V := hN.clm_apply contDiffOn_const
  refine ⟨hv.restrict_scalars ℝ, hw.restrict_scalars ℝ, ?_⟩
  intro z hz
  rw [Theorem12NormalizedFrame.real_lieBracket_eq_complex
    ((hv.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp))
    ((hw.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp))]
  exact hcommute z hz v w

open Theorem12UnitProductBox

omit [IsManifold (complexModel d) ∞ X] in
/-- Uniform block dilation preserves the derivative image of every tangent submodule. -/
private theorem unitSubchart_tangent_image_eq {c : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel r × ComplexModel c))
    (he : ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c)
      ∞ e e.source)
    (a : ComplexModel r × ComplexModel c) (ρ : ℝ) (hρ : 0 < ρ)
    (x : X) (hx : x ∈ (unitSubchart e a ρ hρ).source)
    (P : Submodule ℂ (TangentSpace (complexModel d) x)) :
    P.map (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c)
      (unitSubchart e a ρ hρ) x).toLinearMap =
    P.map (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) e x).toLinearMap := by
  have hex := (he.mdifferentiableOn (by simp) x
    (unitSubchart_source_subset e a ρ hρ hx)).mdifferentiableAt
      (e.open_source.mem_nhds (unitSubchart_source_subset e a ρ hρ hx))
  have hd : mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c)
      (unitSubchart e a ρ hρ) x =
      (ρ : ℂ)⁻¹ • mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) e x := by
    change mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c)
      (blockAffine a ρ hρ ∘ e) x = _
    rw [mfderiv_comp x
      ((blockAffine_contDiff a ρ hρ).contMDiff.mdifferentiableAt (by simp)) hex,
      mfderiv_eq_fderiv, (blockAffine_hasFDerivAt a ρ hρ (e x)).fderiv]
    ext v
    rfl
  rw [hd]
  exact Submodule.map_smul _ P _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne'))

omit [IsManifold (complexModel d) ∞ X] in
/-- A coordinate chart straightening a native tangent distribution yields a holomorphic unit box on
the manifold. -/
private theorem exists_unit_box_of_coordinate_straightening {c : ℕ}
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (k : OpenPartialHomeomorph X (ComplexModel d))
    (hk : ContMDiffOn (complexModel d) (complexModel d) ∞ k k.source)
    (hki : ContMDiffOn (complexModel d) (complexModel d) ∞ k.symm k.target)
    (a : OpenPartialHomeomorph (ComplexModel d) (ComplexModel r × ComplexModel c))
    (ha : ContDiffOn ℂ ∞ a a.source) (hai : ContDiffOn ℂ ∞ a.symm a.target)
    (hflat : ∀ q ∈ k.source, k q ∈ a.source →
      ((P q).map (mfderiv (complexModel d) (complexModel d) k q).toLinearMap).map
        (fderiv ℂ a (k q)).toLinearMap =
      LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap)
    (x : X) (hx : x ∈ k.source) (hxa : k x ∈ a.source) :
    ∃ b : OpenPartialHomeomorph X (ComplexModel r × ComplexModel c),
      x ∈ b.source ∧ b.source ⊆ k.source ∧
      b.target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)) ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) ∞ b b.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel c) (complexModel d) ∞ b.symm b.target ∧
      (∀ q ∈ b.source,
        (P q).map (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) b q).toLinearMap =
          LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap) := by
  let e := k.trans a
  have he : ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c)
      ∞ e e.source := by
    apply ha.contMDiffOn.comp (hk.mono inter_subset_left)
    exact inter_subset_right
  have hei : ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel c) (complexModel d)
      ∞ e.symm e.target := by
    apply hki.comp (hai.contMDiffOn.mono inter_subset_left)
    exact inter_subset_right
  have hxe : x ∈ e.source := ⟨hx, hxa⟩
  obtain ⟨ρ, hρ, hxb, _, hbsub, hbtarget, hb, hbi⟩ :=
    exists_unitProduct_subchart e he hei x hxe
  refine ⟨unitSubchart e (e x) ρ hρ, hxb, hbsub.trans inter_subset_left,
    hbtarget, hb, hbi, ?_⟩
  intro q hq
  rw [unitSubchart_tangent_image_eq e he (e x) ρ hρ q hq]
  have hqe := hbsub hq
  have hkd := (hk.mdifferentiableOn (by simp) q hqe.1).mdifferentiableAt
    (k.open_source.mem_nhds hqe.1)
  have had : DifferentiableAt ℂ a (k q) :=
    (ha.contDiffAt (a.open_source.mem_nhds hqe.2)).differentiableAt (by simp)
  change (P q).map
    (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) (a ∘ k) q).toLinearMap = _
  erw [mfderiv_comp q had.mdifferentiableAt hkd, mfderiv_eq_fderiv]
  change (P q).map ((fderiv ℂ a (k q)).toLinearMap.comp
    (mfderiv (complexModel d) (complexModel d) k q).toLinearMap) = _
  erw [Submodule.map_comp]
  exact hflat q hqe.1 hqe.2

/-- The commuting frame supplied by native leaves admits local real flows. -/
private theorem exists_native_commuting_frame_real_flows
    (f : X ≃ₜ X)
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P)
    (Q : RealTangentDistribution (realModel d) X)
    (hReal : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (D : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b) (x : X) :
    ∃ (V : Set (ComplexModel d))
      (N : ComplexModel d → (Fin r → ℂ) →L[ℂ] ComplexModel d),
      IsOpen V ∧ chartAt (ComplexModel d) x x ∈ V ∧
      V ⊆ (chartAt (ComplexModel d) x).target ∧ ContDiffOn ℂ ∞ N V ∧
      (∀ z ∈ V, LinearMap.range (N z).toLinearMap =
        (P ((chartAt (ComplexModel d) x).symm z)).map
          (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) x)
            ((chartAt (ComplexModel d) x).symm z)).toLinearMap) ∧
      (∀ z ∈ V, Function.Injective (N z)) ∧
      (∀ z ∈ V, ∀ v w, VectorField.lieBracket ℂ
        (fun y ↦ N y v) (fun y ↦ N y w) z = 0) ∧
      (∀ v : Fin r → ℂ,
        ∃ (A : Set (ComplexModel d)) (δ : ℝ)
          (Φ : ComplexModel d × ℝ → ComplexModel d),
          IsOpen A ∧ chartAt (ComplexModel d) x x ∈ A ∧ A ⊆ V ∧ 0 < δ ∧
          ContDiffOn ℝ ∞ Φ (A ×ˢ Ioo (-δ) δ) ∧
          (∀ y ∈ A, Φ (y, 0) = y) ∧
          (∀ q ∈ A ×ˢ Ioo (-δ) δ, Φ q ∈ V) ∧
          (∀ q ∈ A ×ˢ Ioo (-δ) δ,
            HasDerivAt (fun t ↦ Φ (q.1, t)) (N (Φ q) v) q.2) ∧
          (∀ y ∈ A, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
            s + t ∈ Ioo (-δ) δ → Φ (y, s) ∈ A →
            Φ (Φ (y, s), t) = Φ (y, s + t))) := by
  obtain ⟨V, p, N, hV, hxV, hVt, hN, hrange, hproj, hinj, hcommute⟩ :=
    exists_native_commuting_frame f P hP Q hReal D x
  refine ⟨V, N, hV, hxV, hVt, hN, hrange, hinj, hcommute, ?_⟩
  intro v
  exact LocalFlowExistenceBinding.exists_ambient_real_flow_of_complex_smooth
    ⟨V, hV⟩ (fun y ↦ N y v) (hN.clm_apply contDiffOn_const) _ hxV

omit [IsManifold (complexModel d) ∞ X] in
/-- Preserving complex flows of a native commuting frame give a holomorphic unit box flattening its
distribution. -/
theorem exists_unit_box_from_native_flow_data {c : ℕ}
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (k : OpenPartialHomeomorph X (ComplexModel d))
    (hk : ContMDiffOn (complexModel d) (complexModel d) ∞ k k.source)
    (hki : ContMDiffOn (complexModel d) (complexModel d) ∞ k.symm k.target)
    (x : X) (hx : x ∈ k.source)
    (Ω : Set (ComplexModel d)) (hΩ : IsOpen Ω) (hxΩ : k x ∈ Ω)
    (N : ComplexModel d → (Fin r → ℂ) →L[ℂ] ComplexModel d)
    (hNr : ∀ z ∈ Ω, LinearMap.range (N z).toLinearMap =
      (P (k.symm z)).map (mfderiv (complexModel d) (complexModel d) k (k.symm z)).toLinearMap)
    (A : (Fin c → ℂ) →L[ℂ] ComplexModel d)
    (hNinj : Function.Injective (N (k x))) (hAinj : Function.Injective A)
    (hcompl : IsCompl (LinearMap.range (N (k x)).toLinearMap) (LinearMap.range A.toLinearMap))
    (flow : Fin r → ℂ × ComplexModel d → ComplexModel d)
    (domain : Fin r → Set (ℂ × ComplexModel d)) (hopen : ∀ i, IsOpen (domain i))
    (hmem : ∀ i, (0, k x) ∈ domain i)
    (hsmooth : ∀ i, ContDiffOn ℂ ∞ (flow i) (domain i))
    (hzero : ∀ i y, (0, y) ∈ domain i → flow i (0, y) = y)
    (hODE : ∀ i q, q ∈ domain i →
      HasDerivAt (fun t ↦ flow i (t, q.2)) (N (flow i q) (Pi.single i 1)) q.1)
    (hpreserve : ∀ i j, i ≠ j → ∀ q, q ∈ domain i →
      fderiv ℂ (fun y ↦ flow i (q.1, y)) q.2 (N q.2 (Pi.single j 1)) =
        N (flow i q) (Pi.single j 1)) :
    ∃ b : OpenPartialHomeomorph X (ComplexModel r × ComplexModel c),
      x ∈ b.source ∧ b.source ⊆ k.source ∧
      b.target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)) ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) ∞ b b.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel c) (complexModel d) ∞ b.symm b.target ∧
      (∀ q ∈ b.source,
        (P q).map (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) b q).toLinearMap =
          LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap) := by
  have hzeroGerm (i : Fin r) : (fun y ↦ flow i (0, y)) =ᶠ[𝓝 (k x)] id :=
    Theorem12FlowCoordinates.zero_time_germ (flow i) (hopen i) (hmem i) (hzero i)
  have htime (i : Fin r) :
      HasDerivAt (fun t ↦ flow i (t, k x)) (N (k x) (Pi.single i 1)) 0 := by
    simpa only [hzero i (k x) (hmem i)] using hODE i (0, k x) (hmem i)
  obtain ⟨U, W, chart, hU, h0U, hW, h0W, hsource, hguards, hmap, hcenter,
      hxchart, hchart, hcharti, hderivative⟩ :=
    Theorem12FlowCoordinates.exists_finite_flow_chart_of_complementary_frames
      (N (k x)) A hNinj hAinj hcompl flow (k x) domain hopen hmem hsmooth hzeroGerm htime
  have hflatChart (y : ComplexModel d) (hy : y ∈ chart.target) :
      (LinearMap.range (N y).toLinearMap).map (fderiv ℂ chart.symm y).toLinearMap =
        LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap := by
    apply Theorem12FlowStraightening.finite_flow_chart_inverse_straightens flow
      (fun i y ↦ N y (Pi.single i 1)) A (k x) domain
      (fun i q hq ↦ ((hsmooth i).contDiffAt ((hopen i).mem_nhds hq)).differentiableAt
        (by simp)) hODE hpreserve chart hmap hguards (hcharti.differentiableOn (by simp))
      (fun y ↦ LinearMap.range (N y).toLinearMap) ?_ hy
    intro z hz
    exact Theorem12FlowStraightening.range_eq_span_of_columns (N z)
      (fun i ↦ N z (Pi.single i 1)) (fun _ ↦ rfl)
  let a := chart.symm.restrOpen Ω hΩ
  have ha : ContDiffOn ℂ ∞ a a.source := hcharti.mono inter_subset_left
  have hai : ContDiffOn ℂ ∞ a.symm a.target := hchart.mono inter_subset_left
  apply exists_unit_box_of_coordinate_straightening P k hk hki a ha hai ?_ x hx
    ⟨hxchart, hxΩ⟩
  intro q hq hqa
  have hrange := hNr (k q) hqa.2
  rw [k.left_inv hq] at hrange
  rw [← hrange]
  exact hflatChart (k q) hqa.1

end HolomorphicAnosov.Theorem12FrobeniusLocalAssembly








/-! Local real flows combine to give complex smooth flows on a common open domain. -/


/-! Variational equations give holomorphic spatial dependence and complex-time holomorphicity of
compositions of real flows. (Teschl, pp.45–47) -/

open Set
open scoped Topology _root_.Topology

namespace HolomorphicFlowSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A real continuous linear map commuting with multiplication by `i` respects all complex scalars. -/
private theorem map_complex_smul (L : E →L[ℝ] F)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) (z : ℂ) (v : E) :
    L (z • v) = z • L v := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := Complex.re_add_im z |>.symm
  rw [hz, add_smul, L.map_add, mul_smul, Complex.coe_smul, L.map_smul,
    Complex.coe_smul, L.map_smul, hI, add_smul, mul_smul, Complex.coe_smul,
    Complex.coe_smul]

/-- The complex continuous linear refinement of a real linear map commuting with multiplication by
`i`. -/
private def complexLinear (L : E →L[ℝ] F)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) : E →L[ℂ] F where
  toFun := L
  map_add' := L.map_add
  map_smul' := map_complex_smul L hI
  cont := L.continuous

/-- A real derivative commuting with multiplication by `i` defines a complex derivative of the same
map. -/
private theorem hasFDerivAt_complex_of_commutes {f : E → F} {x : E} {L : E →L[ℝ] F}
    (hf : HasFDerivAt f L x)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    HasFDerivAt f (complexLinear L hI) x := by
  apply hasFDerivAt_of_restrictScalars ℝ hf
  rfl

/-- Solutions of the linear variational equation with complex-linear coefficients commute with
multiplication by `i`. -/
private theorem variational_commutes_I
    (A : ℝ → E →L[ℂ] E) (Y : ℝ → E →L[ℝ] E)
    (a b t₀ : ℝ) (K : NNReal) (ht₀ : t₀ ∈ Ioo a b)
    (hbound : ∀ t ∈ Ioo a b, ‖A t‖ ≤ K)
    (hY : ∀ t ∈ Ioo a b, ∀ v : E,
      HasDerivAt (fun s ↦ Y s v) (A t (Y t v)) t)
    (hinit : Y t₀ = ContinuousLinearMap.id ℝ E) :
    ∀ t ∈ Ioo a b, ∀ v : E, Y t (Complex.I • v) = Complex.I • Y t v := by
  intro t ht v
  have huniq := ODE_solution_unique_of_mem_Ioo
    (v := fun t (z : E) ↦ A t z) (s := fun _ ↦ (univ : Set E)) (K := K)
    (f := fun t ↦ Y t (Complex.I • v)) (g := fun t ↦ Complex.I • Y t v)
    (fun t ht ↦ ((A t).lipschitzWith.weaken (hbound t ht)).lipschitzOnWith) ht₀
    (fun t ht ↦ ⟨hY t ht (Complex.I • v), mem_univ _⟩)
    (fun t ht ↦ ⟨by simpa only [map_smul, Pi.smul_def] using
      (hY t ht v).const_smul Complex.I,
      mem_univ _⟩)
    (by simp [hinit])
  exact huniq ht

/-- A real C² flow satisfying its differential equation satisfies the directional first variational
equation. (Teschl, pp.45–47, Eqs 2.46–2.49) -/
private theorem first_variation_at
    (Φ : E × ℝ → E) (X : E → E) (x : E) (t : ℝ) (v : E)
    (hΦ : ContDiffAt ℝ 2 Φ (x, t))
    (hX : DifferentiableAt ℝ X (Φ (x, t)))
    (hODE : ∀ᶠ z in nhds (x, t), fderiv ℝ Φ z (0, 1) = X (Φ z)) :
    HasDerivAt (fun s ↦ fderiv ℝ Φ (x, s) (v, 0))
      (fderiv ℝ X (Φ (x, t)) (fderiv ℝ Φ (x, t) (v, 0))) t := by
  have hD := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have htime : HasDerivAt (fun s : ℝ ↦ (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hleft := (hD.hasFDerivAt.comp_hasDerivAt t htime).clm_apply
    (hasDerivAt_const t (v, (0 : ℝ)))
  have hpart := hD.hasFDerivAt.clm_apply
    (hasFDerivAt_const (0, (1 : ℝ)) (x, t))
  have hright := hX.hasFDerivAt.comp (x, t) (hΦ.differentiableAt two_ne_zero).hasFDerivAt
  have hEq := (hpart.congr_of_eventuallyEq
    (Filter.Eventually.mono hODE fun _ hz ↦ hz.symm)).unique hright
  have hval := congrArg (fun L : (E × ℝ) →L[ℝ] E ↦ L (v, 0)) hEq
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, ContinuousLinearMap.flip_apply, map_zero, zero_add] at hval
  have hsym := hΦ.isSymmSndFDerivAt (by norm_num)
  simpa only [Function.comp_apply, ContinuousLinearMap.map_zero, add_zero,
    hsym.eq (0, 1) (v, 0), hval] using hleft

/-- A jointly real C² flow satisfies the first variational equation on its open domain. -/
private theorem first_variation_on
    (Φ : E × ℝ → E) (X : E → E) (D : Set (E × ℝ)) (hD : IsOpen D)
    (hΦ : ContDiffOn ℝ 2 Φ D)
    (hX : ∀ z ∈ D, DifferentiableAt ℝ X (Φ z))
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Φ (z.1, s)) (X (Φ z)) z.2)
    (x : E) (t : ℝ) (hxt : (x, t) ∈ D) (v : E) :
    HasDerivAt (fun s ↦ fderiv ℝ Φ (x, s) (v, 0))
      (fderiv ℝ X (Φ (x, t)) (fderiv ℝ Φ (x, t) (v, 0))) t := by
  apply first_variation_at Φ X x t v ((hΦ (x, t) hxt).contDiffAt (hD.mem_nhds hxt))
    (hX (x, t) hxt)
  filter_upwards [hD.mem_nhds hxt] with z hz
  have hd := ((hΦ z hz).contDiffAt (hD.mem_nhds hz)).differentiableAt two_ne_zero
  have htime : HasDerivAt (fun s : ℝ ↦ (z.1, s)) (0, 1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  exact (hd.hasFDerivAt.comp_hasDerivAt z.2 htime).unique (hODE z hz)

/-- A real C² flow of a holomorphic field with locally bounded derivative is holomorphic in its
spatial variable. -/
private theorem spatial_holomorphic_of_real_flow
    (Φ : E × ℝ → E) (X : E → E) (U : Set E) (hU : IsOpen U)
    (a b : ℝ) (hzero : (0 : ℝ) ∈ Ioo a b)
    (hΦ : ContDiffOn ℝ 2 Φ (U ×ˢ Ioo a b))
    (hX : ∀ z ∈ U ×ˢ Ioo a b, DifferentiableAt ℂ X (Φ z))
    (hODE : ∀ z ∈ U ×ˢ Ioo a b,
      HasDerivAt (fun s ↦ Φ (z.1, s)) (X (Φ z)) z.2)
    (hinit : ∀ x ∈ U, Φ (x, 0) = x)
    (K : NNReal)
    (hbound : ∀ z ∈ U ×ˢ Ioo a b, ‖fderiv ℂ X (Φ z)‖ ≤ K) :
    ∀ t ∈ Ioo a b, DifferentiableOn ℂ (fun x ↦ Φ (x, t)) U := by
  intro t ht x hx
  let Y : ℝ → E →L[ℝ] E := fun s ↦
    (fderiv ℝ Φ (x, s)).comp ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ))
  have hprod (s : ℝ) : HasFDerivAt (fun y : E ↦ (y, s))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const s x)
  have hslice (s : ℝ) (hs : s ∈ Ioo a b) : HasFDerivAt (fun y ↦ Φ (y, s)) (Y s) x :=
    (((hΦ (x, s) ⟨hx, hs⟩).contDiffAt
      ((hU.prod isOpen_Ioo).mem_nhds ⟨hx, hs⟩)).differentiableAt two_ne_zero).hasFDerivAt.comp x
        (hprod s)
  have hYinit : Y 0 = ContinuousLinearMap.id ℝ E := by
    apply (HasFDerivAt.congr_of_eventuallyEq (hslice 0 hzero) ?_).unique (hasFDerivAt_id x)
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hinit y hy).symm
  have hvar (s : ℝ) (hs : s ∈ Ioo a b) (v : E) :
      HasDerivAt (fun q ↦ Y q v) ((fderiv ℂ X (Φ (x, s))) (Y s v)) s := by
    have h := first_variation_on Φ X (U ×ˢ Ioo a b) (hU.prod isOpen_Ioo) hΦ
      (fun z hz ↦ (hX z hz).restrictScalars ℝ) hODE x s ⟨hx, hs⟩ v
    simpa only [Y, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply, (hX (x, s) ⟨hx, hs⟩).fderiv_restrictScalars ℝ,
      ContinuousLinearMap.coe_restrictScalars'] using h
  have hi := variational_commutes_I (fun s ↦ fderiv ℂ X (Φ (x, s))) Y a b 0 K hzero
    (fun s hs ↦ hbound (x, s) ⟨hx, hs⟩) hvar hYinit t ht
  exact (hasFDerivAt_complex_of_commutes (hslice t ht) hi).differentiableAt.differentiableWithinAt

/-- The spatial derivative of a real flow preserves its own vector field. -/
private theorem own_flow_pushes_field
    (Φ : E × ℝ → E) (X : E → E) (x : E) (t : ℝ) (L : E →L[ℝ] E)
    (hzero : Φ (x, 0) = x)
    (hslice : HasFDerivAt (fun y ↦ Φ (y, t)) L x)
    (hODEzero : HasDerivAt (fun s ↦ Φ (x, s)) (X x) 0)
    (hODEt : HasDerivAt (fun s ↦ Φ (x, s)) (X (Φ (x, t))) t)
    (hgroup : ∀ᶠ s in nhds (0 : ℝ), Φ (Φ (x, s), t) = Φ (x, s + t)) :
    L (X x) = X (Φ (x, t)) := by
  have hleft := hslice.comp_hasDerivAt_of_eq 0 hODEzero hzero.symm
  have hright := hODEt.hasFDerivAt.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).add_const t) (by simp)
  exact (hleft.congr_of_eventuallyEq (Filter.Eventually.mono hgroup fun _ hs ↦ hs.symm)).unique
    (by simpa [Function.comp_def] using hright)

/-- A jointly real differentiable two-time map satisfying the Cauchy–Riemann equations has the
corresponding complex time derivative. -/
private theorem hasDerivAt_complex_of_two_real_directions
    (Ψ : ℝ × ℝ → E) (z : ℂ) (L : (ℝ × ℝ) →L[ℝ] E) (v : E)
    (hΨ : HasFDerivAt Ψ L (z.re, z.im))
    (hre : L (1, 0) = v) (him : L (0, 1) = Complex.I • v) :
    HasDerivAt (fun w : ℂ ↦ Ψ (w.re, w.im)) v z := by
  have hcoord := (Complex.reCLM.hasFDerivAt (x := z)).prodMk
    (Complex.imCLM.hasFDerivAt (x := z))
  have h := hΨ.comp z hcoord
  have hI : (L.comp (Complex.reCLM.prod Complex.imCLM)) Complex.I =
      Complex.I • (L.comp (Complex.reCLM.prod Complex.imCLM)) 1 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, hre] using him
  have hc := (h.complexOfReal_hasFDerivAt hI).hasDerivAt
  change HasDerivAt (fun w : ℂ ↦ Ψ (w.re, w.im)) (L (1, 0)) z at hc
  simpa only [hre] using hc

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- A continuous coefficient is uniformly bounded on some product neighborhood of a point. -/
private theorem exists_product_norm_bound
    (A : E × ℝ → F) (x : E) (hA : ContinuousAt A (x, 0))
    (U : Set E) (hU : IsOpen U) (hx : x ∈ U) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (V : Set E) (τ : ℝ) (K : NNReal),
      IsOpen V ∧ x ∈ V ∧ 0 < τ ∧ V ⊆ U ∧ τ ≤ δ ∧
      ∀ z ∈ V ×ˢ Ioo (-τ) τ, ‖A z‖ ≤ K := by
  have hnorm : ∀ᶠ z in nhds (x, (0 : ℝ)), ‖A z‖ < ‖A (x, 0)‖ + 1 :=
    hA.norm.eventually (Iio_mem_nhds (lt_add_one _))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnorm
  refine ⟨U ∩ Metric.ball x r, min r δ,
    ⟨‖A (x, 0)‖ + 1, by positivity⟩, hU.inter Metric.isOpen_ball,
    ⟨hx, Metric.mem_ball_self hr⟩, lt_min hr hδ, inter_subset_left, min_le_right _ _, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.ball (x, (0 : ℝ)) r := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨hz.1.2, ?_⟩
    simpa only [Real.dist_eq, sub_zero, abs_lt] using
      (show -r < z.2 ∧ z.2 < r from
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_left r δ)) hz.2.1,
          lt_of_lt_of_le hz.2.2 (min_le_left r δ)⟩)
  exact (hball hzball).le

/-- Joint real differentiability and complex differentiability of both partial maps imply joint
complex differentiability. -/
private theorem joint_holomorphic_of_real_and_partials
    (H : E × ℂ → F) (x : E) (z : ℂ) (L : (E × ℂ) →L[ℝ] F)
    (hH : HasFDerivAt H L (x, z))
    (hspatial : DifferentiableAt ℂ (fun y ↦ H (y, z)) x)
    (htime : DifferentiableAt ℂ (fun w ↦ H (x, w)) z) :
    DifferentiableAt ℂ H (x, z) := by
  have hs := hH.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) z x))
  have ht := hH.comp z ((hasFDerivAt_const (𝕜 := ℝ) x z).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) z))
  have hsEq := hs.unique (hspatial.hasFDerivAt.restrictScalars ℝ)
  have htEq := ht.unique (htime.hasFDerivAt.restrictScalars ℝ)
  have hsv (v : E) : L (v, 0) = fderiv ℂ (fun y ↦ H (y, z)) x v := by
    simpa using congrArg (fun T : E →L[ℝ] F ↦ T v) hsEq
  have htw (w : ℂ) : L (0, w) = fderiv ℂ (fun q ↦ H (x, q)) z w := by
    simpa using congrArg (fun T : ℂ →L[ℝ] F ↦ T w) htEq
  apply (hasFDerivAt_complex_of_commutes hH ?_).differentiableAt
  intro p
  calc
    L (Complex.I • p) = L (Complex.I • p.1, 0) + L (0, Complex.I • p.2) := by
      rw [← L.map_add]
      congr 1
      ext <;> simp
    _ = Complex.I • L (p.1, 0) + Complex.I • L (0, p.2) := by
      simp only [hsv, htw, map_smul]
    _ = Complex.I • L p := by
      rw [← smul_add, ← L.map_add]
      simp

/-- The composition of real flows of `X` and `iX` has complex time derivative equal to `X` at its
image. -/
private theorem complex_time_derivative_of_real_flows
    (Φ Ψ : E × ℝ → E) (X : E → E) (x : E) (z : ℂ)
    (M : (E × ℝ) →L[ℝ] E)
    (hΦ : HasFDerivAt Φ M (Ψ (x, z.im), z.re))
    (hspatial : DifferentiableAt ℂ (fun y ↦ Φ (y, z.re)) (Ψ (x, z.im)))
    (hΨ : HasDerivAt (fun s ↦ Ψ (x, s)) (Complex.I • X (Ψ (x, z.im))) z.im)
    (hzero : Φ (Ψ (x, z.im), 0) = Ψ (x, z.im))
    (hODEzero : HasDerivAt (fun s ↦ Φ (Ψ (x, z.im), s))
      (X (Ψ (x, z.im))) 0)
    (hODEt : HasDerivAt (fun s ↦ Φ (Ψ (x, z.im), s))
      (X (Φ (Ψ (x, z.im), z.re))) z.re)
    (hgroup : ∀ᶠ s in nhds (0 : ℝ),
      Φ (Φ (Ψ (x, z.im), s), z.re) = Φ (Ψ (x, z.im), s + z.re)) :
    HasDerivAt (fun w : ℂ ↦ Φ (Ψ (x, w.im), w.re))
      (X (Φ (Ψ (x, z.im), z.re))) z := by
  let y := Ψ (x, z.im)
  have hs := hΦ.comp y ((hasFDerivAt_id (𝕜 := ℝ) y).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) z.re y))
  have hsEq := hs.unique (hspatial.hasFDerivAt.restrictScalars ℝ)
  have hsval (v : E) : M (v, 0) = fderiv ℂ (fun q ↦ Φ (q, z.re)) y v := by
    simpa using congrArg (fun T : E →L[ℝ] E ↦ T v) hsEq
  have hpush := own_flow_pushes_field Φ X y z.re
    (M.comp ((ContinuousLinearMap.id ℝ E).prod 0)) hzero hs hODEzero hODEt hgroup
  have hpushval : M (X y, 0) = X (Φ (y, z.re)) := by simpa using hpush
  have hdt := hΦ.comp_hasDerivAt z.re
    ((hasDerivAt_const (𝕜 := ℝ) z.re y).prodMk (hasDerivAt_id z.re))
  have htimeval : M (0, 1) = X (Φ (y, z.re)) := by
    simpa [Function.comp_def] using hdt.unique hODEt
  have hi := hΨ.hasFDerivAt.comp (z.re, z.im)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (z.re, z.im)))
  have hargs := hi.prodMk (hasFDerivAt_fst (𝕜 := ℝ) (p := (z.re, z.im)))
  have hd := hΦ.comp (z.re, z.im) hargs
  apply hasDerivAt_complex_of_two_real_directions
    (fun p : ℝ × ℝ ↦ Φ (Ψ (x, p.2), p.1)) z _ (X (Φ (y, z.re))) hd
  · simpa using htimeval
  · change M ((1 : ℝ) • (Complex.I • X y), 0) = Complex.I • X (Φ (y, z.re))
    rw [one_smul, hsval, map_smul, ← hsval, hpushval]

/-- The composition of spatially holomorphic real flows of `X` and `iX` is jointly holomorphic in
complex time and space. -/
private theorem composed_real_flows_joint_holomorphic
    (Φ Ψ : E × ℝ → E) (X : E → E) (x : E) (z : ℂ)
    (M N : (E × ℝ) →L[ℝ] E)
    (hΦ : HasFDerivAt Φ M (Ψ (x, z.im), z.re))
    (hΨjoint : HasFDerivAt Ψ N (x, z.im))
    (hΦspatial : DifferentiableAt ℂ (fun y ↦ Φ (y, z.re)) (Ψ (x, z.im)))
    (hΨspatial : DifferentiableAt ℂ (fun y ↦ Ψ (y, z.im)) x)
    (hΨ : HasDerivAt (fun s ↦ Ψ (x, s)) (Complex.I • X (Ψ (x, z.im))) z.im)
    (hzero : Φ (Ψ (x, z.im), 0) = Ψ (x, z.im))
    (hODEzero : HasDerivAt (fun s ↦ Φ (Ψ (x, z.im), s))
      (X (Ψ (x, z.im))) 0)
    (hODEt : HasDerivAt (fun s ↦ Φ (Ψ (x, z.im), s))
      (X (Φ (Ψ (x, z.im), z.re))) z.re)
    (hgroup : ∀ᶠ s in nhds (0 : ℝ),
      Φ (Φ (Ψ (x, z.im), s), z.re) = Φ (Ψ (x, z.im), s + z.re)) :
    DifferentiableAt ℂ (fun p : E × ℂ ↦ Φ (Ψ (p.1, p.2.im), p.2.re)) (x, z) := by
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (x, z))
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := (x, z))
  have him := (Complex.imCLM.hasFDerivAt (x := z)).comp (x, z) hs
  have hre := (Complex.reCLM.hasFDerivAt (x := z)).comp (x, z) hs
  have hi := hΨjoint.comp (x, z) (hf.prodMk him)
  have hreal := hΦ.comp (x, z) (hi.prodMk hre)
  apply joint_holomorphic_of_real_and_partials
    (fun p : E × ℂ ↦ Φ (Ψ (p.1, p.2.im), p.2.re)) x z _ hreal
  · have hc : DifferentiableAt ℂ
        ((fun y : E ↦ Φ (y, z.re)) ∘ (fun y : E ↦ Ψ (y, z.im))) x :=
      hΦspatial.comp x hΨspatial
    exact hc
  · exact (complex_time_derivative_of_real_flows Φ Ψ X x z M hΦ hΦspatial
      hΨ hzero hODEzero hODEt hgroup).differentiableAt

/-- A real flow of a complex smooth field is spatially holomorphic on a product neighborhood of its
initial point. -/
private theorem spatial_holomorphic_near_origin
    (Φ : E × ℝ → E) (X : E → E) (U : Set E) (hU : IsOpen U)
    (x : E) (hx : x ∈ U) (δ : ℝ) (hδ : 0 < δ)
    (hΦ : ContDiffOn ℝ 2 Φ (U ×ˢ Ioo (-δ) δ))
    (hX : ∀ z ∈ U ×ˢ Ioo (-δ) δ, DifferentiableAt ℂ X (Φ z))
    (hODE : ∀ z ∈ U ×ˢ Ioo (-δ) δ,
      HasDerivAt (fun s ↦ Φ (z.1, s)) (X (Φ z)) z.2)
    (hinit : ∀ y ∈ U, Φ (y, 0) = y)
    (hcoefficient : ContinuousAt (fun p ↦ fderiv ℂ X (Φ p)) (x, 0)) :
    ∃ (V : Set E) (τ : ℝ), IsOpen V ∧ x ∈ V ∧ 0 < τ ∧ V ⊆ U ∧ τ ≤ δ ∧
      ∀ t ∈ Ioo (-τ) τ, DifferentiableOn ℂ (fun y ↦ Φ (y, t)) V := by
  obtain ⟨V, τ, K, hV, hxV, hτ, hVU, hτδ, hbound⟩ :=
    exists_product_norm_bound (fun p ↦ fderiv ℂ X (Φ p)) x hcoefficient U hU hx δ hδ
  have hsub : V ×ˢ Ioo (-τ) τ ⊆ U ×ˢ Ioo (-δ) δ := by
    intro p hp
    exact ⟨hVU hp.1, lt_of_le_of_lt (neg_le_neg hτδ) hp.2.1,
      lt_of_lt_of_le hp.2.2 hτδ⟩
  refine ⟨V, τ, hV, hxV, hτ, hVU, hτδ, ?_⟩
  exact spatial_holomorphic_of_real_flow Φ X V hV (-τ) τ ⟨neg_neg_of_pos hτ, hτ⟩
    (hΦ.mono hsub) (fun p hp ↦ hX p (hsub hp))
    (fun p hp ↦ hODE p (hsub hp)) (fun y hy ↦ hinit y (hVU hy)) K hbound


end HolomorphicFlowSupport


/-! Smooth fields on open domains admit local real flows. -/

open Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology




/-! Real smoothness and complex differentiability imply complex smoothness on an open set. -/

noncomputable section
open scoped ContDiff Topology _root_.Topology
open Set Filter

namespace HolomorphicAnosov.RealSmoothComplexSmoothScratch

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : E → F} {Ω : Set E}

/-- Directional derivatives of a real C², complex-differentiable map are complex differentiable on
its open domain. -/
private theorem directional_derivative_complex_differentiable
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hc : DifferentiableOn ℂ f Ω) (v : E) :
    DifferentiableOn ℂ (fun x ↦ fderiv ℝ f x v) Ω := by
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) Ω :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hf |>.2
  intro x hx
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hDf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  let A := fderiv ℝ (fderiv ℝ f) x
  have heval (w : E) : HasFDerivAt (fun y ↦ fderiv ℝ f y w) (A.flip w) x := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hsym : ∀ a b, A a b = A b a :=
    (hf.contDiffAt (hΩ.mem_nhds hx)).isSymmSndFDerivAt (by simp)
  have hslot (c : ℂ) (w a : E) : A a (c • w) = c • A a w := by
    have heq : (fun y ↦ fderiv ℝ f y (c • w)) =ᶠ[𝓝 x]
        (fun y ↦ c • fderiv ℝ f y w) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      rw [((hc y hy).differentiableAt (hΩ.mem_nhds hy)).fderiv_restrictScalars ℝ]
      simp
    have hder := ((heval w).const_smul c).congr_of_eventuallyEq heq
    have he := (heval (c • w)).fderiv.symm.trans hder.fderiv
    exact congrArg (fun L : E →L[ℝ] F ↦ L a) he
  let L : E →L[ℂ] F :=
    { toFun := A.flip v
      map_add' := (A.flip v).map_add
      map_smul' := by
        intro c w
        change A (c • w) v = c • A w v
        rw [hsym, hslot, hsym v w]
      cont := (A.flip v).continuous }
  have hL : HasFDerivAt (fun y ↦ fderiv ℝ f y v) L x := by
    apply hasFDerivAt_of_restrictScalars ℝ (heval v)
    rfl
  exact hL.differentiableAt.differentiableWithinAt


variable [FiniteDimensional ℂ E]

/-- A real smooth, complex-differentiable map is complex smooth to every finite order. -/
private theorem real_smooth_complex_contDiff_nat (n : ℕ)
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hc : DifferentiableOn ℂ f Ω) : ContDiffOn ℂ n f Ω := by
  induction n generalizing f with
  | zero =>
      exact contDiffOn_zero.mpr hf.continuousOn
  | succ n ih =>
      have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) Ω :=
        (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hf |>.2
      have hv (v : E) : ContDiffOn ℂ n (fun x ↦ fderiv ℝ f x v) Ω :=
        ih (hDf.clm_apply contDiffOn_const)
          (directional_derivative_complex_differentiable hΩ hf hc v)
      have hw (v : E) : ContDiffOn ℂ n (fun x ↦ fderivWithin ℂ f Ω x v) Ω := by
        apply (hv v).congr
        intro x hx
        rw [fderivWithin_of_isOpen hΩ hx,
          ((hc x hx).differentiableAt (hΩ.mem_nhds hx)).fderiv_restrictScalars ℝ]
        rfl
      have h := contDiffOn_succ_of_fderiv_apply (n := (n : WithTop ℕ∞)) hc
        (by simp) hw
      simpa only [Nat.cast_add, Nat.cast_one] using h

/-- A real C∞, complex-differentiable map on an open set with finite-dimensional source is complex
C∞ there. -/
private theorem real_smooth_complex_smooth
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hc : DifferentiableOn ℂ f Ω) : ContDiffOn ℂ ∞ f Ω := by
  apply contDiffOn_infty.mpr
  intro n
  exact real_smooth_complex_contDiff_nat n hΩ hf hc


end HolomorphicAnosov.RealSmoothComplexSmoothScratch

namespace ComplexFlowExistence

open Set
open scoped Topology _root_.Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A complex smooth field admits a local real smooth flow with holomorphic spatial slices. -/
private theorem exists_spatially_holomorphic_real_flow
    (Ω : TopologicalSpace.Opens E) (X : E → E)
    (hX : ContDiffOn ℂ ∞ X Ω) (x : E) (hx : x ∈ Ω) :
    ∃ (A : Set E) (δ : ℝ) (Φ : E × ℝ → E),
      IsOpen A ∧ x ∈ A ∧ A ⊆ Ω ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (A ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ A, Φ (y, 0) = y) ∧
      (∀ p ∈ A ×ˢ Ioo (-δ) δ, Φ p ∈ Ω) ∧
      (∀ p ∈ A ×ˢ Ioo (-δ) δ,
        HasDerivAt (fun s ↦ Φ (p.1, s)) (X (Φ p)) p.2) ∧
      (∀ y ∈ A, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
        s + t ∈ Ioo (-δ) δ → Φ (y, s) ∈ A →
        Φ (Φ (y, s), t) = Φ (y, s + t)) ∧
      (∀ t ∈ Ioo (-δ) δ, DifferentiableOn ℂ (fun y ↦ Φ (y, t)) A) := by
  obtain ⟨U, δ, Φ, hU, hxU, hUΩ, hδ, hΦ, hinit, hrange, hODE, hgroup⟩ :=
    LocalFlowExistenceBinding.exists_ambient_real_flow_of_complex_smooth Ω X hX x hx
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hΦat : ContinuousAt Φ (x, 0) :=
    (hΦ.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hxU, hzero⟩)).continuousAt
  have hDX : ContinuousOn (fderiv ℂ X) Ω :=
    (hX.fderiv_of_isOpen Ω.isOpen (m := 0) (by simp)).continuousOn
  have hcoeff : ContinuousAt (fun p ↦ fderiv ℂ X (Φ p)) (x, 0) :=
    (hDX.continuousAt (Ω.isOpen.mem_nhds (hrange (x, 0) ⟨hxU, hzero⟩))).comp hΦat
  have hXd : ∀ p ∈ U ×ˢ Ioo (-δ) δ, DifferentiableAt ℂ X (Φ p) := by
    intro p hp
    exact (hX.contDiffAt (Ω.isOpen.mem_nhds (hrange p hp))).differentiableAt (by simp)
  obtain ⟨V, τ, hV, hxV, hτ, hVU, hτδ, hspatial⟩ :=
    HolomorphicFlowSupport.spatial_holomorphic_near_origin Φ X U hU x hxU δ hδ
      (hΦ.of_le (by simp)) hXd hODE hinit hcoeff
  have htime : Ioo (-τ) τ ⊆ Ioo (-δ) δ := by
    intro t ht
    exact ⟨lt_of_le_of_lt (neg_le_neg hτδ) ht.1, lt_of_lt_of_le ht.2 hτδ⟩
  have hsub : V ×ˢ Ioo (-τ) τ ⊆ U ×ˢ Ioo (-δ) δ :=
    Set.prod_mono hVU htime
  refine ⟨V, τ, Φ, hV, hxV, hVU.trans hUΩ, hτ, hΦ.mono hsub,
    (fun y hy ↦ hinit y (hVU hy)), (fun p hp ↦ hrange p (hsub hp)),
    (fun p hp ↦ hODE p (hsub hp)), ?_, hspatial⟩
  intro y hy s hs t ht hst hrecv
  exact hgroup y (hVU hy) s (htime hs) t (htime ht) (htime hst) (hVU hrecv)

omit [FiniteDimensional ℂ E] in
/-- The real flow group law holds near zero time at each interior receiving point. -/
private theorem eventually_own_group
    (Φ : E × ℝ → E) (A : Set E) (hA : IsOpen A)
    (δ : ℝ) (hδ : 0 < δ)
    (hΦ : ContDiffOn ℝ ∞ Φ (A ×ˢ Ioo (-δ) δ))
    (hinit : ∀ y ∈ A, Φ (y, 0) = y)
    (hgroup : ∀ y ∈ A, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
      s + t ∈ Ioo (-δ) δ → Φ (y, s) ∈ A → Φ (Φ (y, s), t) = Φ (y, s + t))
    (y : E) (hy : y ∈ A) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
    ∀ᶠ s in nhds (0 : ℝ), Φ (Φ (y, s), t) = Φ (y, s + t) := by
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hc : ContinuousAt (fun s : ℝ ↦ Φ (y, s)) 0 :=
    ((hΦ.contDiffAt ((hA.prod isOpen_Ioo).mem_nhds ⟨hy, hzero⟩)).continuousAt).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hrecv : ∀ᶠ s in nhds (0 : ℝ), Φ (y, s) ∈ A :=
    hc.preimage_mem_nhds (hA.mem_nhds (by simpa only [hinit y hy] using hy))
  have hsum : ∀ᶠ s in nhds (0 : ℝ), s + t ∈ Ioo (-δ) δ := by
    exact (continuousAt_id.add_const t).preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (by simpa using ht))
  filter_upwards [isOpen_Ioo.mem_nhds hzero, hsum, hrecv] with s hs hst hsA
  exact hgroup y hy s hs t ht hst hsA



/-- The real flows of `X` and `iX` combine into a complex smooth flow on a common receiving domain. -/
private theorem complex_flow_of_real_pair
    (Ω : TopologicalSpace.Opens E) (X : E → E) (x : E)
    (A B : Set E) (δ ε : ℝ) (Φ Ψ : E × ℝ → E)
    (hA : IsOpen A) (hxA : x ∈ A) (hAΩ : A ⊆ Ω) (hδ : 0 < δ)
    (hΦ : ContDiffOn ℝ ∞ Φ (A ×ˢ Ioo (-δ) δ))
    (hΦinit : ∀ y ∈ A, Φ (y, 0) = y)
    (hΦrange : ∀ p ∈ A ×ˢ Ioo (-δ) δ, Φ p ∈ Ω)
    (hΦODE : ∀ p ∈ A ×ˢ Ioo (-δ) δ,
      HasDerivAt (fun s ↦ Φ (p.1, s)) (X (Φ p)) p.2)
    (hΦgroup : ∀ y ∈ A, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
      s + t ∈ Ioo (-δ) δ → Φ (y, s) ∈ A → Φ (Φ (y, s), t) = Φ (y, s + t))
    (hΦspatial : ∀ t ∈ Ioo (-δ) δ, DifferentiableOn ℂ (fun y ↦ Φ (y, t)) A)
    (hB : IsOpen B) (hxB : x ∈ B) (hε : 0 < ε)
    (hΨ : ContDiffOn ℝ ∞ Ψ (B ×ˢ Ioo (-ε) ε))
    (hΨinit : ∀ y ∈ B, Ψ (y, 0) = y)
    (hΨODE : ∀ p ∈ B ×ˢ Ioo (-ε) ε,
      HasDerivAt (fun s ↦ Ψ (p.1, s)) (Complex.I • X (Ψ p)) p.2)
    (hΨspatial : ∀ t ∈ Ioo (-ε) ε, DifferentiableOn ℂ (fun y ↦ Ψ (y, t)) B) :
    ∃ (U : Set E) (τ : ℝ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ 0 < τ ∧
      ContDiffOn ℂ ∞ (fun p : E × ℂ ↦ Φ (Ψ (p.1, p.2.im), p.2.re))
        (U ×ˢ Metric.ball 0 τ) ∧
      (∀ y ∈ U, Φ (Ψ (y, 0), 0) = y) ∧
      (∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) τ, Φ (Ψ (p.1, p.2.im), p.2.re) ∈ Ω) ∧
      (∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) τ,
        HasDerivAt (fun z : ℂ ↦ Φ (Ψ (p.1, z.im), z.re))
          (X (Φ (Ψ (p.1, p.2.im), p.2.re))) p.2) ∧
      (∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) τ,
        p.1 ∈ B ∧ p.2.im ∈ Ioo (-ε) ε ∧
        Ψ (p.1, p.2.im) ∈ A ∧ p.2.re ∈ Ioo (-δ) δ) := by
  let S : Set (E × ℂ) := {p | p.1 ∈ B ∧ p.2.im ∈ Ioo (-ε) ε ∧
    Ψ (p.1, p.2.im) ∈ A ∧ p.2.re ∈ Ioo (-δ) δ}
  let D : Set (E × ℂ) := interior S
  let H : E × ℂ → E := fun p ↦ Φ (Ψ (p.1, p.2.im), p.2.re)
  have hzeroδ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hzeroε : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hΨat : ContinuousAt Ψ (x, 0) :=
    (hΨ.contDiffAt ((hB.prod isOpen_Ioo).mem_nhds ⟨hxB, hzeroε⟩)).continuousAt
  have hargs : ContinuousAt (fun p : E × ℂ ↦ (p.1, p.2.im)) (x, 0) :=
    continuousAt_fst.prodMk (Complex.imCLM.continuous.continuousAt.comp continuousAt_snd)
  have hrecv : ∀ᶠ p : E × ℂ in nhds (x, 0), Ψ (p.1, p.2.im) ∈ A := by
    have hcomp : ContinuousAt (fun p : E × ℂ ↦ Ψ (p.1, p.2.im)) (x, 0) :=
      hΨat.comp_of_eq hargs (by simp)
    exact hcomp.preimage_mem_nhds
      (hA.mem_nhds (by simpa only [Complex.zero_im, hΨinit x hxB] using hxA))
  have hS : S ∈ nhds (x, (0 : ℂ)) := by
    have hb : ∀ᶠ p : E × ℂ in nhds (x, 0), p.1 ∈ B :=
      continuousAt_fst.preimage_mem_nhds (hB.mem_nhds hxB)
    have hi : ∀ᶠ p : E × ℂ in nhds (x, 0), p.2.im ∈ Ioo (-ε) ε :=
      (Complex.imCLM.continuous.continuousAt.comp
      continuousAt_snd).preimage_mem_nhds (isOpen_Ioo.mem_nhds hzeroε)
    have hr : ∀ᶠ p : E × ℂ in nhds (x, 0), p.2.re ∈ Ioo (-δ) δ :=
      (Complex.reCLM.continuous.continuousAt.comp
      continuousAt_snd).preimage_mem_nhds (isOpen_Ioo.mem_nhds hzeroδ)
    filter_upwards [hb, hi, hrecv, hr] with p hpB hpI hpA hpR
    exact ⟨hpB, hpI, hpA, hpR⟩
  have hxD : (x, (0 : ℂ)) ∈ D := mem_interior_iff_mem_nhds.mpr hS
  have hD : IsOpen D := isOpen_interior
  have hguard (p : E × ℂ) (hp : p ∈ D) :
      p.1 ∈ B ∧ p.2.im ∈ Ioo (-ε) ε ∧
      Ψ (p.1, p.2.im) ∈ A ∧ p.2.re ∈ Ioo (-δ) δ := by
    have hh : p ∈ S := interior_subset hp
    exact hh
  have hreal : ContDiffOn ℝ ∞ H D := by
    intro p hp
    obtain ⟨hy, hi, ha, hr⟩ := hguard p hp
    have hΨp : ContDiffAt ℝ ∞ Ψ (p.1, p.2.im) :=
      hΨ.contDiffAt ((hB.prod isOpen_Ioo).mem_nhds ⟨hy, hi⟩)
    have hΦp : ContDiffAt ℝ ∞ Φ (Ψ (p.1, p.2.im), p.2.re) :=
      hΦ.contDiffAt ((hA.prod isOpen_Ioo).mem_nhds ⟨ha, hr⟩)
    have him : ContDiffAt ℝ ∞ (fun q : E × ℂ ↦ q.2.im) p :=
      Complex.imCLM.contDiff.contDiffAt.comp p contDiffAt_snd
    have hre : ContDiffAt ℝ ∞ (fun q : E × ℂ ↦ q.2.re) p :=
      Complex.reCLM.contDiff.contDiffAt.comp p contDiffAt_snd
    exact (hΦp.comp p ((hΨp.comp p (contDiffAt_fst.prodMk him)).prodMk hre)).contDiffWithinAt
  have htime (p : E × ℂ) (hp : p ∈ D) :
      HasDerivAt (fun z : ℂ ↦ H (p.1, z)) (X (H p)) p.2 := by
    obtain ⟨hy, hi, ha, hr⟩ := hguard p hp
    have hΦp : DifferentiableAt ℝ Φ (Ψ (p.1, p.2.im), p.2.re) := (hΦ.contDiffAt ((hA.prod isOpen_Ioo).mem_nhds
      ⟨ha, hr⟩)).differentiableAt (by simp)
    have hsp := (hΦspatial p.2.re hr _ ha).differentiableAt (hA.mem_nhds ha)
    exact HolomorphicFlowSupport.complex_time_derivative_of_real_flows Φ Ψ X p.1 p.2 _
      hΦp.hasFDerivAt hsp (hΨODE (p.1, p.2.im) ⟨hy, hi⟩) (hΦinit _ ha)
      (by simpa only [hΦinit _ ha] using hΦODE (Ψ (p.1, p.2.im), 0) ⟨ha, hzeroδ⟩)
      (hΦODE (Ψ (p.1, p.2.im), p.2.re) ⟨ha, hr⟩)
      (eventually_own_group Φ A hA δ hδ hΦ hΦinit hΦgroup _ ha _ hr)
  have hc : DifferentiableOn ℂ H D := by
    intro p hp
    obtain ⟨hy, hi, ha, hr⟩ := hguard p hp
    have hΦp : DifferentiableAt ℝ Φ (Ψ (p.1, p.2.im), p.2.re) := (hΦ.contDiffAt ((hA.prod isOpen_Ioo).mem_nhds
      ⟨ha, hr⟩)).differentiableAt (by simp)
    have hΨp : DifferentiableAt ℝ Ψ (p.1, p.2.im) := (hΨ.contDiffAt ((hB.prod isOpen_Ioo).mem_nhds
      ⟨hy, hi⟩)).differentiableAt (by simp)
    exact (HolomorphicFlowSupport.composed_real_flows_joint_holomorphic Φ Ψ X p.1 p.2 _ _
      hΦp.hasFDerivAt hΨp.hasFDerivAt
      ((hΦspatial p.2.re hr _ ha).differentiableAt (hA.mem_nhds ha))
      ((hΨspatial p.2.im hi _ hy).differentiableAt (hB.mem_nhds hy))
      (hΨODE (p.1, p.2.im) ⟨hy, hi⟩) (hΦinit _ ha)
      (by simpa only [hΦinit _ ha] using hΦODE (Ψ (p.1, p.2.im), 0) ⟨ha, hzeroδ⟩)
      (hΦODE (Ψ (p.1, p.2.im), p.2.re) ⟨ha, hr⟩)
      (eventually_own_group Φ A hA δ hδ hΦ hΦinit hΦgroup _ ha _ hr)).differentiableWithinAt
  have hcomplex : ContDiffOn ℂ ∞ H D :=
    HolomorphicAnosov.RealSmoothComplexSmoothScratch.real_smooth_complex_smooth hD hreal hc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hxD)
  have hsub : Metric.ball x r ×ˢ Metric.ball (0 : ℂ) r ⊆ D := by
    intro p hp
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hp.1, hp.2⟩
  refine ⟨Metric.ball x r, r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_, hr,
    hcomplex.mono hsub, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hg := hguard (y, 0) (hsub ⟨hy, Metric.mem_ball_self hr⟩)
    exact hAΩ (by simpa only [Complex.zero_im, hΨinit y hg.1] using hg.2.2.1)
  · intro y hy
    have hg := hguard (y, 0) (hsub ⟨hy, Metric.mem_ball_self hr⟩)
    rw [hΨinit y hg.1, hΦinit y]
    simpa only [Complex.zero_im, hΨinit y hg.1] using hg.2.2.1
  · intro p hp
    have hg := hguard p (hsub hp)
    exact hΦrange _ ⟨hg.2.2.1, hg.2.2.2⟩
  · intro p hp
    exact htime p (hsub hp)
  · intro p hp
    exact hguard p (hsub hp)



/-- A complex smooth field admits a local complex smooth flow represented by a pair of real flows. -/
private theorem exists_local_complex_flow_with_real_pair
    (Ω : TopologicalSpace.Opens E) (X : E → E)
    (hX : ContDiffOn ℂ ∞ X Ω) (x : E) (hx : x ∈ Ω) :
    ∃ (A B : Set E) (δ ε : ℝ) (Φ Ψ : E × ℝ → E) (U : Set E) (τ : ℝ),
      (IsOpen A ∧ x ∈ A ∧ A ⊆ Ω ∧ 0 < δ ∧
        ContDiffOn ℝ ∞ Φ (A ×ˢ Ioo (-δ) δ) ∧
        (∀ y ∈ A, Φ (y, 0) = y) ∧
        (∀ p ∈ A ×ˢ Ioo (-δ) δ, Φ p ∈ Ω) ∧
        (∀ p ∈ A ×ˢ Ioo (-δ) δ,
          HasDerivAt (fun s ↦ Φ (p.1, s)) (X (Φ p)) p.2) ∧
        (∀ y ∈ A, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
          s + t ∈ Ioo (-δ) δ → Φ (y, s) ∈ A →
          Φ (Φ (y, s), t) = Φ (y, s + t)) ∧
        (∀ t ∈ Ioo (-δ) δ, DifferentiableOn ℂ (fun y ↦ Φ (y, t)) A)) ∧
      (IsOpen B ∧ x ∈ B ∧ B ⊆ Ω ∧ 0 < ε ∧
        ContDiffOn ℝ ∞ Ψ (B ×ˢ Ioo (-ε) ε) ∧
        (∀ y ∈ B, Ψ (y, 0) = y) ∧
        (∀ p ∈ B ×ˢ Ioo (-ε) ε, Ψ p ∈ Ω) ∧
        (∀ p ∈ B ×ˢ Ioo (-ε) ε,
          HasDerivAt (fun s ↦ Ψ (p.1, s)) (Complex.I • X (Ψ p)) p.2) ∧
        (∀ y ∈ B, ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
          s + t ∈ Ioo (-ε) ε → Ψ (y, s) ∈ B →
          Ψ (Ψ (y, s), t) = Ψ (y, s + t)) ∧
        (∀ t ∈ Ioo (-ε) ε, DifferentiableOn ℂ (fun y ↦ Ψ (y, t)) B)) ∧
      (IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ 0 < τ ∧
        ContDiffOn ℂ ∞ (fun p : E × ℂ ↦ Φ (Ψ (p.1, p.2.im), p.2.re))
          (U ×ˢ Metric.ball 0 τ) ∧
        (∀ y ∈ U, Φ (Ψ (y, 0), 0) = y) ∧
        (∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) τ,
          Φ (Ψ (p.1, p.2.im), p.2.re) ∈ Ω) ∧
        (∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) τ,
          HasDerivAt (fun z : ℂ ↦ Φ (Ψ (p.1, z.im), z.re))
            (X (Φ (Ψ (p.1, p.2.im), p.2.re))) p.2) ∧
        (∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) τ,
          p.1 ∈ B ∧ p.2.im ∈ Ioo (-ε) ε ∧
          Ψ (p.1, p.2.im) ∈ A ∧ p.2.re ∈ Ioo (-δ) δ)) := by
  obtain ⟨A, δ, Φ, hA, hxA, hAΩ, hδ, hΦ, hΦinit, hΦrange, hΦODE, hΦgroup,
    hΦspatial⟩ := exists_spatially_holomorphic_real_flow Ω X hX x hx
  have hIX : ContDiffOn ℂ ∞ (fun y ↦ Complex.I • X y) Ω := hX.const_smul Complex.I
  obtain ⟨B, ε, Ψ, hB, hxB, hBΩ, hε, hΨ, hΨinit, hΨrange, hΨODE, hΨgroup,
    hΨspatial⟩ := exists_spatially_holomorphic_real_flow Ω (fun y ↦ Complex.I • X y) hIX x hx
  obtain ⟨U, τ, hU⟩ := complex_flow_of_real_pair Ω X x A B δ ε Φ Ψ
    hA hxA hAΩ hδ hΦ hΦinit hΦrange hΦODE hΦgroup hΦspatial
    hB hxB hε hΨ hΨinit hΨODE hΨspatial
  exact ⟨A, B, δ, ε, Φ, Ψ, U, τ,
    ⟨hA, hxA, hAΩ, hδ, hΦ, hΦinit, hΦrange, hΦODE, hΦgroup, hΦspatial⟩,
    ⟨hB, hxB, hBΩ, hε, hΨ, hΨinit, hΨrange, hΨODE, hΨgroup, hΨspatial⟩, hU⟩

/-- A complex smooth field on an open domain admits a local complex C∞ flow. -/
private theorem exists_local_complex_flow
    (Ω : TopologicalSpace.Opens E) (X : E → E)
    (hX : ContDiffOn ℂ ∞ X Ω) (x : E) (hx : x ∈ Ω) :
    ∃ (U : Set E) (τ : ℝ) (H : E × ℂ → E),
      IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ 0 < τ ∧
      ContDiffOn ℂ ∞ H (U ×ˢ Metric.ball 0 τ) ∧
      (∀ y ∈ U, H (y, 0) = y) ∧
      (∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) τ, H p ∈ Ω) ∧
      (∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) τ,
        HasDerivAt (fun z : ℂ ↦ H (p.1, z)) (X (H p)) p.2) := by
  obtain ⟨A, B, δ, ε, Φ, Ψ, U, τ, _, _, hU, hxU, hUΩ, hτ, hH, hinit, hrange,
    hODE, _⟩ := exists_local_complex_flow_with_real_pair Ω X hX x hx
  exact ⟨U, τ, (fun p ↦ Φ (Ψ (p.1, p.2.im), p.2.re)),
    hU, hxU, hUΩ, hτ, hH, hinit, hrange, hODE⟩


end ComplexFlowExistence


/-! Real and imaginary flow composition preserves commuting fields. (Lee, Prop 18.5, pp.469–470 and
Thm 19.10, pp.501–502; Teschl, pp.45–47) -/

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.ComplexFlowPreservation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real C² flow satisfying its differential equation satisfies the directional first variational
equation. (Teschl, pp.45–47, Eqs 2.46–2.49) -/
private theorem first_variation_at
    (Φ : E × ℝ → E) (X : E → E) (x : E) (t : ℝ) (v : E)
    (hΦ : ContDiffAt ℝ 2 Φ (x, t))
    (hX : DifferentiableAt ℝ X (Φ (x, t)))
    (hODE : ∀ᶠ z in nhds (x, t), fderiv ℝ Φ z (0, 1) = X (Φ z)) :
    HasDerivAt (fun s ↦ fderiv ℝ Φ (x, s) (v, 0))
      (fderiv ℝ X (Φ (x, t)) (fderiv ℝ Φ (x, t) (v, 0))) t := by
  have hD := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have htime : HasDerivAt (fun s : ℝ ↦ (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hleft := (hD.hasFDerivAt.comp_hasDerivAt t htime).clm_apply
    (hasDerivAt_const t (v, (0 : ℝ)))
  have hpart := hD.hasFDerivAt.clm_apply
    (hasFDerivAt_const (0, (1 : ℝ)) (x, t))
  have hright := hX.hasFDerivAt.comp (x, t) (hΦ.differentiableAt two_ne_zero).hasFDerivAt
  have hEq := (hpart.congr_of_eventuallyEq
    (Filter.Eventually.mono hODE fun _ hz ↦ hz.symm)).unique hright
  have hval := congrArg (fun L : (E × ℝ) →L[ℝ] E ↦ L (v, 0)) hEq
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, ContinuousLinearMap.flip_apply, map_zero, zero_add] at hval
  have hsym := hΦ.isSymmSndFDerivAt (by norm_num)
  simpa only [Function.comp_apply, ContinuousLinearMap.map_zero, add_zero,
    hsym.eq (0, 1) (v, 0), hval] using hleft

/-- A jointly real C² flow satisfies the first variational equation on its open domain. -/
private theorem first_variation_on
    (Φ : E × ℝ → E) (X : E → E) (D : Set (E × ℝ)) (hD : IsOpen D)
    (hΦ : ContDiffOn ℝ 2 Φ D)
    (hX : ∀ z ∈ D, DifferentiableAt ℝ X (Φ z))
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Φ (z.1, s)) (X (Φ z)) z.2)
    (x : E) (t : ℝ) (hxt : (x, t) ∈ D) (v : E) :
    HasDerivAt (fun s ↦ fderiv ℝ Φ (x, s) (v, 0))
      (fderiv ℝ X (Φ (x, t)) (fderiv ℝ Φ (x, t) (v, 0))) t := by
  apply first_variation_at Φ X x t v ((hΦ (x, t) hxt).contDiffAt (hD.mem_nhds hxt))
    (hX (x, t) hxt)
  filter_upwards [hD.mem_nhds hxt] with z hz
  have hd := ((hΦ z hz).contDiffAt (hD.mem_nhds hz)).differentiableAt two_ne_zero
  have htime : HasDerivAt (fun s : ℝ ↦ (z.1, s)) (0, 1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  exact (hd.hasFDerivAt.comp_hasDerivAt z.2 htime).unique (hODE z hz)

/-- The spatial slice derivative is the joint derivative restricted to spatial directions. -/
private theorem spatial_slice_derivative
    (Φ : E × ℝ → E) (U : Set E) (hU : IsOpen U) (a b : ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (U ×ˢ Ioo a b))
    (x : E) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasFDerivAt (fun y ↦ Φ (y, t))
      ((fderiv ℝ Φ (x, t)).comp
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ))) x := by
  exact (((hΦ (x, t) ⟨hx, ht⟩).contDiffAt
    ((hU.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)).differentiableAt two_ne_zero).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))

/-- The spatial derivative of a real flow preserves a commuting vector field. (Lee, Prop 18.5,
pp.469–470; Teschl, pp.45–47) -/
private theorem flow_pushes_commuting_field
    (X Y : E → E) (Ω U : Set E) (hU : IsOpen U)
    (Φ : E × ℝ → E) (a b : ℝ) (hzero : (0 : ℝ) ∈ Ioo a b)
    (hΦ : ContDiffOn ℝ 2 Φ (U ×ˢ Ioo a b))
    (hinit : ∀ x ∈ U, Φ (x, 0) = x)
    (hrange : ∀ z ∈ U ×ˢ Ioo a b, Φ z ∈ Ω)
    (hX : ∀ z ∈ Ω, DifferentiableAt ℝ X z)
    (hY : ∀ z ∈ Ω, DifferentiableAt ℝ Y z)
    (hbracket : ∀ z ∈ Ω, VectorField.lieBracket ℝ X Y z = 0)
    (hODE : ∀ z ∈ U ×ˢ Ioo a b,
      HasDerivAt (fun s ↦ Φ (z.1, s)) (X (Φ z)) z.2)
    (K : NNReal)
    (hbound : ∀ z ∈ U ×ˢ Ioo a b, ‖fderiv ℝ X (Φ z)‖ ≤ K)
    (x : E) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo a b) :
    fderiv ℝ (fun y ↦ Φ (y, t)) x (Y x) = Y (Φ (x, t)) := by
  let L : ℝ → E →L[ℝ] E := fun s ↦ (fderiv ℝ Φ (x, s)).comp
    ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ))
  have hLzero : L 0 = ContinuousLinearMap.id ℝ E := by
    apply (HasFDerivAt.congr_of_eventuallyEq
      (spatial_slice_derivative Φ U hU a b hΦ x hx 0 hzero) ?_).unique
        (hasFDerivAt_id x)
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hinit y hy).symm
  have hvar (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun q ↦ L q (Y x))
        (fderiv ℝ X (Φ (x, s)) (L s (Y x))) s := by
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply] using
        first_variation_on Φ X (U ×ˢ Ioo a b) (hU.prod isOpen_Ioo) hΦ
          (fun z hz ↦ hX (Φ z) (hrange z hz)) hODE x s ⟨hx, hs⟩ (Y x)
  have htransport (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun q ↦ Y (Φ (x, q)))
        (fderiv ℝ X (Φ (x, s)) (Y (Φ (x, s)))) s := by
    have heq : fderiv ℝ Y (Φ (x, s)) (X (Φ (x, s))) =
        fderiv ℝ X (Φ (x, s)) (Y (Φ (x, s))) :=
      sub_eq_zero.mp (hbracket _ (hrange (x, s) ⟨hx, hs⟩))
    simpa only [heq, Function.comp_def] using
      (hY _ (hrange (x, s) ⟨hx, hs⟩)).hasFDerivAt.comp_hasDerivAt s
      (hODE (x, s) ⟨hx, hs⟩)
  have heq := ODE_solution_unique_of_mem_Ioo
    (v := fun s (v : E) ↦ fderiv ℝ X (Φ (x, s)) v)
    (s := fun _ ↦ (univ : Set E)) (K := K)
    (f := fun s ↦ L s (Y x)) (g := fun s ↦ Y (Φ (x, s)))
    (fun s hs ↦ ((fderiv ℝ X (Φ (x, s))).lipschitzWith.weaken
      (hbound (x, s) ⟨hx, hs⟩)).lipschitzOnWith) hzero
    (fun s hs ↦ ⟨hvar s hs, mem_univ _⟩)
    (fun s hs ↦ ⟨htransport s hs, mem_univ _⟩)
    (by simp [hLzero, hinit x hx])
  rw [(spatial_slice_derivative Φ U hU a b hΦ x hx t ht).fderiv]
  exact heq ht


section Complex
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Real flow data on an open rectangle, with a bounded variational coefficient along trajectories
and holomorphic spatial slices. -/
private structure RealFlowOn (X : E → E) (Ω U : Set E) (a b : ℝ) (Φ : E × ℝ → E) : Prop where
  open_initial : IsOpen U
  zero_time : (0 : ℝ) ∈ Ioo a b
  smooth : ContDiffOn ℝ 2 Φ (U ×ˢ Ioo a b)
  initial : ∀ x ∈ U, Φ (x, 0) = x
  image : ∀ p ∈ U ×ˢ Ioo a b, Φ p ∈ Ω
  field : ∀ x ∈ Ω, DifferentiableAt ℝ X x
  equation : ∀ p ∈ U ×ˢ Ioo a b,
    HasDerivAt (fun t ↦ Φ (p.1, t)) (X (Φ p)) p.2
  bounded_coefficient : ∃ K : NNReal, ∀ p ∈ U ×ˢ Ioo a b,
    ‖fderiv ℝ X (Φ p)‖ ≤ K
  spatial : ∀ p ∈ U ×ˢ Ioo a b, DifferentiableAt ℂ (fun y ↦ Φ (y, p.2)) p.1

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- Continuity gives a local uniform bound for the real variational coefficient. -/
private theorem exists_real_coefficient_bound
    (A : E × ℝ → E →L[ℝ] E) (x : E) (hA : ContinuousAt A (x, 0))
    (U : Set E) (hU : IsOpen U) (hx : x ∈ U) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (V : Set E) (τ : ℝ) (K : NNReal),
      IsOpen V ∧ x ∈ V ∧ 0 < τ ∧ V ⊆ U ∧ τ ≤ δ ∧
      ∀ z ∈ V ×ˢ Ioo (-τ) τ, ‖A z‖ ≤ K := by
  have hnorm : ∀ᶠ z in nhds (x, (0 : ℝ)), ‖A z‖ < ‖A (x, 0)‖ + 1 :=
    hA.norm.eventually (Iio_mem_nhds (lt_add_one _))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnorm
  refine ⟨U ∩ Metric.ball x r, min r δ,
    ⟨‖A (x, 0)‖ + 1, by positivity⟩, hU.inter Metric.isOpen_ball,
    ⟨hx, Metric.mem_ball_self hr⟩, lt_min hr hδ, inter_subset_left, min_le_right _ _, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.ball (x, (0 : ℝ)) r := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨hz.1.2, ?_⟩
    simpa only [Real.dist_eq, sub_zero, abs_lt] using
      (show -r < z.2 ∧ z.2 < r from
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_left r δ)) hz.2.1,
          lt_of_lt_of_le hz.2.2 (min_le_left r δ)⟩)
  exact (hball hzball).le

omit [IsScalarTower ℝ ℂ E] in
/-- A real flow with holomorphic spatial slices can be restricted to a rectangle with bounded
variational coefficient. -/
private theorem exists_realFlowOn
    {X : E → E} {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hX : ContDiffOn ℝ 2 X Ω) {Φ : E × ℝ → E} {δ : ℝ} (hδ : 0 < δ)
    (hΦ : ContDiffOn ℝ 2 Φ (U ×ˢ Ioo (-δ) δ))
    (hinit : ∀ y ∈ U, Φ (y, 0) = y)
    (hrange : ∀ p ∈ U ×ˢ Ioo (-δ) δ, Φ p ∈ Ω)
    (hODE : ∀ p ∈ U ×ˢ Ioo (-δ) δ,
      HasDerivAt (fun t ↦ Φ (p.1, t)) (X (Φ p)) p.2)
    (hspatial : ∀ p ∈ U ×ˢ Ioo (-δ) δ,
      DifferentiableAt ℂ (fun y ↦ Φ (y, p.2)) p.1)
    {x : E} (hx : x ∈ U) :
    ∃ V τ, x ∈ V ∧ 0 < τ ∧ V ⊆ U ∧ τ ≤ δ ∧ RealFlowOn X Ω V (-τ) τ Φ := by
  have hz : (x, (0 : ℝ)) ∈ U ×ˢ Ioo (-δ) δ :=
    ⟨hx, neg_lt_zero.mpr hδ, hδ⟩
  have hc : ContinuousAt (fun p ↦ fderiv ℝ X (Φ p)) (x, (0 : ℝ)) :=
    ((hX.contDiffAt (hΩ.mem_nhds (hrange _ hz))).continuousAt_fderiv two_ne_zero).comp
      (hΦ.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hz)).continuousAt
  obtain ⟨V, τ, K, hV, hxV, hτ, hVU, hτδ, hbound⟩ :=
    exists_real_coefficient_bound (fun p ↦ fderiv ℝ X (Φ p)) x hc U hU hx δ hδ
  have hsub : V ×ˢ Ioo (-τ) τ ⊆ U ×ˢ Ioo (-δ) δ := by
    intro p hp
    exact ⟨hVU hp.1, lt_of_le_of_lt (neg_le_neg hτδ) hp.2.1,
      lt_of_lt_of_le hp.2.2 hτδ⟩
  refine ⟨V, τ, hxV, hτ, hVU, hτδ, hV, ⟨neg_lt_zero.mpr hτ, hτ⟩,
    hΦ.mono hsub, (fun y hy ↦ hinit y (hVU hy)),
    (fun p hp ↦ hrange p (hsub hp)), ?_,
    (fun p hp ↦ hODE p (hsub hp)), ⟨K, hbound⟩,
    (fun p hp ↦ hspatial p (hsub hp))⟩
  intro y hy
  exact (hX.contDiffAt (hΩ.mem_nhds hy)).differentiableAt two_ne_zero

/-- The composition of two real flows using imaginary and real parts of complex time. -/
private def composedFlow (Φ Ψ : E × ℝ → E) (p : ℂ × E) : E :=
  Φ (Ψ (p.2, p.1.im), p.1.re)

/-- The domain where both real times lie in their intervals and the intermediate image lies in the
receiving flow's initial domain. -/
private def receivingDomain (Ψ : E × ℝ → E) (U V : Set E) (a b c d : ℝ) : Set (ℂ × E) :=
  {p | p.2 ∈ V ∧ p.1.im ∈ Ioo c d ∧ Ψ (p.2, p.1.im) ∈ U ∧ p.1.re ∈ Ioo a b}

/-- Real flow preservation implies preservation by the complex derivative of the spatial slice. -/
private theorem realFlow_preserves_complex
    {X Y : E → E} {Ω U : Set E} {a b : ℝ} {Φ : E × ℝ → E}
    (hΦ : RealFlowOn X Ω U a b Φ)
    (hY : ∀ x ∈ Ω, DifferentiableAt ℝ Y x)
    (hbracket : ∀ x ∈ Ω, VectorField.lieBracket ℝ X Y x = 0)
    {x : E} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo a b) :
    fderiv ℂ (fun y ↦ Φ (y, t)) x (Y x) = Y (Φ (x, t)) := by
  obtain ⟨K, hK⟩ := hΦ.bounded_coefficient
  have hreal := flow_pushes_commuting_field X Y Ω U hΦ.open_initial Φ a b hΦ.zero_time
    hΦ.smooth hΦ.initial hΦ.image hΦ.field hY hbracket hΦ.equation K hK x hx t ht
  rw [(hΦ.spatial (x, t) ⟨hx, ht⟩).fderiv_restrictScalars ℝ] at hreal
  exact hreal

/-- The composition of real flows of `X` and `iX` preserves a field commuting with both. -/
private theorem composedFlow_preserves
    {X Y : E → E} {Ω U V : Set E} {a b c d : ℝ} {Φ Ψ : E × ℝ → E}
    (hΦ : RealFlowOn X Ω U a b Φ)
    (hΨ : RealFlowOn (fun x ↦ Complex.I • X x) Ω V c d Ψ)
    (hY : ∀ x ∈ Ω, DifferentiableAt ℝ Y x)
    (hbracket : ∀ x ∈ Ω, VectorField.lieBracket ℝ X Y x = 0)
    (hibracket : ∀ x ∈ Ω,
      VectorField.lieBracket ℝ (fun y ↦ Complex.I • X y) Y x = 0)
    {p : ℂ × E} (hp : p ∈ receivingDomain Ψ U V a b c d) :
    fderiv ℂ (fun y ↦ composedFlow Φ Ψ (p.1, y)) p.2 (Y p.2) =
      Y (composedFlow Φ Ψ p) := by
  obtain ⟨hx, ht, hreceive, hs⟩ := hp
  have hψ := hΨ.spatial (p.2, p.1.im) ⟨hx, ht⟩
  have hφ := hΦ.spatial (Ψ (p.2, p.1.im), p.1.re) ⟨hreceive, hs⟩
  have hd := hφ.hasFDerivAt.comp p.2 hψ.hasFDerivAt
  rw [show fderiv ℂ (fun y ↦ composedFlow Φ Ψ (p.1, y)) p.2 =
    (fderiv ℂ (fun y ↦ Φ (y, p.1.re)) (Ψ (p.2, p.1.im))).comp
      (fderiv ℂ (fun y ↦ Ψ (y, p.1.im)) p.2) from hd.fderiv]
  change fderiv ℂ (fun y ↦ Φ (y, p.1.re)) (Ψ (p.2, p.1.im))
    (fderiv ℂ (fun y ↦ Ψ (y, p.1.im)) p.2 (Y p.2)) = _
  rw [realFlow_preserves_complex hΨ hY hibracket hx ht,
    realFlow_preserves_complex hΦ hY hbracket hreceive hs]
  rfl

omit [IsScalarTower ℝ ℂ E] in
/-- The receiving domain is open. -/
private theorem receivingDomain_isOpen
    {X : E → E} {Ω U V : Set E} {a b c d : ℝ} {Φ Ψ : E × ℝ → E}
    (hΦ : RealFlowOn X Ω U a b Φ)
    (hΨ : RealFlowOn (fun x ↦ Complex.I • X x) Ω V c d Ψ) :
    IsOpen (receivingDomain Ψ U V a b c d) := by
  have hq : Continuous (fun p : ℂ × E ↦ (p.2, p.1.im)) :=
    continuous_snd.prodMk (Complex.continuous_im.comp continuous_fst)
  have hg : ContinuousOn (fun p : ℂ × E ↦ Ψ (p.2, p.1.im))
      ((fun p : ℂ × E ↦ (p.2, p.1.im)) ⁻¹' (V ×ˢ Ioo c d)) :=
    hΨ.smooth.continuousOn.comp hq.continuousOn (fun _ h ↦ h)
  have ho := hg.isOpen_inter_preimage
    ((hΨ.open_initial.prod isOpen_Ioo).preimage hq) hΦ.open_initial
  have hr : IsOpen ((fun p : ℂ × E ↦ p.1.re) ⁻¹' Ioo a b) :=
    isOpen_Ioo.preimage (Complex.continuous_re.comp
    (continuous_fst : Continuous (fun p : ℂ × E ↦ p.1)))
  convert ho.inter hr using 1
  ext p
  simp only [receivingDomain, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod]
  tauto

omit [IsScalarTower ℝ ℂ E] in
/-- The receiving domain contains a product neighborhood of the base point at zero time. -/
private theorem exists_receiving_product
    {X : E → E} {Ω U V : Set E} {a b c d : ℝ} {Φ Ψ : E × ℝ → E}
    (hΦ : RealFlowOn X Ω U a b Φ)
    (hΨ : RealFlowOn (fun x ↦ Complex.I • X x) Ω V c d Ψ)
    {x : E} (hxU : x ∈ U) (hxV : x ∈ V) :
    ∃ O : Set ℂ, ∃ W : Set E, IsOpen O ∧ 0 ∈ O ∧ IsOpen W ∧ x ∈ W ∧
      O ×ˢ W ⊆ receivingDomain Ψ U V a b c d := by
  apply mem_nhds_prod_iff'.mp
  apply (receivingDomain_isOpen hΦ hΨ).mem_nhds
  refine ⟨hxV, ?_, ?_, ?_⟩
  · simpa using hΨ.zero_time
  · simpa only [Complex.zero_im, hΨ.initial x hxV] using hxU
  · simpa using hΦ.zero_time

/-- Each composed real flow preserves the fields with distinct indices in a commuting normalized family. -/
private theorem family_composedFlow_preserves {ι : Type*}
    (X : ι → E → E) (Ω : Set E) (U V : ι → Set E)
    (a b c d : ι → ℝ) (Φ Ψ : ι → E × ℝ → E)
    (hΦ : ∀ i, RealFlowOn (X i) Ω (U i) (a i) (b i) (Φ i))
    (hΨ : ∀ i, RealFlowOn (fun x ↦ Complex.I • X i x) Ω (V i) (c i) (d i) (Ψ i))
    (hbracket : ∀ i j, i ≠ j → ∀ x ∈ Ω,
      VectorField.lieBracket ℝ (X i) (X j) x = 0)
    (hibracket : ∀ i j, i ≠ j → ∀ x ∈ Ω,
      VectorField.lieBracket ℝ (fun y ↦ Complex.I • X i y) (X j) x = 0) :
    ∀ i j, i ≠ j → ∀ p ∈ receivingDomain (Ψ i) (U i) (V i) (a i) (b i) (c i) (d i),
      fderiv ℂ (fun y ↦ composedFlow (Φ i) (Ψ i) (p.1, y)) p.2 (X j p.2) =
        X j (composedFlow (Φ i) (Ψ i) p) := by
  intro i j hij p hp
  exact composedFlow_preserves (hΦ i) (hΨ i) (hΦ j).field
    (hbracket i j hij) (hibracket i j hij) hp

omit [IsScalarTower ℝ ℂ E] in
/-- A finite family of flows has a common open receiving domain. -/
private theorem finite_family_receiving_domain {ι : Type*} [Fintype ι]
    (X : ι → E → E) (Ω : Set E) (U V : ι → Set E)
    (a b c d : ι → ℝ) (Φ Ψ : ι → E × ℝ → E)
    (hΦ : ∀ i, RealFlowOn (X i) Ω (U i) (a i) (b i) (Φ i))
    (hΨ : ∀ i, RealFlowOn (fun x ↦ Complex.I • X i x) Ω (V i) (c i) (d i) (Ψ i))
    {x : E} (hxU : ∀ i, x ∈ U i) (hxV : ∀ i, x ∈ V i) :
    ∃ O : Set ℂ, ∃ W : Set E, IsOpen O ∧ 0 ∈ O ∧ IsOpen W ∧ x ∈ W ∧
      ∀ i, O ×ˢ W ⊆ receivingDomain (Ψ i) (U i) (V i) (a i) (b i) (c i) (d i) := by
  have hopen : IsOpen (⋂ i, receivingDomain (Ψ i) (U i) (V i)
      (a i) (b i) (c i) (d i)) := isOpen_iInter_of_finite
        (fun i ↦ receivingDomain_isOpen (hΦ i) (hΨ i))
  have hx : (0, x) ∈ ⋂ i, receivingDomain (Ψ i) (U i) (V i)
      (a i) (b i) (c i) (d i) := by
    simp only [mem_iInter]
    intro i
    refine ⟨hxV i, ?_, ?_, ?_⟩
    · simpa using (hΨ i).zero_time
    · simpa only [Complex.zero_im, (hΨ i).initial x (hxV i)] using hxU i
    · simpa using (hΦ i).zero_time
  obtain ⟨O, W, hO, h0, hW, hxW, hsub⟩ := mem_nhds_prod_iff'.mp (hopen.mem_nhds hx)
  refine ⟨O, W, hO, h0, hW, hxW, ?_⟩
  intro i p hp
  exact mem_iInter.mp (hsub hp) i

/-- A finite commuting frame admits a common product neighborhood on which each composed flow
preserves the other frame fields. -/
private theorem exists_common_preserving_product {ι : Type*} [Fintype ι]
    (X : ι → E → E) (Ω : Set E) (U V : ι → Set E)
    (a b c d : ι → ℝ) (Φ Ψ : ι → E × ℝ → E)
    (hΦ : ∀ i, RealFlowOn (X i) Ω (U i) (a i) (b i) (Φ i))
    (hΨ : ∀ i, RealFlowOn (fun x ↦ Complex.I • X i x) Ω (V i) (c i) (d i) (Ψ i))
    (hbracket : ∀ i j, i ≠ j → ∀ x ∈ Ω,
      VectorField.lieBracket ℝ (X i) (X j) x = 0)
    (hibracket : ∀ i j, i ≠ j → ∀ x ∈ Ω,
      VectorField.lieBracket ℝ (fun y ↦ Complex.I • X i y) (X j) x = 0)
    {x : E} (hxU : ∀ i, x ∈ U i) (hxV : ∀ i, x ∈ V i) :
    ∃ O : Set ℂ, ∃ W : Set E, IsOpen O ∧ 0 ∈ O ∧ IsOpen W ∧ x ∈ W ∧
      (∀ i, O ×ˢ W ⊆ receivingDomain (Ψ i) (U i) (V i)
        (a i) (b i) (c i) (d i)) ∧
      ∀ i j, i ≠ j → ∀ p ∈ O ×ˢ W,
        fderiv ℂ (fun y ↦ composedFlow (Φ i) (Ψ i) (p.1, y)) p.2 (X j p.2) =
          X j (composedFlow (Φ i) (Ψ i) p) := by
  obtain ⟨O, W, hO, h0, hW, hxW, hguards⟩ :=
    finite_family_receiving_domain X Ω U V a b c d Φ Ψ hΦ hΨ hxU hxV
  refine ⟨O, W, hO, h0, hW, hxW, hguards, ?_⟩
  intro i j hij p hp
  exact family_composedFlow_preserves X Ω U V a b c d Φ Ψ hΦ hΨ
    hbracket hibracket i j hij p (hguards i hp)

end Complex


end HolomorphicAnosov.ComplexFlowPreservation

namespace HolomorphicAnosov.Theorem12NativeHolomorphicBoxes

open Set Filter
open scoped Topology _root_.Topology ContDiff Manifold
open Theorem12FrobeniusLocalAssembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A finite commuting normalized frame admits complex smooth flows preserving the other frame
fields on open receiving domains. -/
theorem exists_preserving_complex_frame_flows {r : ℕ}
    (Ω : Set E) (hΩ : IsOpen Ω) (x : E) (hx : x ∈ Ω)
    (N : E → (Fin r → ℂ) →L[ℂ] E) (hN : ContDiffOn ℂ ∞ N Ω)
    (hcommute : ∀ z ∈ Ω, ∀ v w, VectorField.lieBracket ℂ
      (fun y ↦ N y v) (fun y ↦ N y w) z = 0) :
    ∃ (flow : Fin r → ℂ × E → E) (domain : Fin r → Set (ℂ × E)),
      (∀ i, IsOpen (domain i)) ∧ (∀ i, (0, x) ∈ domain i) ∧
      (∀ i, ContDiffOn ℂ ∞ (flow i) (domain i)) ∧
      (∀ i y, (0, y) ∈ domain i → flow i (0, y) = y) ∧
      (∀ i q, q ∈ domain i → flow i q ∈ Ω) ∧
      (∀ i q, q ∈ domain i →
        HasDerivAt (fun t ↦ flow i (t, q.2))
          (N (flow i q) (Pi.single i 1)) q.1) ∧
      (∀ i j, i ≠ j → ∀ q, q ∈ domain i →
        fderiv ℂ (fun y ↦ flow i (q.1, y)) q.2 (N q.2 (Pi.single j 1)) =
          N (flow i q) (Pi.single j 1)) := by
  classical
  let X : Fin r → E → E := fun i y ↦ N y (Pi.single i 1)
  have hX (i : Fin r) : ContDiffOn ℂ ∞ (X i) Ω := hN.clm_apply contDiffOn_const
  have hpairs := fun i : Fin r ↦
    ComplexFlowExistence.exists_local_complex_flow_with_real_pair
      ⟨Ω, hΩ⟩ (X i) (hX i) x hx
  choose A B δ ε Φ Ψ U τ hΦ hΨ hH using hpairs
  have hreal (i : Fin r) := ComplexFlowPreservation.exists_realFlowOn hΩ (hΦ i).1
    ((hX i).restrict_scalars ℝ |>.of_le (by simp)) (hΦ i).2.2.2.1
    ((hΦ i).2.2.2.2.1.of_le (by simp)) (hΦ i).2.2.2.2.2.1
    (hΦ i).2.2.2.2.2.2.1 (hΦ i).2.2.2.2.2.2.2.1
    (fun p hp ↦ ((hΦ i).2.2.2.2.2.2.2.2.2 p.2 hp.2).differentiableAt
      ((hΦ i).1.mem_nhds hp.1)) (hΦ i).2.1
  have himag (i : Fin r) := ComplexFlowPreservation.exists_realFlowOn hΩ (hΨ i).1
    (((hX i).const_smul Complex.I).restrict_scalars ℝ |>.of_le (by simp))
    (hΨ i).2.2.2.1 ((hΨ i).2.2.2.2.1.of_le (by simp)) (hΨ i).2.2.2.2.2.1
    (hΨ i).2.2.2.2.2.2.1 (hΨ i).2.2.2.2.2.2.2.1
    (fun p hp ↦ ((hΨ i).2.2.2.2.2.2.2.2.2 p.2 hp.2).differentiableAt
      ((hΨ i).1.mem_nhds hp.1)) (hΨ i).2.1
  choose A' δ' hxA' hδ' hA'A hδ'δ hreal' using hreal
  choose B' ε' hxB' hε' hB'B hε'ε himag' using himag
  have hRealComm (v w : Fin r → ℂ) (y : E) (hy : y ∈ Ω) :
      VectorField.lieBracket ℝ (fun z ↦ N z v) (fun z ↦ N z w) y = 0 := by
    have hv : ContDiffOn ℂ ∞ (fun z ↦ N z v) Ω := hN.clm_apply contDiffOn_const
    have hw : ContDiffOn ℂ ∞ (fun z ↦ N z w) Ω := hN.clm_apply contDiffOn_const
    rw [Theorem12NormalizedFrame.real_lieBracket_eq_complex
      ((hv.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hw.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))]
    exact hcommute y hy v w
  have hbracket (i j : Fin r) (_ : i ≠ j) (y : E) (hy : y ∈ Ω) :
      VectorField.lieBracket ℝ (X i) (X j) y = 0 := by
    exact hRealComm (Pi.single i 1) (Pi.single j 1) y hy
  have hibracket (i j : Fin r) (_ : i ≠ j) (y : E) (hy : y ∈ Ω) :
      VectorField.lieBracket ℝ (fun z ↦ Complex.I • X i z) (X j) y = 0 := by
    have heq : (fun z ↦ N z (Complex.I • Pi.single i 1)) =
        (fun z ↦ Complex.I • X i z) := by
      funext z
      exact (N z).map_smul Complex.I (Pi.single i 1)
    rw [← heq]
    exact hRealComm (Complex.I • Pi.single i 1) (Pi.single j 1) y hy
  obtain ⟨O, W, hO, h0O, hW, hxW, hguards, hpreserve⟩ :=
    ComplexFlowPreservation.exists_common_preserving_product X Ω A' B'
      (fun i ↦ -δ' i) δ' (fun i ↦ -ε' i) ε' Φ Ψ hreal' himag'
      hbracket hibracket hxA' hxB'
  let domain : Fin r → Set (ℂ × E) := fun i ↦
    (O ×ˢ W) ∩ (Metric.ball 0 (τ i) ×ˢ U i)
  let flow : Fin r → ℂ × E → E := fun i q ↦ Φ i (Ψ i (q.2, q.1.im), q.1.re)
  refine ⟨flow, domain, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hO.prod hW).inter (Metric.isOpen_ball.prod (hH i).1)
  · intro i
    exact ⟨⟨h0O, hxW⟩, Metric.mem_ball_self (hH i).2.2.2.1, (hH i).2.1⟩
  · intro i
    exact (hH i).2.2.2.2.1.comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun q hq ↦ ⟨hq.2.2, hq.2.1⟩)
  · intro i y hy
    exact (hH i).2.2.2.2.2.1 y hy.2.2
  · intro i q hq
    exact (hH i).2.2.2.2.2.2.1 (q.2, q.1) ⟨hq.2.2, hq.2.1⟩
  · intro i q hq
    exact (hH i).2.2.2.2.2.2.2.1 (q.2, q.1) ⟨hq.2.2, hq.2.1⟩
  · intro i j hij q hq
    exact hpreserve i j hij q hq.1

end HolomorphicAnosov.Theorem12NativeHolomorphicBoxes


namespace HolomorphicAnosov.Theorem12NativeHolomorphicBoxes

open Set Filter
open scoped Topology _root_.Topology ContDiff Manifold
open Theorem12FrobeniusLocalAssembly
attribute [local instance] complex_isManifold_real

variable {d r c : ℕ} {X : Type*} [MetricSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- A holomorphic subbundle with native leaves admits a unit product box flattening its tangent
distribution. -/
private theorem exists_native_holomorphic_unit_box
    (f : X ≃ₜ X)
    (P R : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P) (hR : IsHolomorphicTangentSubbundle c R)
    (hcompl : ∀ q, IsCompl (P q) (R q))
    (Q T : RealTangentDistribution (realModel d) X)
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (hRealR : ∀ q, ((R q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = T q)
    (DP : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (DR : ∀ b, NativeAsymptoticLeafDatum (realModel d) f.symm T b) (x : X) :
    ∃ b : OpenPartialHomeomorph X (ComplexModel r × ComplexModel c),
      x ∈ b.source ∧
      b.target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)) ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) ∞ b b.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel c) (complexModel d) ∞ b.symm b.target ∧
      (∀ q ∈ b.source,
        (P q).map (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c) b q).toLinearMap =
          LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap) := by
  obtain ⟨V, S, U, hV, hxV, hVt, hS, hU, hSi, hUi, hSr, hUr, hSU, hSc, hUc⟩ :=
    exists_native_complementary_commuting_frames f P R hP hR hcompl Q T
      hRealP hRealR DP DR x
  obtain ⟨flow, domain, hopen, hmem, hsmooth, hzero, hrange, hODE, hpreserve⟩ :=
    exists_preserving_complex_frame_flows V hV _ hxV S hS hSc
  let k := chartAt (ComplexModel d) x
  obtain ⟨b, hxb, hsource, htarget, hb, hbi, hflat⟩ :=
    exists_unit_box_from_native_flow_data P k
      (contMDiffOn_chart (n := ∞) (I := complexModel d))
      (contMDiffOn_chart_symm (n := ∞) (I := complexModel d) (x := x))
      x (mem_chart_source (ComplexModel d) x) V hV hxV S hSr
      (U (k x)) (hSi _ hxV) (hUi _ hxV) (hSU _ hxV)
      flow domain hopen hmem hsmooth hzero hODE hpreserve
  exact ⟨b, hxb, htarget, hb, hbi, hflat⟩

/-- The native holomorphic unit boxes form a cover of the manifold. -/
private theorem exists_native_holomorphic_unit_box_cover
    (f : X ≃ₜ X)
    (P R : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P) (hR : IsHolomorphicTangentSubbundle c R)
    (hcompl : ∀ q, IsCompl (P q) (R q))
    (Q T : RealTangentDistribution (realModel d) X)
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (hRealR : ∀ q, ((R q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = T q)
    (DP : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (DR : ∀ b, NativeAsymptoticLeafDatum (realModel d) f.symm T b) :
    ∃ box : X → OpenPartialHomeomorph X (ComplexModel r × ComplexModel c),
      (∀ x, x ∈ (box x).source) ∧
      (∀ x, (box x).target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c))) ∧
      (∀ x, ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c)
        ∞ (box x) (box x).source) ∧
      (∀ x, ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel c) (complexModel d)
        ∞ (box x).symm (box x).target) ∧
      (∀ x q, q ∈ (box x).source →
        (P q).map (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c)
          (box x) q).toLinearMap =
          LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap) := by
  classical
  have h := fun x ↦ exists_native_holomorphic_unit_box f P R hP hR hcompl Q T
    hRealP hRealR DP DR x
  choose box hx ht hb hbi hf using h
  exact ⟨box, hx, ht, hb, hbi, hf⟩

end HolomorphicAnosov.Theorem12NativeHolomorphicBoxes


namespace HolomorphicAnosov.Theorem12NativeHolomorphicBoxes

open Set Filter
open scoped Topology _root_.Topology ContDiff Manifold
open Theorem12FrobeniusLocalAssembly
attribute [local instance] complex_isManifold_real

variable {d r c : ℕ} {X : Type*} [MetricSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Complementary rank-`r` and rank-`c` subbundles at a point satisfy `r + c = d`. -/
private theorem native_complementary_rank_add
    (f : X ≃ₜ X)
    (P R : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P) (hR : IsHolomorphicTangentSubbundle c R)
    (hcompl : ∀ q, IsCompl (P q) (R q))
    (Q T : RealTangentDistribution (realModel d) X)
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (hRealR : ∀ q, ((R q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = T q)
    (DP : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (DR : ∀ b, NativeAsymptoticLeafDatum (realModel d) f.symm T b) (x : X) :
    d = r + c := by
  obtain ⟨V, S, U, hV, hxV, hVt, hS, hU, hSi, hUi, hSr, hUr, hSU, hSc, hUc⟩ :=
    exists_native_complementary_commuting_frames f P R hP hR hcompl Q T
      hRealP hRealR DP DR x
  have h := Submodule.finrank_add_eq_of_isCompl (hSU _ hxV)
  rw [LinearMap.finrank_range_of_inj (hSi _ hxV),
    LinearMap.finrank_range_of_inj (hUi _ hxV)] at h
  simpa [ComplexModel] using h.symm

/-- Native leaves and complementary holomorphic bundles give a flattening unit-box cover in the
complex product model. -/
private theorem exists_native_holomorphic_unit_box_cover_product_model
    (f : X ≃ₜ X)
    (P R : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P) (hR : IsHolomorphicTangentSubbundle c R)
    (hcompl : ∀ q, IsCompl (P q) (R q))
    (Q T : RealTangentDistribution (realModel d) X)
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (hRealR : ∀ q, ((R q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = T q)
    (DP : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (DR : ∀ b, NativeAsymptoticLeafDatum (realModel d) f.symm T b) :
    ∃ box : X → OpenPartialHomeomorph X (ComplexModel r × ComplexModel c),
      (∀ x, x ∈ (box x).source) ∧
      (∀ x, (box x).target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c))) ∧
      (∀ x, ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
        ∞ (box x) (box x).source) ∧
      (∀ x, ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
        ∞ (box x).symm (box x).target) ∧
      (∀ x q, q ∈ (box x).source →
        (P q).map (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
          (box x) q).toLinearMap =
          LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap) := by
  obtain ⟨box, hx, ht, hb, hbi, hf⟩ := exists_native_holomorphic_unit_box_cover
    f P R hP hR hcompl Q T hRealP hRealR DP DR
  refine ⟨box, hx, ht, ?_, ?_, ?_⟩
  · simp_rw +instances [complexModel, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    simpa only [complexModel] using hb
  · simp_rw +instances [complexModel, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    simpa only [complexModel] using hbi
  · intro x q hq
    have hqf := hf x q hq
    have hm : mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
        (box x) q = mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel c)
        (box x) q := by
      unfold complexModel
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    erw [hm]
    exact hqf

end HolomorphicAnosov.Theorem12NativeHolomorphicBoxes


/-! Holomorphic covering sheets lift downstairs boxes to holomorphic unit product boxes. -/

namespace HolomorphicAnosov.Theorem12CoverBoxes

open Theorem12UnitProductBox
open Set Filter
open scoped Topology _root_.Topology ContDiff Manifold

universe u v w

variable {d r c : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]

/-- Each point of a holomorphic covering admits a unit product box in one sheet projecting to an
affine restriction of a downstairs box. -/
private theorem exists_lifted_unit_box
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (hsheets : ∀ y : Y, ∃ s : OpenPartialHomeomorph Y X,
      y ∈ s.source ∧ EqOn s p s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target)
    (y : Y) :
    ∃ (i : F.boxIndex) (s : OpenPartialHomeomorph Y X) (ρ : ℝ) (hρ : 0 < ρ),
      let a := F.box i (p y)
      let e := s.trans (F.box i)
      let b := unitSubchart e a ρ hρ
      let b₀ := unitSubchart (F.box i) a ρ hρ
      y ∈ b.source ∧ b.source ⊆ s.source ∧ EqOn s p s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target ∧
      b.source = s.source ∩ s ⁻¹' b₀.source ∧
      b.target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)) ∧
      b₀.target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)) ∧
      b₀.source ⊆ s.target ∧ b₀.source ⊆ (F.box i).source ∧
      ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c)) ∞ b b.source ∧
      ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d) ∞ b.symm b.target ∧
      (∀ z, b.symm z = s.symm (b₀.symm z)) ∧
      (∀ z ∈ b.target, p (b.symm z) = b₀.symm z) ∧
      (∀ q ∈ b.source, b q = b₀ (p q)) ∧
      (∀ q q', (b q).2 = (b q').2 ↔
        (F.box i (s q)).2 = (F.box i (s q')).2) ∧
      (blockAffine a ρ hρ).symm '' unitProduct ⊆ e.target := by
  obtain ⟨s, hy, hsp, hs, hsi⟩ := hsheets y
  obtain ⟨i, hi⟩ := F.cover (p y)
  let e := s.trans (F.box i)
  have hye : y ∈ e.source := by
    change y ∈ s.source ∧ s y ∈ (F.box i).source
    refine ⟨hy, ?_⟩
    rw [hsp hy]
    exact hi
  have he : ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ e e.source := by
    apply (F.box_holomorphic i).comp (hs.mono inter_subset_left)
    exact fun q hq ↦ hq.2
  have hei : ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ e.symm e.target := by
    apply hsi.comp ((F.box_inverse_holomorphic i).mono inter_subset_left)
    exact fun z hz ↦ hz.2
  obtain ⟨ρ, hρ, hsub⟩ := exists_blockAffine_unit_subset e.target e.open_target
    (e y) (e.map_source hye)
  have ha : e y = F.box i (p y) := by
    change F.box i (s y) = F.box i (p y)
    rw [hsp hy]
  let a := F.box i (p y)
  have hsub' : (blockAffine a ρ hρ).symm '' unitProduct ⊆ e.target := by
    simpa only [a, ha, unitProduct] using hsub
  have hsub₀ : (blockAffine a ρ hρ).symm '' unitProduct ⊆ (F.box i).target :=
    fun z hz ↦ (hsub' hz).1
  have hbhol :
      ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c)) ∞
        (unitSubchart e a ρ hρ) (unitSubchart e a ρ hρ).source ∧
      ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d) ∞
        (unitSubchart e a ρ hρ).symm (unitSubchart e a ρ hρ).target := by
    simp_rw +instances [complexModel, ← modelWithCornersSelf_prod,
      chartedSpaceSelf_prod] at he hei ⊢
    exact unitSubchart_holomorphic e he hei a ρ hρ hsub'
  refine ⟨i, s, ρ, hρ, ?_, ?_, hsp, hs, hsi, ?_, ?_, ?_, ?_,
    unitSubchart_source_subset (F.box i) a ρ hρ, ?_, ?_, ?_, ?_, ?_, ?_, hsub'⟩
  · simpa only [ha] using mem_unitSubchart_source e y hye ρ hρ
  · exact (unitSubchart_source_subset e a ρ hρ).trans inter_subset_left
  · ext q
    change (((q ∈ s.source ∧ s q ∈ (F.box i).source) ∧ True) ∧
      blockAffine a ρ hρ (F.box i (s q)) ∈ unitProduct) ↔
      (q ∈ s.source ∧ ((s q ∈ (F.box i).source ∧ True) ∧
        blockAffine a ρ hρ (F.box i (s q)) ∈ unitProduct))
    tauto
  · exact unitSubchart_target e a ρ hρ hsub'
  · exact unitSubchart_target (F.box i) a ρ hρ hsub₀
  · intro q hq
    let z := unitSubchart (F.box i) a ρ hρ q
    have hz : z ∈ unitProduct := by
      simpa only [unitSubchart_target (F.box i) a ρ hρ hsub₀] using
        (unitSubchart (F.box i) a ρ hρ).map_source hq
    have hez := hsub' ⟨z, hz, rfl⟩
    have hq' := (unitSubchart (F.box i) a ρ hρ).left_inv hq
    change (F.box i).symm ((blockAffine a ρ hρ).symm z) = q at hq'
    exact hq' ▸ hez.2
  · exact hbhol.1
  · exact hbhol.2
  · intro z
    rfl
  · intro z hz
    have hq := (unitSubchart e a ρ hρ).map_target hz
    have hsour := (unitSubchart_source_subset e a ρ hρ hq).1
    rw [← hsp hsour]
    change s (s.symm ((unitSubchart (F.box i) a ρ hρ).symm z)) = _
    have hzt : z ∈ unitProduct := by
      change z ∈ (unitSubchart e a ρ hρ).target at hz
      rwa [unitSubchart_target e a ρ hρ hsub'] at hz
    exact s.right_inv ((hsub' ⟨z, hzt, rfl⟩).2)
  · intro q hq
    change blockAffine a ρ hρ (F.box i (s q)) =
      blockAffine a ρ hρ (F.box i (p q))
    rw [hsp ((unitSubchart_source_subset e a ρ hρ hq).1)]
  · intro q q'
    exact unitSubchart_same_plaque_iff e a ρ hρ q q'

omit [ChartedSpace (ComplexModel d) Y] in
/-- Lifted unit-box coordinates equal the block-affine normalization of downstairs coordinates. -/
private theorem lifted_unit_box_original_coordinates
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (s : OpenPartialHomeomorph Y X) (hsp : EqOn s p s.source)
    (i : F.boxIndex) (a : ComplexModel r × ComplexModel c)
    (ρ : ℝ) (hρ : 0 < ρ) (q : Y)
    (hq : q ∈ (unitSubchart (s.trans (F.box i)) a ρ hρ).source) :
    F.box i (p q) = a + (ρ : ℂ) • (unitSubchart (s.trans (F.box i)) a ρ hρ q) := by
  have hqs := (unitSubchart_source_subset (s.trans (F.box i)) a ρ hρ hq).1
  change F.box i (p q) = (blockAffine a ρ hρ).symm
    (blockAffine a ρ hρ (F.box i (s q)))
  rw [hsp hqs, Homeomorph.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The lifted box derivative flattens the pullback of the downstairs horizontal distribution. -/
private theorem lifted_unit_box_horizontal_iff
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (s : OpenPartialHomeomorph Y X) (hsp : EqOn s p s.source)
    (hs : ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source)
    (i : F.boxIndex) (a : ComplexModel r × ComplexModel c)
    (ρ : ℝ) (hρ : 0 < ρ) (q : Y)
    (hq : q ∈ (unitSubchart (s.trans (F.box i)) a ρ hρ).source)
    (v : TangentSpace (complexModel d) q) :
    (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
      (unitSubchart (s.trans (F.box i)) a ρ hρ) q v).2 = 0 ↔
    (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
      (F.box i) (p q) (mfderiv (complexModel d) (complexModel d) p q v)).2 = 0 := by
  have hqe := unitSubchart_source_subset (s.trans (F.box i)) a ρ hρ hq
  have hqs : q ∈ s.source := hqe.1
  have hqF : s q ∈ (F.box i).source := hqe.2
  have he : ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c)) ∞
      (s.trans (F.box i)) (s.trans (F.box i)).source := by
    apply (F.box_holomorphic i).comp (hs.mono inter_subset_left)
    exact fun q hq ↦ hq.2
  rw [unitSubchart_complex_horizontal_iff (s.trans (F.box i)) he a ρ hρ q hq v]
  have hsD := (hs.contMDiffAt (s.open_source.mem_nhds hqs)).mdifferentiableAt (by simp)
  have hFD := ((F.box_holomorphic i).contMDiffAt
    ((F.box i).open_source.mem_nhds hqF)).mdifferentiableAt (by simp)
  have hEq : (s : Y → X) =ᶠ[𝓝 q] p := by
    filter_upwards [s.open_source.mem_nhds hqs] with z hz
    exact hsp hz
  have hDs : mfderiv (complexModel d) (complexModel d) s q =
      mfderiv (complexModel d) (complexModel d) p q := by
    have hh := hEq.mfderiv_eq (I := complexModel d) (I' := complexModel d)
    exact hh
  change (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
    (F.box i ∘ s) q v).2 = 0 ↔ _
  rw [mfderiv_comp q hFD hsD]
  let dF (z : X) : ComplexModel d →L[ℂ] (ComplexModel r × ComplexModel c) :=
    mfderiv (complexModel d) ((complexModel r).prod (complexModel c)) (F.box i) z
  change (dF (s q) (mfderiv (complexModel d) (complexModel d) s q v)).2 = 0 ↔
    (dF (p q) (mfderiv (complexModel d) (complexModel d) p q v)).2 = 0
  rw [hDs, hsp hqs]

/-- A holomorphic covering admits a family of lifted unit boxes indexed by its points. -/
private theorem exists_lifted_unit_box_family
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (hsheets : ∀ y : Y, ∃ s : OpenPartialHomeomorph Y X,
      y ∈ s.source ∧ EqOn s p s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target) :
    ∃ B : Y → OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c),
      ∀ y : Y, y ∈ (B y).source ∧
        (B y).target = (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
          (complexFoliationDisk c : Set (ComplexModel c)) ∧
        ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c)) ∞
          (B y) (B y).source ∧
        ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d) ∞
          (B y).symm (B y).target ∧
        ∃ (i : F.boxIndex) (s : OpenPartialHomeomorph Y X) (ρ : ℝ) (hρ : 0 < ρ),
          let a := F.box i (p y)
          let b₀ := unitSubchart (F.box i) a ρ hρ
          B y = unitSubchart (s.trans (F.box i)) a ρ hρ ∧
          EqOn s p s.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target ∧
          (B y).source = s.source ∩ s ⁻¹' b₀.source ∧
          b₀.source ⊆ s.target ∧ b₀.source ⊆ (F.box i).source ∧
          b₀.target = (B y).target ∧
          (∀ z, (B y).symm z = s.symm (b₀.symm z)) ∧
          (∀ z ∈ (B y).target, p ((B y).symm z) = b₀.symm z) ∧
          (∀ q ∈ (B y).source, B y q = b₀ (p q)) ∧
          (∀ q q', (B y q).2 = (B y q').2 ↔
            (F.box i (s q)).2 = (F.box i (s q')).2) ∧
          (blockAffine a ρ hρ).symm '' unitProduct ⊆ (s.trans (F.box i)).target := by
  classical
  choose i s ρ hρ hh using exists_lifted_unit_box F p hsheets
  let B := fun y ↦ unitSubchart ((s y).trans (F.box (i y)))
    (F.box (i y) (p y)) (ρ y) (hρ y)
  refine ⟨B, ?_⟩
  intro y
  rcases hh y with ⟨hy, hsub, hsp, hs, hsi, hsrc, hbt, hb₀t, hb₀s, hb₀F,
    hb, hbi, hinv, hproj, hfwd, hplaque, hfull⟩
  refine ⟨hy, hbt, hb, hbi, i y, s y, ρ y, hρ y, rfl, hsp, hs, hsi, hsrc,
    hb₀s, hb₀F, hb₀t.trans hbt.symm, hinv, hproj, hfwd, hplaque, hfull⟩



end HolomorphicAnosov.Theorem12CoverBoxes


/-! Finite lifted plaque chains characterize endpoints of lifted intrinsic paths. (Hatcher,
pp.60–62; Bredon, II.14, pp.111–112; Nisoli, pp.9–10) -/

namespace HolomorphicAnosov.LiftedPlaquePartition
open Set Topology _root_.Topology
open scoped unitInterval ContDiff

/-- A continuous path subordinate to an open cover whose within-set pairs are primitive steps gives
a finite chain of primitive steps. -/
private theorem path_finite_chain
    {Q Y : Type*} [TopologicalSpace Q] (v : Q → Y) (R : Y → Y → Prop)
    (hlocal : ∀ q : Q, ∃ U : Set Q, IsOpen U ∧ q ∈ U ∧
      ∀ a ∈ U, ∀ b ∈ U, R (v a) (v b))
    {q₀ q₁ : Q} (γ : Path q₀ q₁) : Relation.EqvGen R (v q₀) (v q₁) := by
  choose U hU hmem hstep using hlocal
  let C : Q → Set unitInterval := fun q ↦ γ ⁻¹' U q
  have hCo : ∀ q, IsOpen (C q) := fun q ↦ (hU q).preimage γ.continuous
  have hCc : univ ⊆ ⋃ q, C q := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t, hmem (γ t)⟩
  obtain ⟨t, ht₀, hmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hCo hCc
  have hchain : ∀ n, Relation.EqvGen R (v (γ (t 0))) (v (γ (t n))) := by
    intro n
    induction n with
    | zero => exact Relation.EqvGen.refl _
    | succ n ih =>
      obtain ⟨q, hq⟩ := hsub n
      exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _
        (hstep q _ (hq ⟨le_rfl, hmono (Nat.le_succ n)⟩)
          _ (hq ⟨hmono (Nat.le_succ n), le_rfl⟩)))
  have h := hchain N
  simpa only [ht₀, hN N le_rfl, Path.source, Path.target] using h

/-- A finite chain of realizable lifted plaque steps gives a path in the native pullback. -/
private theorem chain_lifts_to_pullback_path
    {X Y L : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X) (R : Y → Y → Prop)
    (hsymm : ∀ ⦃x z⦄, R x z → R z x)
    (hstep : ∀ q : IntrinsicCoveringPullback j p, ∀ z,
      R q.val.2 z → ∃ q' : IntrinsicCoveringPullback j p,
        q'.val.2 = z ∧ Joined q q')
    (q : IntrinsicCoveringPullback j p) {z : Y} (h : Relation.EqvGen R q.val.2 z) :
    ∃ q' : IntrinsicCoveringPullback j p, q'.val.2 = z ∧ Joined q q' := by
  let : Std.Symm R := ⟨hsymm⟩
  rw [Relation.EqvGen.eqvGen_eq_reflTransGen] at h
  generalize heq : q.val.2 = a at h
  induction h with
  | refl => exact ⟨q, heq, Joined.refl q⟩
  | @tail b c hab hbc ih =>
    obtain ⟨q', hq', hqq'⟩ := ih
    obtain ⟨q'', hq'', hq'q''⟩ := hstep q' c (hq'.symm ▸ hbc)
    exact ⟨q'', hq'', hqq'.trans hq'q''⟩

/-- Finite lifted plaque chains coincide with marked intrinsic path-lift endpoints when steps are
realizable and locally cover the pullback. -/
private theorem chain_iff_liftedIntrinsicLeafRange
    {X Y L : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X) (a : L) (y : Y) (hmark : j a = p y)
    (R : Y → Y → Prop) (hsymm : ∀ ⦃x z⦄, R x z → R z x)
    (hstep : ∀ q : IntrinsicCoveringPullback j p, ∀ z,
      R q.val.2 z → ∃ q' : IntrinsicCoveringPullback j p,
        q'.val.2 = z ∧ Joined q q')
    (hlocal : ∀ q : IntrinsicCoveringPullback j p,
      ∃ U : Set (IntrinsicCoveringPullback j p), IsOpen U ∧ q ∈ U ∧
        ∀ q₁ ∈ U, ∀ q₂ ∈ U, R q₁.val.2 q₂.val.2)
    (z : Y) : Relation.EqvGen R y z ↔ z ∈ liftedIntrinsicLeafRange p j a y := by
  constructor
  · intro h
    obtain ⟨q, hq, ⟨ξ⟩⟩ := chain_lifts_to_pullback_path p j R hsymm hstep
      (intrinsicCoveringPullbackPoint j p a y hmark) h
    refine ⟨q.val.1, ξ.map (continuous_fst.comp continuous_subtype_val),
      (ξ.map (continuous_snd.comp continuous_subtype_val)).cast rfl hq.symm, ?_⟩
    intro t
    exact (ξ t).property.symm
  · rintro ⟨b, γ, η, hη⟩
    let q : IntrinsicCoveringPullback j p :=
      ⟨(b, z), by simpa only [Path.target] using (hη 1).symm⟩
    let ξ : Path (intrinsicCoveringPullbackPoint j p a y hmark) q :=
      { toFun := fun t ↦ ⟨(γ t, η t), (hη t).symm⟩
        continuous_toFun := (γ.continuous.prodMk η.continuous).subtype_mk _
        source' := by apply Subtype.ext; exact Prod.ext γ.source η.source
        target' := by apply Subtype.ext; exact Prod.ext γ.target η.target }
    exact path_finite_chain (fun q ↦ q.val.2) R hlocal ξ

noncomputable section

universe u v w

variable {d r c : ℕ} {X : Type u}
  [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The original plaque parametrization with its quotient class label rebased by equality. -/
private def originalPlaqueMap (F : RegularHolomorphicFoliation.{u,w} d r c X)
    (i : F.boxIndex) (w : complexFoliationDisk c) (q : Quotient F.partition)
    (h : F.label i w = q) : complexFoliationDisk r → IntrinsicFoliationLeaf F.partition q :=
  fun a ↦ ⟨(F.box i).symm (a.val, w.val), (F.label_eq i a w).trans h⟩

/-- The rebased original plaque map is an open embedding in its native class topology. -/
private theorem originalPlaqueMap_isOpenEmbedding
    (F : RegularHolomorphicFoliation.{u,w} d r c X)
    (i : F.boxIndex) (w : complexFoliationDisk c) (q : Quotient F.partition)
    (h : F.label i w = q) :
    letI := F.leafTopology q
    IsOpenEmbedding (originalPlaqueMap F i w q h) := by
  subst q
  let := F.leafTopology (F.label i w)
  let := F.leafCharts (F.label i w)
  have heq : originalPlaqueMap F i w (F.label i w) rfl =
      fun a ↦ (F.plaqueChart i w a).val := by
    funext a
    apply Subtype.ext
    exact (F.plaqueChart_eq i a w).symm
  rw [heq]
  exact (F.plaque i w).isOpenEmbedding'.comp
    (F.plaqueChart i w).toHomeomorph.isOpenEmbedding

/-- The map between coordinate disks induced by a horizontal homeomorphism whose image lies in the
target disk. -/
private def horizontalDiscMap (A : ComplexModel r ≃ₜ ComplexModel r)
    (hA : A '' (complexFoliationDisk r : Set (ComplexModel r)) ⊆
      (complexFoliationDisk r : Set (ComplexModel r))) :
    complexFoliationDisk r → complexFoliationDisk r :=
  fun a ↦ ⟨A a.val, hA ⟨a.val, a.property, rfl⟩⟩

/-- The restricted horizontal coordinate map is an open embedding. -/
private theorem horizontalDiscMap_isOpenEmbedding
    (A : ComplexModel r ≃ₜ ComplexModel r)
    (hA : A '' (complexFoliationDisk r : Set (ComplexModel r)) ⊆
      (complexFoliationDisk r : Set (ComplexModel r))) :
    IsOpenEmbedding (horizontalDiscMap A hA) := by
  exact (complexFoliationDisk r).isOpenEmbedding'.of_comp _
    (A.isOpenEmbedding.comp (complexFoliationDisk r).isOpenEmbedding')

/-- Affine restrictions of original plaques are open embeddings in their native classes. -/
private theorem originalAffinePlaque_isOpenEmbedding
    (F : RegularHolomorphicFoliation.{u,w} d r c X)
    (i : F.boxIndex) (w : complexFoliationDisk c) (q : Quotient F.partition)
    (h : F.label i w = q) (A : ComplexModel r ≃ₜ ComplexModel r)
    (hA : A '' (complexFoliationDisk r : Set (ComplexModel r)) ⊆
      (complexFoliationDisk r : Set (ComplexModel r))) :
    letI := F.leafTopology q
    IsOpenEmbedding (originalPlaqueMap F i w q h ∘ horizontalDiscMap A hA) := by
  let := F.leafTopology q
  exact (originalPlaqueMap_isOpenEmbedding F i w q h).comp
    (horizontalDiscMap_isOpenEmbedding A hA)

/-- Within a covering sheet, the native first coordinate uniquely determines a lifted slice point. -/
private theorem sheet_slice_unique
    {X Y L : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X)
    (b : OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (s : OpenPartialHomeomorph Y X) (hs : b.source ⊆ s.source)
    (hsp : EqOn s p s.source) (w : ComplexModel c)
    (htarget : ∀ a : complexFoliationDisk r, (a.val, w) ∈ b.target)
    (φ : complexFoliationDisk r → L)
    (hφ : ∀ a, j (φ a) = p (b.symm (a.val, w)))
    (q : IntrinsicCoveringPullback j p) (a : complexFoliationDisk r)
    (hqa : q.val.1 = φ a) (hqb : q.val.2 ∈ b.source) :
    q.val.2 = b.symm (a.val, w) := by
  have hx := hs (b.map_target (htarget a))
  apply s.injOn (hs hqb) hx
  rw [hsp (hs hqb), hsp hx, ← q.property, hqa, hφ]

/-- A native open slice intersected with a covering sheet is pullback-open, and its pairs lie in the
same raw slice. -/
private theorem sheet_slice_pullback_open
    {X Y L : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X)
    (b : OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (s : OpenPartialHomeomorph Y X) (hs : b.source ⊆ s.source)
    (hsp : EqOn s p s.source) (w : ComplexModel c)
    (htarget : ∀ a : complexFoliationDisk r, (a.val, w) ∈ b.target)
    (φ : complexFoliationDisk r → L) (hφopen : IsOpenEmbedding φ)
    (hφ : ∀ a, j (φ a) = p (b.symm (a.val, w))) :
    IsOpen {q : IntrinsicCoveringPullback j p |
      q.val.1 ∈ range φ ∧ q.val.2 ∈ b.source} ∧
    ∀ q₁ : IntrinsicCoveringPullback j p,
      q₁.val.1 ∈ range φ → q₁.val.2 ∈ b.source →
      ∀ q₂ : IntrinsicCoveringPullback j p,
        q₂.val.1 ∈ range φ → q₂.val.2 ∈ b.source →
        ∃ a₁ a₂ : complexFoliationDisk r,
          b.symm (a₁.val, w) = q₁.val.2 ∧ b.symm (a₂.val, w) = q₂.val.2 := by
  refine ⟨(hφopen.isOpen_range.preimage
    (continuous_fst.comp continuous_subtype_val)).inter
    (b.open_source.preimage (continuous_snd.comp continuous_subtype_val)), ?_⟩
  rintro q₁ ⟨a₁, ha₁⟩ hq₁ q₂ ⟨a₂, ha₂⟩ hq₂
  exact ⟨a₁, a₂,
    (sheet_slice_unique p j b s hs hsp w htarget φ hφ q₁ a₁ ha₁.symm hq₁).symm,
    (sheet_slice_unique p j b s hs hsp w htarget φ hφ q₂ a₂ ha₂.symm hq₂).symm⟩

/-- Points of a lifted slice are joined by paths in the native pullback. -/
private theorem sheet_slice_joined
    {X Y L : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X)
    (b : OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (w : ComplexModel c)
    (htarget : ∀ a : complexFoliationDisk r, (a.val, w) ∈ b.target)
    (φ : complexFoliationDisk r → L) (hφcont : Continuous φ)
    (hφ : ∀ a, j (φ a) = p (b.symm (a.val, w)))
    (a₁ a₂ : complexFoliationDisk r) :
    Joined (⟨(φ a₁, b.symm (a₁.val, w)), hφ a₁⟩ : IntrinsicCoveringPullback j p)
      ⟨(φ a₂, b.symm (a₂.val, w)), hφ a₂⟩ := by
  let Ψ : complexFoliationDisk r → IntrinsicCoveringPullback j p :=
    fun a ↦ ⟨(φ a, b.symm (a.val, w)), hφ a⟩
  have hΨ : Continuous Ψ := by
    apply Continuous.subtype_mk
    apply hφcont.prodMk
    exact b.continuousOn_symm.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) htarget
  exact ((Metric.isPathConnected_ball (E := ComplexModel r) (x := 0)
    (show (0 : ℝ) < 1 by norm_num)).joinedIn a₁.val a₁.property
      a₂.val a₂.property).joined_subtype.map hΨ

/-- A lifted raw slice has a native open parametrization in its downstairs affine coordinates. -/
private theorem original_raw_slice
    {Y : Type v} [TopologicalSpace Y]
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X) (y : Y)
    (b : OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (i : F.boxIndex) (A : ComplexModel r ≃ₜ ComplexModel r)
    (K : ComplexModel c ≃ₜ ComplexModel c)
    (hcoord : ∀ a : complexFoliationDisk r, ∀ w : complexFoliationDisk c,
      (A a.val, K w.val) ∈ (F.box i).target)
    (hproj : ∀ a : complexFoliationDisk r, ∀ w : complexFoliationDisk c,
      p (b.symm (a.val, w.val)) = (F.box i).symm (A a.val, K w.val))
    (w₀ : complexFoliationDisk c) (a₀ : complexFoliationDisk r)
    (q : IntrinsicCoveringPullback (Subtype.val : F.Leaf (p y) → X) p)
    (hq : b.symm (a₀.val, w₀.val) = q.val.2) :
    ∃ φ : complexFoliationDisk r → F.Leaf (p y),
      IsOpenEmbedding φ ∧
      (∀ a, (φ a).val = p (b.symm (a.val, w₀.val))) ∧ q.val.1 = φ a₀ := by
  have hc : ∀ a : complexFoliationDisk r,
      A a.val ∈ (complexFoliationDisk r : Set (ComplexModel r)) ∧
      K w₀.val ∈ (complexFoliationDisk c : Set (ComplexModel c)) := by
    intro a
    simpa only [F.box_target i, mem_prod] using hcoord a w₀
  let w' : complexFoliationDisk c := ⟨K w₀.val, (hc a₀).2⟩
  have hA : A '' (complexFoliationDisk r : Set (ComplexModel r)) ⊆
      (complexFoliationDisk r : Set (ComplexModel r)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hc ⟨a, ha⟩).1
  have hval : (F.box i).symm (A a₀.val, w'.val) = q.val.1.val := by
    rw [← hproj a₀ w₀, hq, ← q.property]
  have hlabel : F.label i w' = Quotient.mk F.partition (p y) := by
    rw [← F.label_eq i (horizontalDiscMap A hA a₀) w']
    change Quotient.mk F.partition ((F.box i).symm (A a₀.val, w'.val)) = _
    rw [hval]
    exact q.val.1.property
  let φ := originalPlaqueMap F i w' (Quotient.mk F.partition (p y)) hlabel ∘
    horizontalDiscMap A hA
  refine ⟨φ, originalAffinePlaque_isOpenEmbedding F i w' _ hlabel A hA, ?_, ?_⟩
  · intro a
    exact (hproj a w₀).symm
  · apply Subtype.ext
    exact hval.symm

/-- The relation of lying in a common horizontal slice of a raw lifted box. -/
private def rawPlaqueStep {Y J : Type*} [TopologicalSpace Y]
    (B : J → OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (x z : Y) : Prop :=
  ∃ k, ∃ w : complexFoliationDisk c, ∃ a a' : complexFoliationDisk r,
    (B k).symm (a.val, w.val) = x ∧ (B k).symm (a'.val, w.val) = z

/-- Finite raw lifted-plaque chains coincide with the marked intrinsic path-lift range of the
downstairs leaf. -/
private theorem raw_partition_iff_lifted_range
    {Y : Type v} [TopologicalSpace Y] {J : Type*}
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (B : J → OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (hcover : ∀ z : Y, ∃ k, z ∈ (B k).source)
    (htarget : ∀ k, (B k).target =
      (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)))
    (index : J → F.boxIndex) (sheet : J → OpenPartialHomeomorph Y X)
    (hs : ∀ k, (B k).source ⊆ (sheet k).source)
    (hsp : ∀ k, EqOn (sheet k) p (sheet k).source)
    (A : J → ComplexModel r ≃ₜ ComplexModel r)
    (K : J → ComplexModel c ≃ₜ ComplexModel c)
    (hcoord : ∀ k, ∀ a : complexFoliationDisk r, ∀ w : complexFoliationDisk c,
      (A k a.val, K k w.val) ∈ (F.box (index k)).target)
    (hproj : ∀ k, ∀ a : complexFoliationDisk r, ∀ w : complexFoliationDisk c,
      p ((B k).symm (a.val, w.val)) =
        (F.box (index k)).symm (A k a.val, K k w.val))
    (y z : Y) : Relation.EqvGen (rawPlaqueStep B) y z ↔
      z ∈ liftedIntrinsicLeafRange p (Subtype.val : F.Leaf (p y) → X)
        ⟨p y, rfl⟩ y := by
  let j : F.Leaf (p y) → X := Subtype.val
  have hsymm : ∀ ⦃x z⦄, rawPlaqueStep B x z → rawPlaqueStep B z x := by
    rintro x z ⟨k, w₀, a, a', ha, ha'⟩
    exact ⟨k, w₀, a', a, ha', ha⟩
  have hstep : ∀ q : IntrinsicCoveringPullback j p, ∀ z,
      rawPlaqueStep B q.val.2 z → ∃ q' : IntrinsicCoveringPullback j p,
        q'.val.2 = z ∧ Joined q q' := by
    rintro q z ⟨k, w₀, a, a', ha, ha'⟩
    obtain ⟨φ, hφopen, hφ, hqa⟩ := original_raw_slice F p y (B k) (index k)
      (A k) (K k) (hcoord k) (hproj k) w₀ a q ha
    have ht : ∀ v : complexFoliationDisk r, (v.val, w₀.val) ∈ (B k).target :=
      fun v ↦ (htarget k).symm ▸ ⟨v.property, w₀.property⟩
    have hj := sheet_slice_joined p j (B k) w₀.val ht φ hφopen.continuous hφ a a'
    let q' : IntrinsicCoveringPullback j p :=
      ⟨(φ a', (B k).symm (a'.val, w₀.val)), hφ a'⟩
    have heq : q = (⟨(φ a, (B k).symm (a.val, w₀.val)), hφ a⟩ :
        IntrinsicCoveringPullback j p) := by
      apply Subtype.ext
      exact Prod.ext hqa ha.symm
    exact ⟨q', ha', heq.symm ▸ hj⟩
  have hlocal : ∀ q : IntrinsicCoveringPullback j p,
      ∃ U : Set (IntrinsicCoveringPullback j p), IsOpen U ∧ q ∈ U ∧
        ∀ q₁ ∈ U, ∀ q₂ ∈ U, rawPlaqueStep B q₁.val.2 q₂.val.2 := by
    intro q
    obtain ⟨k, hqk⟩ := hcover q.val.2
    have hqt := (B k).map_source hqk
    rw [htarget k] at hqt
    let a : complexFoliationDisk r := ⟨((B k) q.val.2).1, hqt.1⟩
    let w₀ : complexFoliationDisk c := ⟨((B k) q.val.2).2, hqt.2⟩
    have ha : (B k).symm (a.val, w₀.val) = q.val.2 := (B k).left_inv hqk
    obtain ⟨φ, hφopen, hφ, hqa⟩ := original_raw_slice F p y (B k) (index k)
      (A k) (K k) (hcoord k) (hproj k) w₀ a q ha
    have ht : ∀ v : complexFoliationDisk r, (v.val, w₀.val) ∈ (B k).target :=
      fun v ↦ (htarget k).symm ▸ ⟨v.property, w₀.property⟩
    obtain ⟨hU, hpair⟩ := sheet_slice_pullback_open p j (B k) (sheet k)
      (hs k) (hsp k) w₀.val ht φ hφopen hφ
    refine ⟨{q | q.val.1 ∈ range φ ∧ q.val.2 ∈ (B k).source}, hU,
      ⟨⟨a, hqa.symm⟩, hqk⟩, ?_⟩
    intro q₁ hq₁ q₂ hq₂
    obtain ⟨a₁, a₂, ha₁, ha₂⟩ := hpair q₁ hq₁.1 hq₁.2 q₂ hq₂.1 hq₂.2
    exact ⟨k, w₀, a₁, a₂, ha₁, ha₂⟩
  exact chain_iff_liftedIntrinsicLeafRange p j ⟨p y, rfl⟩ y rfl
    (rawPlaqueStep B) hsymm hstep hlocal z

/-- The inverse affine normalization of a complex coordinate block. -/
private def affineCoordinate {n : ℕ} (a : ComplexModel n) (ρ : ℝ) (hρ : 0 < ρ) :
    ComplexModel n ≃ₜ ComplexModel n where
  toFun z := a + (ρ : ℂ) • z
  invFun z := (ρ : ℂ)⁻¹ • (z - a)
  left_inv z := by
    have hc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
    change (ρ : ℂ)⁻¹ • (a + (ρ : ℂ) • z - a) = z
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
  right_inv z := by
    have hc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
    change a + (ρ : ℂ) • ((ρ : ℂ)⁻¹ • (z - a)) = z
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    abel
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The partition generated by affine sheet-restricted lifted boxes equals the marked intrinsic
path-lift range. -/
private theorem raw_affine_partition_iff_lifted_range
    {Y : Type v} [TopologicalSpace Y] {J : Type*}
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (B : J → OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (hcover : ∀ z : Y, ∃ k, z ∈ (B k).source)
    (htarget : ∀ k, (B k).target =
      (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)))
    (index : J → F.boxIndex) (sheet : J → OpenPartialHomeomorph Y X)
    (hs : ∀ k, (B k).source ⊆ (sheet k).source)
    (hsp : ∀ k, EqOn (sheet k) p (sheet k).source)
    (center : J → ComplexModel r × ComplexModel c)
    (radius : J → ℝ) (hradius : ∀ k, 0 < radius k)
    (hcoord : ∀ k, ∀ a : complexFoliationDisk r, ∀ w : complexFoliationDisk c,
      center k + (radius k : ℂ) • (a.val, w.val) ∈ (F.box (index k)).target)
    (hproj : ∀ k, ∀ a : complexFoliationDisk r, ∀ w : complexFoliationDisk c,
      p ((B k).symm (a.val, w.val)) =
        (F.box (index k)).symm (center k + (radius k : ℂ) • (a.val, w.val)))
    (y z : Y) : Relation.EqvGen (rawPlaqueStep B) y z ↔
      z ∈ liftedIntrinsicLeafRange p (Subtype.val : F.Leaf (p y) → X)
        ⟨p y, rfl⟩ y := by
  apply raw_partition_iff_lifted_range F p B hcover htarget index sheet hs hsp
    (fun k ↦ affineCoordinate (center k).1 (radius k) (hradius k))
    (fun k ↦ affineCoordinate (center k).2 (radius k) (hradius k))
  · exact hcoord
  · exact hproj

end

end HolomorphicAnosov.LiftedPlaquePartition


/-! Pointed native pullback components have inclusion ranges equal to marked intrinsic path-lift
endpoint ranges. (Hatcher, pp.60–62; Bredon, II.14, pp.111–112) -/

namespace HolomorphicAnosov

universe u v w

/-- The inclusion range of a pointed intrinsic pullback leaf equals its marked intrinsic path-lift
range. -/
private theorem intrinsicCoveringLeafInclusion_range_eq
    {X : Type u} {Y : Type v} {L : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X) (a : L) (y : Y) (h : j a = p y) :
    Set.range (intrinsicCoveringLeafInclusion j p a y h) =
      liftedIntrinsicLeafRange p j a y := by
  ext z
  constructor
  · rintro ⟨⟨q, hq⟩, rfl⟩
    obtain ⟨ξ⟩ := hq
    refine ⟨q.val.1,
      ξ.map (continuous_fst.comp continuous_subtype_val),
      ξ.map (continuous_snd.comp continuous_subtype_val), ?_⟩
    intro t
    exact (ξ t).property.symm
  · rintro ⟨b, γ, η, hη⟩
    let q : IntrinsicCoveringPullback j p := ⟨(b, z), by
      simpa only [Path.target] using (hη 1).symm⟩
    let ξ : Path (intrinsicCoveringPullbackPoint j p a y h) q :=
      { toFun := fun t ↦ ⟨(γ t, η t), (hη t).symm⟩
        continuous_toFun := (γ.continuous.prodMk η.continuous).subtype_mk _
        source' := by apply Subtype.ext; exact Prod.ext γ.source η.source
        target' := by apply Subtype.ext; exact Prod.ext γ.target η.target }
    exact ⟨⟨q, ⟨ξ⟩⟩, rfl⟩


/-- A lifted leaf covering its native base has inclusion range equal to the marked intrinsic
path-lift range. (Hatcher, pp.60–62) -/
private theorem liftedIntrinsicLeafRange_eq_of_leaf_covering
    {X : Type u} {Y : Type v} {L : Type w} {T : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    [TopologicalSpace T] [PathConnectedSpace T]
    (p : Y → X) (j : L → X) (k : T → L) (i : T → Y)
    (hp : IsCoveringMap p) (hk : IsCoveringMap k) (hi : Continuous i)
    (hcomm : ∀ t, p (i t) = j (k t)) (t₀ : T) :
    liftedIntrinsicLeafRange p j (k t₀) (i t₀) = Set.range i := by
  ext z
  constructor
  · rintro ⟨b, γ, η, hη⟩
    obtain ⟨Γ, hΓ, hΓ₀⟩ := hk.exists_path_lifts γ.toContinuousMap t₀ γ.source
    have heq : (fun t ↦ i (Γ t)) = η := hp.eq_of_comp_eq
      (hi.comp Γ.continuous) η.continuous (by
        funext t
        exact (hcomm (Γ t)).trans
          ((congrArg j (congrFun hΓ t)).trans (hη t).symm))
      0 (by simp only [hΓ₀, Path.source])
    exact ⟨Γ 1, (congrFun heq 1).trans η.target⟩
  · rintro ⟨t, rfl⟩
    let ξ := PathConnectedSpace.somePath t₀ t
    exact ⟨k t, ξ.map hk.continuous, ξ.map hi, fun s ↦ hcomm (ξ s)⟩


/-- A surjective projection derivative maps the pullback tangent distribution onto the base
distribution. -/
private theorem image_pullback_tangent
    {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℂ E₁]
    [AddCommGroup E₂] [Module ℂ E₂]
    (D : E₁ →ₗ[ℂ] E₂) (hD : Function.Surjective D) (S : Submodule ℂ E₂) :
    (S.comap D).map D = S :=
  Submodule.map_comap_eq_of_surjective hD S


open scoped ContDiff

/-- Intrinsic leaves of a regular holomorphic foliation are path connected. (Nisoli, pp.9–10) -/
private theorem regularHolomorphicFoliation_leaf_pathConnected
    {d r c : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation.{u, v} d r c M) (y : M) :
    PathConnectedSpace (F.Leaf y) := by
  have : ConnectedSpace (F.Leaf y) := F.leafConnected _
  have : LocallyPathConnectedSpace (F.Leaf y) :=
    ChartedSpace.locallyPathConnectedSpace (ComplexModel r) (F.Leaf y)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- A regular foliation leaf covering the original native leaf has inclusion range equal to the
marked intrinsic path-lift range. -/
private theorem regularHolomorphicFoliation_leaf_range_eq
    {d r c : ℕ} {M : Type u} {X : Type v} {L : Type w}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace X] [TopologicalSpace L]
    (F : RegularHolomorphicFoliation.{u, u} d r c M) (y : M)
    (p : M → X) (j : L → X) (k : F.Leaf y → L)
    (hp : IsCoveringMap p) (hk : IsCoveringMap k)
    (hcomm : ∀ t : F.Leaf y, p t.val = j (k t)) :
    liftedIntrinsicLeafRange p j (k ⟨y, rfl⟩) y =
      Set.range (fun t : F.Leaf y ↦ t.val) := by
  have := regularHolomorphicFoliation_leaf_pathConnected F y
  exact liftedIntrinsicLeafRange_eq_of_leaf_covering p j k Subtype.val hp hk
    (F.inclusion_holomorphic _).continuous hcomm ⟨y, rfl⟩


end HolomorphicAnosov

/-! Pointed components of intrinsic pullback coverings cover their native base leaves. (Bredon, II
§14, pp.111–112; Hatcher, pp.60–62) -/

open Topology _root_.Topology Set
open scoped ContDiff

namespace HolomorphicAnosov

universe u v w
variable {S : Type u} {Y : Type v} {L : Type w}
variable [TopologicalSpace S] [TopologicalSpace Y] [TopologicalSpace L]

/-- The projection of a pointed intrinsic pullback leaf is surjective over a path-connected base
leaf. -/
private theorem intrinsicCoveringLeafProjection_surjective [PathConnectedSpace L]
    (j : L → S) (p : Y → S) (hj : Continuous j) (hp : IsCoveringMap p)
    (a : L) (y : Y) (h : j a = p y) :
    Function.Surjective (intrinsicCoveringLeafProjection j p a y h) := by
  intro b
  let γ := PathConnectedSpace.somePath a b
  obtain ⟨η, hη, hη0⟩ := hp.exists_path_lifts
    ⟨fun t ↦ j (γ t), hj.comp γ.continuous⟩ y (by simpa using h)
  let z : IntrinsicCoveringPullback j p := ⟨(b, η 1), by
    have hh := congr_fun hη 1
    simpa using hh.symm⟩
  have hz : z ∈ pathComponent (intrinsicCoveringPullbackPoint j p a y h) := by
    refine ⟨{ toFun := fun t ↦ ⟨(γ t, η t), (congr_fun hη t).symm⟩
              continuous_toFun := (γ.continuous.prodMk η.continuous).subtype_mk _
              source' := ?_
              target' := ?_ }⟩
    · apply Subtype.ext
      exact Prod.ext γ.source hη0
    · apply Subtype.ext
      exact Prod.ext γ.target rfl
  exact ⟨⟨z, hz⟩, rfl⟩

/-- The covering sheet chart pulled back over an open native base neighborhood. -/
private def intrinsicPullbackSheet {I : Type*} [TopologicalSpace I]
    (j : L → S) (p : Y → S) (hj : Continuous j)
    (U : Set S) (V : Set L) (hVU : V ⊆ j ⁻¹' U)
    (H : p ⁻¹' U ≃ₜ U × I) (hH : ∀ z, (H z).1.1 = p z) :
    {z : IntrinsicCoveringPullback j p // z.val.1 ∈ V} ≃ₜ V × I where
  toFun z := (⟨z.val.val.1, z.property⟩,
    (H ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact hVU z.property⟩).2)
  invFun z := ⟨⟨(z.1.val, (H.symm (⟨j z.1.val, hVU z.1.property⟩, z.2)).val), by
    have hh := hH (H.symm (⟨j z.1.val, hVU z.1.property⟩, z.2))
    simpa using hh⟩, z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hh : (⟨j z.val.val.1, hVU z.property⟩,
          (H ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact hVU z.property⟩).2) =
          H ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact hVU z.property⟩ := by
        apply Prod.ext
        · apply Subtype.ext
          exact z.val.property.trans (hH ⟨z.val.val.2, by
            change p z.val.val.2 ∈ U
            rw [← z.val.property]
            exact hVU z.property⟩).symm
        · rfl
      simp only [hh, H.symm_apply_apply]
  right_inv z := by
    apply Prod.ext
    · rfl
    · simp
  continuous_toFun := by
    exact
      ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).prodMk (continuous_snd.comp (H.continuous.comp
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)))
  continuous_invFun := by
    exact (((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp (H.symm.continuous.comp
        (((hj.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
          continuous_snd)))).subtype_mk _).subtype_mk _

/-- The intrinsic pullback projection is a covering map. -/
private theorem intrinsicPullbackProjection_isCoveringMap
    (j : L → S) (p : Y → S) (hj : Continuous j) (hp : IsCoveringMap p) :
    IsCoveringMap (fun z : IntrinsicCoveringPullback j p ↦ z.val.1) := by
  intro a
  obtain ⟨inst, U, haU, hU, hpU, H, hH⟩ := hp (j a)
  let V := j ⁻¹' U
  let e := intrinsicPullbackSheet j p hj U V (fun _ hx ↦ hx) H hH
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage
    (I := p ⁻¹' {j a})
  exact ⟨inst, V, haU, hU.preimage hj,
    (hU.preimage hj).preimage (continuous_fst.comp continuous_subtype_val), e, fun _ ↦ rfl⟩

section ComponentRestriction

variable {E : Type*} {B : Type*} {I : Type*}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace I]

/-- A covering sheet chart restricted to a smaller evenly covered neighborhood. -/
private def coveringSheetRestrict (f : E → B) (hf : Continuous f)
    (U V : Set B) (hVU : V ⊆ U)
    (H : f ⁻¹' U ≃ₜ U × I) (hH : ∀ z, (H z).1.val = f z) :
    f ⁻¹' V ≃ₜ V × I where
  toFun z := (⟨f z, z.property⟩, (H ⟨z, hVU z.property⟩).2)
  invFun z := ⟨H.symm (⟨z.1, hVU z.1.property⟩, z.2), by
    have hh := hH (H.symm (⟨z.1, hVU z.1.property⟩, z.2))
    have hh' : f (H.symm (⟨z.1, hVU z.1.property⟩, z.2)) = z.1.val := by
      simpa using hh.symm
    change f _ ∈ V
    rw [hh']
    exact z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    have hh : (⟨f z, hVU z.property⟩, (H ⟨z, hVU z.property⟩).2) =
        H ⟨z, hVU z.property⟩ := by
      apply Prod.ext
      · exact Subtype.ext (hH ⟨z, hVU z.property⟩).symm
      · rfl
    simp only [hh, H.symm_apply_apply]
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      have hh := hH (H.symm (⟨z.1, hVU z.1.property⟩, z.2))
      simpa using hh.symm
    · simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- All points in a path-connected covering sheet have the same path-component membership. -/
private theorem coveringSheet_component_iff (f : E → B) (V : Set B)
    (H : f ⁻¹' V ≃ₜ V × I) [PathConnectedSpace V]
    (e0 : E) (v0 v : V) (i : I) :
    (H.symm (v, i)).val ∈ pathComponent e0 ↔
      (H.symm (v0, i)).val ∈ pathComponent e0 := by
  let γ := PathConnectedSpace.somePath v0 v
  have hjoin : Joined (H.symm (v0, i)).val (H.symm (v, i)).val :=
    ⟨γ.map (continuous_subtype_val.comp
      (H.symm.continuous.comp (continuous_id.prodMk continuous_const)))⟩
  exact ⟨fun hc ↦ hc.trans hjoin.symm, fun hc ↦ hc.trans hjoin⟩

/-- The covering sheet chart restricted to sheets meeting the marked path component. -/
private def coveringComponentSheet (f : E → B) (V : Set B)
    (H : f ⁻¹' V ≃ₜ V × I) (hH : ∀ z, (H z).1.val = f z)
    [PathConnectedSpace V] (e0 : E) (v0 : V) :
    {z : pathComponent e0 // f z.val ∈ V} ≃ₜ
      V × {i : I // (H.symm (v0, i)).val ∈ pathComponent e0} where
  toFun z := (⟨f z.val.val, z.property⟩, ⟨(H ⟨z.val.val, z.property⟩).2, by
    have hz := (coveringSheet_component_iff f V H e0 v0
      (H ⟨z.val.val, z.property⟩).1 (H ⟨z.val.val, z.property⟩).2).mp
    exact hz (by simp)⟩)
  invFun z := ⟨⟨(H.symm (z.1, z.2.val)).val,
      (coveringSheet_component_iff f V H e0 v0 z.1 z.2.val).mpr z.2.property⟩, by
    have hh := hH (H.symm (z.1, z.2.val))
    have hh' : f (H.symm (z.1, z.2.val)) = z.1.val := by
      simpa using hh.symm
    change f _ ∈ V
    rw [hh']
    exact z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    have hh : (⟨f z.val.val, z.property⟩, (H ⟨z.val.val, z.property⟩).2) =
        H ⟨z.val.val, z.property⟩ := by
      apply Prod.ext
      · exact Subtype.ext (hH ⟨z.val.val, z.property⟩).symm
      · rfl
    simp only [hh, H.symm_apply_apply]
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      have hh := hH (H.symm (z.1, z.2.val))
      simpa using hh.symm
    · apply Subtype.ext
      simp
  continuous_toFun := by
    have hf : Continuous (fun z : f ⁻¹' V ↦ f z) := by
      have hh := (continuous_subtype_val.comp (continuous_fst.comp H.continuous))
      exact hh.congr (fun z ↦ hH z)
    have hc : Continuous (fun z : {z : pathComponent e0 // f z.val ∈ V} ↦
        (⟨z.val.val, z.property⟩ : f ⁻¹' V)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact ((hf.comp hc).subtype_mk _).prodMk
      ((continuous_snd.comp (H.continuous.comp hc)).subtype_mk _)
  continuous_invFun := by
    exact ((continuous_subtype_val.comp (H.symm.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).subtype_mk _).subtype_mk _

/-- A covering restricted to a pointed path component covers a locally path-connected base, with
fibres given by the sheets meeting the component. -/
private theorem isCoveringMap_pathComponent_restrict [LocallyPathConnectedSpace B]
    (f : E → B) (hf : IsCoveringMap f) (e0 : E) :
    IsCoveringMap (fun z : pathComponent e0 ↦ f z.val) := by
  intro b
  obtain ⟨inst, U, hbU, hU, hfU, H, hH⟩ := hf b
  obtain ⟨V, ⟨hV, hbV, hconn⟩, hVU⟩ :=
    (isOpen_isPathConnected_basis b).mem_iff.mp (hU.mem_nhds hbU)
  have : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp hconn
  let H' := coveringSheetRestrict f hf.continuous U V hVU H hH
  have hH' : ∀ z, (H' z).1.val = f z := fun _ ↦ rfl
  let J := {i : f ⁻¹' {b} // (H'.symm (⟨b, hbV⟩, i)).val ∈ pathComponent e0}
  have : DiscreteTopology J := inferInstance
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := J)
  exact ⟨inferInstance, V, hbV, hV,
    hV.preimage (hf.continuous.comp continuous_subtype_val),
    coveringComponentSheet f V H' hH' e0 ⟨b, hbV⟩, fun _ ↦ rfl⟩

/-- Path components of a covering of a locally path-connected base are open. -/
private theorem isOpen_pathComponent_of_isCoveringMap [LocallyPathConnectedSpace B]
    (f : E → B) (hf : IsCoveringMap f) (e0 : E) : IsOpen (pathComponent e0) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨inst, U, hzU, hU, hfU, H, hH⟩ := hf (f z)
  obtain ⟨V, ⟨hV, hzV, hconn⟩, hVU⟩ :=
    (isOpen_isPathConnected_basis (f z)).mem_iff.mp (hU.mem_nhds hzU)
  have : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp hconn
  let H' := coveringSheetRestrict f hf.continuous U V hVU H hH
  let v0 : V := ⟨f z, hzV⟩
  let i := (H' ⟨z, hzV⟩).2
  let W : Set (f ⁻¹' V) := (fun q ↦ (H' q).2) ⁻¹' {i}
  have hW : IsOpen W := (isOpen_discrete {i}).preimage
    (continuous_snd.comp H'.continuous)
  have hpreV : IsOpen (f ⁻¹' V) := hV.preimage hf.continuous
  have hzanchor : (H'.symm (v0, i)).val = z := by
    exact congr_arg Subtype.val (H'.symm_apply_apply ⟨z, hzV⟩)
  refine mem_nhds_iff.mpr ⟨Subtype.val '' W, ?_,
    hpreV.isOpenMap_subtype_val W hW, ⟨⟨z, hzV⟩, rfl, rfl⟩⟩
  rintro q ⟨q, hq, rfl⟩
  have hqi : (H' q).2 = i := hq
  have hanchor : (H'.symm (v0, (H' q).2)).val ∈ pathComponent e0 := by
    rw [hqi, hzanchor]
    exact hz
  have hcurrent := (coveringSheet_component_iff f V H' e0 v0
    (H' q).1 (H' q).2).mpr hanchor
  simpa using hcurrent

end ComponentRestriction

/-- The pointed native pullback leaf projection is a covering map. -/
private theorem intrinsicCoveringLeafProjection_isCoveringMap [LocallyPathConnectedSpace L]
    (j : L → S) (p : Y → S) (hj : Continuous j) (hp : IsCoveringMap p)
    (a : L) (y : Y) (h : j a = p y) :
    IsCoveringMap (intrinsicCoveringLeafProjection j p a y h) :=
  isCoveringMap_pathComponent_restrict _
    (intrinsicPullbackProjection_isCoveringMap j p hj hp)
    (intrinsicCoveringPullbackPoint j p a y h)

/-- The marked pullback component is open in the intrinsic pullback space. -/
private theorem intrinsicCoveringPullbackLeaf_isOpen [LocallyPathConnectedSpace L]
    (j : L → S) (p : Y → S) (hj : Continuous j) (hp : IsCoveringMap p)
    (a : L) (y : Y) (h : j a = p y) :
    IsOpen (pathComponent (intrinsicCoveringPullbackPoint j p a y h)) :=
  isOpen_pathComponent_of_isCoveringMap _
    (intrinsicPullbackProjection_isCoveringMap j p hj hp)
    (intrinsicCoveringPullbackPoint j p a y h)

section OriginalNativeLeaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
variable (f : M ≃ₜ M) (P : RealTangentDistribution I M) (x : M)

/-- A native asymptotic leaf's pointed pullback projection is a covering map, and its marked
component is open. -/
private theorem nativeAsymptoticLeaf_pullback_cover
    (D : NativeAsymptoticLeafDatum I f P x)
    {Y : Type*} [TopologicalSpace Y] (p : Y → M) (hp : IsCoveringMap p) :
    letI : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
    ∀ (a : StableAsymptoticLeaf f x) (y : Y) (h : a.val = p y),
      IsCoveringMap (intrinsicCoveringLeafProjection Subtype.val p a y h) ∧
      Function.Surjective (intrinsicCoveringLeafProjection Subtype.val p a y h) ∧
      IsOpen (pathComponent (intrinsicCoveringPullbackPoint Subtype.val p a y h)) := by
  let : TopologicalSpace (StableAsymptoticLeaf f x) := D.topology
  let : ChartedSpace (Fin D.rank → ℝ) (StableAsymptoticLeaf f x) := D.charts
  let : IsManifold (modelWithCornersSelf ℝ (Fin D.rank → ℝ)) ∞
      (StableAsymptoticLeaf f x) := D.smoothAtlas
  have : LocallyPathConnectedSpace (StableAsymptoticLeaf f x) :=
    ChartedSpace.locallyPathConnectedSpace (Fin D.rank → ℝ) (StableAsymptoticLeaf f x)
  have : ConnectedSpace (StableAsymptoticLeaf f x) := D.connected
  have : PathConnectedSpace (StableAsymptoticLeaf f x) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  have hj : Continuous (Subtype.val : StableAsymptoticLeaf f x → M) :=
    D.inclusion_smooth.continuous
  intro a y h
  exact ⟨intrinsicCoveringLeafProjection_isCoveringMap _ p hj hp a y h,
    intrinsicCoveringLeafProjection_surjective _ p hj hp a y h,
    intrinsicCoveringPullbackLeaf_isOpen _ p hj hp a y h⟩

end OriginalNativeLeaf


end HolomorphicAnosov

/-! Holomorphic local lifts give holomorphic inclusions of native pullback leaves and transport
their tangent ranges. -/

open Topology _root_.Topology Set
open scoped ContDiff

namespace HolomorphicAnosov.Theorem12LiftSupport

universe u v w z
variable {d r : ℕ} {X : Type u} {Y : Type v} {L : Type w} {P : Type z}
variable [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
variable [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
variable [TopologicalSpace L] [ChartedSpace (ComplexModel r) L]
variable [TopologicalSpace P] [ChartedSpace (ComplexModel r) P]

/-- A continuous lift of a holomorphic map through a local biholomorphism is holomorphic. -/
private theorem contMDiff_lift
    (p : Y → X) (hp : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (i : P → Y) (hi : Continuous i)
    (hpi : ContMDiff (complexModel r) (complexModel d) ∞ (p ∘ i)) :
    ContMDiff (complexModel r) (complexModel d) ∞ i := by
  intro q
  let hloc := hp (i q)
  have hs : ContMDiffAt (complexModel r) (complexModel d) ∞
      (hloc.localInverse ∘ (p ∘ i)) q :=
    hloc.localInverse_contMDiffAt.comp q (hpi q)
  have heq : (hloc.localInverse ∘ (p ∘ i)) =ᶠ[𝓝 q] i :=
    hloc.localInverse_eventuallyEq_left.comp_tendsto hi.continuousAt
  exact hs.congr_of_eventuallyEq heq.symm

/-- A continuous lift of a holomorphic map through holomorphic covering sheets is holomorphic. -/
private theorem contMDiff_lift_of_native_sheets
    (p : Y → X)
    (hsheets : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    (i : P → Y) (hi : Continuous i)
    (hpi : ContMDiff (complexModel r) (complexModel d) ∞ (p ∘ i)) :
    ContMDiff (complexModel r) (complexModel d) ∞ i := by
  apply contMDiff_lift p _ i hi hpi
  intro y
  obtain ⟨e, hy, hep, he, hei⟩ := hsheets y
  exact ⟨{ toPartialEquiv := e.toPartialEquiv
           open_source := e.open_source
           open_target := e.open_target
           contMDiffOn_toFun := he
           contMDiffOn_invFun := hei }, hy, hep.symm⟩

/-- A continuous lift in a holomorphic commuting square is holomorphic. -/
private theorem contMDiff_lift_commuting
    (p : Y → X) (hp : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (j : L → X) (hj : ContMDiff (complexModel r) (complexModel d) ∞ j)
    (k : P → L) (hk : ContMDiff (complexModel r) (complexModel r) ∞ k)
    (i : P → Y) (hi : Continuous i) (hcomm : p ∘ i = j ∘ k) :
    ContMDiff (complexModel r) (complexModel d) ∞ i := by
  apply contMDiff_lift p hp i hi
  rw [hcomm]
  exact hj.comp hk

/-- The derivatives in a holomorphic commuting square satisfy the corresponding composition
identity. -/
private theorem mfderiv_lift_commuting
    (p : Y → X) (hp : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (j : L → X) (hj : ContMDiff (complexModel r) (complexModel d) ∞ j)
    (k : P → L) (hk : ContMDiff (complexModel r) (complexModel r) ∞ k)
    (i : P → Y) (hi : Continuous i) (hcomm : p ∘ i = j ∘ k) (q : P) :
    (mfderiv (complexModel d) (complexModel d) p (i q)).comp
        (mfderiv (complexModel r) (complexModel d) i q) =
      (mfderiv (complexModel r) (complexModel d) j (k q)).comp
        (mfderiv (complexModel r) (complexModel r) k q) := by
  have hs := contMDiff_lift_commuting p hp j hj k hk i hi hcomm
  rw [← mfderiv_comp q (hp.mdifferentiable (by simp) (i q))
      (hs.mdifferentiable (by simp) q), hcomm,
    mfderiv_comp q (hj.mdifferentiable (by simp) (k q)) (hk.mdifferentiable (by simp) q)]

/-- The covering derivative maps the lifted inclusion's tangent range onto the original leaf tangent
range. -/
private theorem lifted_tangent_range
    (p : Y → X) (hp : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (j : L → X) (hj : ContMDiff (complexModel r) (complexModel d) ∞ j)
    (k : P → L) (hk : IsLocalDiffeomorph (complexModel r) (complexModel r) ∞ k)
    (i : P → Y) (hi : Continuous i) (hcomm : p ∘ i = j ∘ k) (q : P) :
    (LinearMap.range (mfderiv (complexModel r) (complexModel d) i q).toLinearMap).map
        (mfderiv (complexModel d) (complexModel d) p (i q)).toLinearMap =
      LinearMap.range (mfderiv (complexModel r) (complexModel d) j (k q)).toLinearMap := by
  have hder := mfderiv_lift_commuting p hp j hj k hk.contMDiff i hi hcomm q
  have hsurj : Function.Surjective (mfderiv (complexModel r) (complexModel r) k q) :=
    (hk.mfderivToContinuousLinearEquiv (by simp) q).surjective
  ext v
  constructor
  · rintro ⟨u, ⟨t, rfl⟩, rfl⟩
    exact ⟨mfderiv (complexModel r) (complexModel r) k q t,
      (congr_arg (fun A ↦ A t) hder).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := hsurj t
    refine ⟨mfderiv (complexModel r) (complexModel d) i q u, ⟨u, rfl⟩, ?_⟩
    have hh := congr_arg (fun A ↦ A u) hder
    change mfderiv (complexModel d) (complexModel d) p (i q)
      (mfderiv (complexModel r) (complexModel d) i q u) =
      mfderiv (complexModel r) (complexModel d) j (k q)
        (mfderiv (complexModel r) (complexModel r) k q u) at hh
    rw [hu] at hh
    exact hh

/-- The inclusion derivative of a lifted leaf is injective when the base inclusion derivative is
injective. -/
private theorem lifted_mfderiv_injective
    (p : Y → X) (hp : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (j : L → X) (hj : ContMDiff (complexModel r) (complexModel d) ∞ j)
    (hjinj : ∀ l, Function.Injective (mfderiv (complexModel r) (complexModel d) j l))
    (k : P → L) (hk : IsLocalDiffeomorph (complexModel r) (complexModel r) ∞ k)
    (i : P → Y) (hi : Continuous i) (hcomm : p ∘ i = j ∘ k) (q : P) :
    Function.Injective (mfderiv (complexModel r) (complexModel d) i q) := by
  intro u v huv
  have hder := mfderiv_lift_commuting p hp j hj k hk.contMDiff i hi hcomm q
  apply (hk.mfderivToContinuousLinearEquiv (by simp) q).injective
  apply hjinj (k q)
  calc
    _ = mfderiv (complexModel d) (complexModel d) p (i q)
        (mfderiv (complexModel r) (complexModel d) i q u) :=
      (congr_arg (fun A ↦ A u) hder).symm
    _ = mfderiv (complexModel d) (complexModel d) p (i q)
        (mfderiv (complexModel r) (complexModel d) i q v) := congr_arg _ huv
    _ = _ := congr_arg (fun A ↦ A v) hder

/-- The lifted leaf inclusion is a differential immersion. -/
private theorem lifted_isDiffImmersionAt
    (p : Y → X) (hp : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (j : L → X)
    (hj : ∀ l, Manifold.IsImmersionAt (complexModel r) (complexModel d) ∞ j l)
    (k : P → L) (hk : IsLocalDiffeomorph (complexModel r) (complexModel r) ∞ k)
    (i : P → Y) (hi : Continuous i) (hcomm : p ∘ i = j ∘ k) (q : P) :
    IsDiffImmersionAt (complexModel r) (complexModel d) i q := by
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  exact lifted_mfderiv_injective p hp j (fun l ↦ (hj l).contMDiffAt)
    (fun l ↦ (hj l).mfderiv_injective (by simp)) k hk i hi hcomm q


end HolomorphicAnosov.Theorem12LiftSupport
/-! Pointed intrinsic pullback components carry complex leaf structures compatible with their
covering projections. -/
namespace HolomorphicAnosov.LiftedRegularFoliationSupport
open scoped ContDiff
open Set Topology _root_.Topology
noncomputable section
universe u v w
variable {d r : ℕ} {X : Type u} {Y : Type v} {L : Type w}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [ChartedSpace (ComplexModel d) Y]
  [TopologicalSpace L] [T2Space L] [SecondCountableTopology L]
  [ChartedSpace (ComplexModel r) L] [IsManifold (complexModel r) ∞ L]
  [PathConnectedSpace L]

/-- A pointed intrinsic pullback component admits a complex atlas, a locally biholomorphic covering
projection, and a holomorphic inclusion with injective derivative and the marked endpoint range. -/
private theorem pointed_pullback_complex_leaf
    (p : Y → X) (hp : IsCoveringMap p)
    (hplocal : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (j : L → X) (hj : ContMDiff (complexModel r) (complexModel d) ∞ j)
    (hji : ∀ z, Function.Injective (mfderiv (complexModel r) (complexModel d) j z))
    (a : L) (y : Y) (h : j a = p y) :
    ∃ cs : ChartedSpace (ComplexModel r) (IntrinsicCoveringPullbackLeaf j p a y h),
      letI := cs
      IsManifold (complexModel r) ∞ (IntrinsicCoveringPullbackLeaf j p a y h) ∧
      IsCoveringMap (intrinsicCoveringLeafProjection j p a y h) ∧
      Function.Surjective (intrinsicCoveringLeafProjection j p a y h) ∧
      IsLocalDiffeomorph (complexModel r) (complexModel r) ∞
        (intrinsicCoveringLeafProjection j p a y h) ∧
      ContMDiff (complexModel r) (complexModel d) ∞
        (intrinsicCoveringLeafInclusion j p a y h) ∧
      (∀ q, Function.Injective (mfderiv (complexModel r) (complexModel d)
        (intrinsicCoveringLeafInclusion j p a y h) q)) ∧
      Set.range (intrinsicCoveringLeafInclusion j p a y h) =
        liftedIntrinsicLeafRange p j a y ∧
      ∀ q, (LinearMap.range (mfderiv (complexModel r) (complexModel d)
          (intrinsicCoveringLeafInclusion j p a y h) q).toLinearMap).map
          (mfderiv (complexModel d) (complexModel d) p
            (intrinsicCoveringLeafInclusion j p a y h q)).toLinearMap =
        LinearMap.range (mfderiv (complexModel r) (complexModel d) j
          (intrinsicCoveringLeafProjection j p a y h q)).toLinearMap := by
  have : LocallyPathConnectedSpace L :=
    ChartedSpace.locallyPathConnectedSpace (ComplexModel r) L
  have hk := intrinsicCoveringLeafProjection_isCoveringMap j p hj.continuous hp a y h
  have hsurj := intrinsicCoveringLeafProjection_surjective j p hj.continuous hp a y h
  have : SecondCountableTopology (L × Y) := inferInstance
  have : SecondCountableTopology (IntrinsicCoveringPullback j p) := by
    change SecondCountableTopology {z : L × Y // j z.1 = p z.2}
    exact TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (IntrinsicCoveringPullbackLeaf j p a y h) := inferInstance
  obtain ⟨cs, hm, _, hksmooth, hksheets, _⟩ := complex_cover_pullback_atlas (d := r)
    (intrinsicCoveringLeafProjection j p a y h) hk hsurj
  let _ := cs
  let _ := hm
  have hklocal : IsLocalDiffeomorph (complexModel r) (complexModel r) ∞
      (intrinsicCoveringLeafProjection j p a y h) := by
    intro q
    obtain ⟨e, hq, he, hes, heis⟩ := hksheets q
    exact ⟨{ toPartialEquiv := e.toPartialEquiv
             open_source := e.open_source
             open_target := e.open_target
             contMDiffOn_toFun := hes
             contMDiffOn_invFun := heis }, hq, he.symm⟩
  have hcomm : p ∘ (intrinsicCoveringLeafInclusion j p a y h) =
      j ∘ (intrinsicCoveringLeafProjection j p a y h) := by
    funext q
    exact q.val.property.symm
  have hi := Theorem12LiftSupport.contMDiff_lift_commuting p hplocal j hj
    (intrinsicCoveringLeafProjection j p a y h) hksmooth
    (intrinsicCoveringLeafInclusion j p a y h)
    (intrinsicCoveringLeafInclusion j p a y h).continuous hcomm
  refine ⟨cs, hm, hk, hsurj, hklocal, hi, ?_,
    intrinsicCoveringLeafInclusion_range_eq p j a y h, ?_⟩
  · exact Theorem12LiftSupport.lifted_mfderiv_injective p hplocal j hj hji
      (intrinsicCoveringLeafProjection j p a y h) hklocal
      (intrinsicCoveringLeafInclusion j p a y h)
      (intrinsicCoveringLeafInclusion j p a y h).continuous hcomm
  · exact Theorem12LiftSupport.lifted_tangent_range p hplocal j hj
      (intrinsicCoveringLeafProjection j p a y h) hklocal
      (intrinsicCoveringLeafInclusion j p a y h)
      (intrinsicCoveringLeafInclusion j p a y h).continuous hcomm

end
end HolomorphicAnosov.LiftedRegularFoliationSupport

namespace HolomorphicAnosov.LiftedClassCarrier
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w
section ChartTransport
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {C : Type u} {L : Type w} [TopologicalSpace C] [TopologicalSpace L]
  [ChartedSpace E L]

/-- The charted-space structure transported along a homeomorphism. -/
@[local instance_reducible] private def carriedChartedSpace (h : C ≃ₜ L) : ChartedSpace E C where
  atlas := Set.range (fun p : C ↦ h.transOpenPartialHomeomorph (chartAt E (h p)))
  chartAt p := h.transOpenPartialHomeomorph (chartAt E (h p))
  mem_chart_source p := mem_chart_source E (h p)
  chart_mem_atlas p := ⟨p, rfl⟩

omit [NormedSpace ℂ E] in
/-- Transported chart transitions equal the corresponding native chart transitions. -/
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

/-- The transported atlas defines a complex manifold structure. -/
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

/-- The transporting homeomorphism is holomorphic in the transported atlas. -/
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

/-- The inverse transporting homeomorphism is holomorphic. -/
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

/-- The derivative of the transporting homeomorphism is injective. -/
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
end
end HolomorphicAnosov.LiftedClassCarrier

namespace HolomorphicAnosov.LiftedRegularFoliationSupport
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w

/-- The lifted leaf inclusion is injective when the original leaf inclusion is injective. -/
private theorem intrinsicCoveringLeafInclusion_injective
    {X : Type u} {Y : Type v} {L : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X) (hj : Function.Injective j)
    (a : L) (y : Y) (h : j a = p y) :
    Function.Injective (intrinsicCoveringLeafInclusion j p a y h) := by
  intro q q' he
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply hj
    exact q.val.property.trans ((congrArg p he).trans q'.val.property.symm)
  · exact he

section Carrier
variable {Y : Type v} {P : Type w} [TopologicalSpace P]
    (R : Setoid Y) (q : Quotient R) (i : P → Y)
    (hi : Function.Injective i)
    (hclass : ∀ y, Quotient.mk R y = q ↔ y ∈ Set.range i)

/-- The point-preserving map from a pointed pullback component to its lifted partition class. -/
private def componentClassMap (z : P) : IntrinsicFoliationLeaf R q :=
  ⟨i z, (hclass (i z)).mpr ⟨z, rfl⟩⟩

include hi in
omit [TopologicalSpace P] in
/-- The component-to-class map is bijective when its inclusion range equals the class carrier. -/
private theorem componentClassMap_bijective :
    Function.Bijective (componentClassMap R q i hclass) := by
  constructor
  · intro a b hab
    exact hi (congrArg Subtype.val hab)
  · intro z
    obtain ⟨a, ha⟩ := (hclass z.val).mp z.property
    exact ⟨a, Subtype.ext ha⟩

/-- The point-preserving equivalence between a lifted partition class and its pointed pullback
component. -/
private def classComponentEquiv : IntrinsicFoliationLeaf R q ≃ P :=
  (Equiv.ofBijective (componentClassMap R q i hclass)
    (componentClassMap_bijective R q i hi hclass)).symm

omit [TopologicalSpace P] in
private theorem classComponentEquiv_point (z : IntrinsicFoliationLeaf R q) :
    i (classComponentEquiv R q i hi hclass z) = z.val := by
  exact congrArg Subtype.val (Equiv.apply_symm_apply
    (Equiv.ofBijective (componentClassMap R q i hclass)
      (componentClassMap_bijective R q i hi hclass)) z)

/-- The intrinsic topology on a lifted class transported from its pointed pullback component. -/
@[local instance_reducible] private def liftedClassTopology :
    TopologicalSpace (IntrinsicFoliationLeaf R q) :=
  (classComponentEquiv R q i hi hclass).topologicalSpace

/-- The point-preserving homeomorphism between a lifted class and its pointed pullback component. -/
private def classComponentHomeomorph :
    letI := liftedClassTopology R q i hi hclass
    IntrinsicFoliationLeaf R q ≃ₜ P :=
  (classComponentEquiv R q i hi hclass).homeomorph

/-- A lifted class inherits a complex atlas and holomorphic immersive inclusion from its pointed
pullback component. -/
private theorem lifted_class_complex_structure
    {d r : ℕ} [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    [ChartedSpace (ComplexModel r) P] [IsManifold (complexModel r) ∞ P]
    [T2Space P] [SecondCountableTopology P] [ConnectedSpace P]
    (his : ContMDiff (complexModel r) (complexModel d) ∞ i)
    (hdi : ∀ z, Function.Injective (mfderiv (complexModel r) (complexModel d) i z)) :
    letI := liftedClassTopology R q i hi hclass
    ∃ cs : ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf R q),
      letI := cs
      IsManifold (complexModel r) ∞ (IntrinsicFoliationLeaf R q) ∧
      T2Space (IntrinsicFoliationLeaf R q) ∧
      SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
      ConnectedSpace (IntrinsicFoliationLeaf R q) ∧
      ContMDiff (complexModel r) (complexModel d) ∞
        (Subtype.val : IntrinsicFoliationLeaf R q → Y) ∧
      (∀ z, Function.Injective (mfderiv (complexModel r) (complexModel d)
        (Subtype.val : IntrinsicFoliationLeaf R q → Y) z)) ∧
      Set.range (Subtype.val : IntrinsicFoliationLeaf R q → Y) = Set.range i := by
  let _ := liftedClassTopology R q i hi hclass
  let H := classComponentHomeomorph R q i hi hclass
  let _ := LiftedClassCarrier.carriedChartedSpace (E := ComplexModel r) H
  let _ := LiftedClassCarrier.carried_isManifold (E := ComplexModel r) H
  have hs := LiftedClassCarrier.carried_contMDiff (E := ComplexModel r) H
  have hpoint : i ∘ H = (Subtype.val : IntrinsicFoliationLeaf R q → Y) :=
    funext (classComponentEquiv_point R q i hi hclass)
  have hsub : ContMDiff (complexModel r) (complexModel d) ∞
      (Subtype.val : IntrinsicFoliationLeaf R q → Y) := by
    rw [← hpoint]
    exact his.comp hs
  refine ⟨LiftedClassCarrier.carriedChartedSpace (E := ComplexModel r) H,
    inferInstance, H.symm.t2Space, H.secondCountableTopology,
    H.symm.surjective.connectedSpace H.symm.continuous, hsub, ?_, ?_⟩
  · intro z v w hvw
    have hc := mfderiv_comp z ((his (H z)).mdifferentiableAt (by simp))
      ((hs z).mdifferentiableAt (by simp))
    rw [hpoint] at hc
    apply LiftedClassCarrier.carried_mfderiv_injective (E := ComplexModel r) H z
    apply hdi (H z)
    have hv := congrArg (fun D ↦ D v) hc
    have hw := congrArg (fun D ↦ D w) hc
    exact hv.symm.trans (hvw.trans hw)
  · rw [← hpoint, Set.range_comp, H.surjective.range_eq, Set.image_univ]

end Carrier
end
end HolomorphicAnosov.LiftedRegularFoliationSupport

namespace HolomorphicAnosov.LiftedRegularFoliationSupport
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w
variable {d r : ℕ} {X : Type u} {Y : Type v} {L : Type w}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [ChartedSpace (ComplexModel d) Y]
  [TopologicalSpace L] [T2Space L] [SecondCountableTopology L]
  [ChartedSpace (ComplexModel r) L] [IsManifold (complexModel r) ∞ L]
  [PathConnectedSpace L]

/-- A lifted partition class carries the intrinsic complex structure of its marked pullback
component and has inclusion range equal to the marked path-lift range. -/
private theorem pointed_pullback_partition_class
    (p : Y → X) (hp : IsCoveringMap p)
    (hplocal : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (j : L → X) (hj : ContMDiff (complexModel r) (complexModel d) ∞ j)
    (hjinj : Function.Injective j)
    (hji : ∀ z, Function.Injective (mfderiv (complexModel r) (complexModel d) j z))
    (a : L) (y : Y) (h : j a = p y)
    (R : Setoid Y) (q : Quotient R)
    (hclass : ∀ z, Quotient.mk R z = q ↔ z ∈ liftedIntrinsicLeafRange p j a y) :
    ∃ top : TopologicalSpace (IntrinsicFoliationLeaf R q),
      letI := top
      ∃ cs : ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf R q),
        letI := cs
        IsManifold (complexModel r) ∞ (IntrinsicFoliationLeaf R q) ∧
        T2Space (IntrinsicFoliationLeaf R q) ∧
        SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
        ConnectedSpace (IntrinsicFoliationLeaf R q) ∧
        ContMDiff (complexModel r) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf R q → Y) ∧
        (∀ z, Function.Injective (mfderiv (complexModel r) (complexModel d)
          (Subtype.val : IntrinsicFoliationLeaf R q → Y) z)) ∧
        Set.range (Subtype.val : IntrinsicFoliationLeaf R q → Y) =
          liftedIntrinsicLeafRange p j a y ∧
        ∃ H : IntrinsicFoliationLeaf R q ≃ₜ IntrinsicCoveringPullbackLeaf j p a y h,
          ∀ z, intrinsicCoveringLeafInclusion j p a y h (H z) = z.val := by
  obtain ⟨cs, hm, _, _, _, his, hdi, hrange, _⟩ :=
    pointed_pullback_complex_leaf p hp hplocal j hj hji a y h
  let _ := cs
  let _ := hm
  have : SecondCountableTopology (L × Y) := inferInstance
  have : SecondCountableTopology (IntrinsicCoveringPullback j p) := by
    change SecondCountableTopology {z : L × Y // j z.1 = p z.2}
    exact TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (IntrinsicCoveringPullbackLeaf j p a y h) :=
    inferInstance
  have : PathConnectedSpace (IntrinsicCoveringPullbackLeaf j p a y h) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  let i := intrinsicCoveringLeafInclusion j p a y h
  have hinj := intrinsicCoveringLeafInclusion_injective p j hjinj a y h
  have hclass' : ∀ z, Quotient.mk R z = q ↔ z ∈ Set.range i := by
    intro z
    rw [hrange]
    exact hclass z
  let top := liftedClassTopology R q i hinj hclass'
  let _ := top
  obtain ⟨csc, hmc, ht, hsc, hc, hics, hdics, hrc⟩ :=
    lifted_class_complex_structure R q i hinj hclass' his hdi
  refine ⟨top, csc, hmc, ht, hsc, hc, hics, hdics, ?_, ?_⟩
  · exact hrc.trans hrange
  · exact ⟨classComponentHomeomorph R q i hinj hclass',
      classComponentEquiv_point R q i hinj hclass'⟩

end
end HolomorphicAnosov.LiftedRegularFoliationSupport

namespace HolomorphicAnosov.LiftedRegularFoliationSupport
open Set Topology _root_.Topology
noncomputable section
universe u v w z
variable {X : Type u} {Y : Type v} {L : Type w} {D : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L] [TopologicalSpace D]

/-- An entire original native plaque lifted through one covering sheet is an open embedding in the
marked pullback component. -/
private theorem lifted_native_plaque_open_embedding
    (p : Y → X) (j : L → X) (hjinj : Function.Injective j)
    (a : L) (y : Y) (h : j a = p y)
    (g : D → L) (hg : IsOpenEmbedding g)
    (t : D → Y) (ht : Continuous t)
    (hcomm : ∀ z, j (g z) = p (t z))
    (hrange : ∀ z, t z ∈ liftedIntrinsicLeafRange p j a y)
    (S : Set Y) (hS : IsOpen S) (htS : ∀ z, t z ∈ S)
    (hpS : Set.InjOn p S) :
    ∃ l : D → IntrinsicCoveringPullbackLeaf j p a y h,
      IsOpenEmbedding l ∧
      (∀ z, intrinsicCoveringLeafProjection j p a y h (l z) = g z) ∧
      (∀ z, intrinsicCoveringLeafInclusion j p a y h (l z) = t z) := by
  have hmem : ∀ z,
      (⟨(g z, t z), hcomm z⟩ : IntrinsicCoveringPullback j p) ∈
        pathComponent (intrinsicCoveringPullbackPoint j p a y h) := by
    intro z
    obtain ⟨q, hq⟩ := (intrinsicCoveringLeafInclusion_range_eq p j a y h) ▸ hrange z
    have he : q.val = (⟨(g z, t z), hcomm z⟩ : IntrinsicCoveringPullback j p) := by
      apply Subtype.ext
      apply Prod.ext
      · apply hjinj
        exact q.val.property.trans ((congrArg p hq).trans (hcomm z).symm)
      · exact hq
    exact he ▸ q.property
  let l : D → IntrinsicCoveringPullbackLeaf j p a y h :=
    fun z ↦ ⟨⟨(g z, t z), hcomm z⟩, hmem z⟩
  have hl : Continuous l :=
    ((hg.continuous.prodMk ht).subtype_mk (fun z ↦ hcomm z)).subtype_mk hmem
  have hli : Function.Injective l := by
    intro z z' he
    exact hg.injective (congrArg (intrinsicCoveringLeafProjection j p a y h) he)
  have hlo : IsOpenMap l := by
    intro O hO
    have he : l '' O =
        (intrinsicCoveringLeafProjection j p a y h) ⁻¹' (g '' O) ∩
        (intrinsicCoveringLeafInclusion j p a y h) ⁻¹' S := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, htS z⟩
      · rintro ⟨⟨z, hz, hgz⟩, hqS⟩
        refine ⟨z, hz, ?_⟩
        have hqt : intrinsicCoveringLeafInclusion j p a y h q = t z := by
          apply hpS hqS (htS z)
          exact q.val.property.symm.trans ((congrArg j hgz).symm.trans (hcomm z))
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext hgz hqt.symm
    rw [he]
    exact ((hg.isOpenMap O hO).preimage
      (intrinsicCoveringLeafProjection j p a y h).continuous).inter
      (hS.preimage (intrinsicCoveringLeafInclusion j p a y h).continuous)
  exact ⟨l, IsOpenEmbedding.of_continuous_injective_isOpenMap hl hli hlo,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

end
end HolomorphicAnosov.LiftedRegularFoliationSupport

namespace HolomorphicAnosov.LiftedRegularFoliationSupport
open Set Topology _root_.Topology TopologicalSpace
open scoped ContDiff Manifold
noncomputable section
universe u v w
variable {d r c : ℕ} {Y : Type u} {L : Type v} {P : Type w}
  [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
  [TopologicalSpace L] [ChartedSpace (ComplexModel r) L]
  [TopologicalSpace P] [ChartedSpace (ComplexModel r) P]
  [IsManifold (complexModel r) ∞ P]

omit [IsManifold (complexModel r) ∞ P] in
/-- The lifted whole plaque is complex diffeomorphic to its coordinate disk. -/
private theorem lifted_plaque_diffeomorph
    (D : Opens (ComplexModel r))
    (k : P → L) (hk : IsLocalDiffeomorph (complexModel r) (complexModel r) ∞ k)
    (i : P → Y) (hi : ContMDiff (complexModel r) (complexModel d) ∞ i)
    (g : D → L) (hg : ContMDiff (complexModel r) (complexModel r) ∞ g)
    (l : D → P) (hl : IsOpenEmbedding l) (hcomm : k ∘ l = g)
    (e : OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (he : ContMDiffOn (complexModel d)
      ((complexModel r).prod (complexModel c)) ∞ e e.source)
    (b : ComplexModel c) (htarget : ∀ a : D, (a.val, b) ∈ e.target)
    (hvalue : ∀ a, i (l a) = e.symm (a.val, b)) :
    ∃ U : Opens P, (U : Set P) = Set.range l ∧
      ∃ H : Diffeomorph (complexModel r) (complexModel r) D U ∞,
        (∀ a, (H a).val = l a) ∧
        ∀ a, i ((H a).val) = e.symm (a.val, b) := by
  let U : Opens P := ⟨Set.range l, hl.isOpen_range⟩
  let H : D ≃ₜ U := hl.isEmbedding.toHomeomorph
  have hH : ∀ a, (H a).val = l a := fun _ ↦ rfl
  have hls : ContMDiff (complexModel r) (complexModel r) ∞ l :=
    Theorem12LiftSupport.contMDiff_lift k hk l hl.continuous (hcomm ▸ hg)
  have hHs : ContMDiff (complexModel r) (complexModel r) ∞ H :=
    (ContMDiff.subtypeVal_comp_iff U H).mp hls
  have hback : ∀ z : U, l (H.symm z) = z.val := by
    intro z
    exact (hH (H.symm z)).symm.trans (congrArg Subtype.val (H.apply_symm_apply z))
  have hdomain : ∀ z : U, i z.val ∈ e.source := by
    intro z
    rw [← hback z, hvalue (H.symm z)]
    exact e.map_target (htarget (H.symm z))
  have hh : ContMDiff (complexModel r) ((complexModel r).prod (complexModel c)) ∞
      (fun z : U ↦ e (i z.val)) :=
    he.comp_contMDiff (hi.comp contMDiff_subtype_val) hdomain
  have hhp : ContMDiff (complexModel r) (complexModel r) ∞
      (fun z : U ↦ (e (i z.val)).1) := by
    exact hh.fst
  have hHis : ContMDiff (complexModel r) (complexModel r) ∞ H.symm := by
    apply (ContMDiff.subtypeVal_comp_iff D H.symm).mp
    apply hhp.congr
    intro z
    change (H.symm z).val = (e (i z.val)).1
    rw [← hback z, hvalue (H.symm z), e.right_inv (htarget (H.symm z))]
  let Hd : Diffeomorph (complexModel r) (complexModel r) D U ∞ :=
    { H.toEquiv with contMDiff_toFun := hHs, contMDiff_invFun := hHis }
  exact ⟨U, rfl, Hd, hH, fun a ↦ (congrArg i (hH a)).trans (hvalue a)⟩

end
end HolomorphicAnosov.LiftedRegularFoliationSupport

namespace HolomorphicAnosov.LiftedRegularFoliationSupport
open Set Topology _root_.Topology
noncomputable section
universe u v w

/-- A covering family of intrinsically open whole plaques generates the native class topology. -/
private theorem topology_generated_by_whole_plaques
    {Y : Type u} [TopologicalSpace Y] {J : Type v} {r c : ℕ}
    (R : Setoid Y) (q : Quotient R)
    [TopologicalSpace (IntrinsicFoliationLeaf R q)]
    (box : J → OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (htarget : ∀ i, (box i).target =
      (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
        (complexFoliationDisk c : Set (ComplexModel c)))
    (hcover : ∀ y, ∃ i, y ∈ (box i).source)
    (label : J → complexFoliationDisk c → Quotient R)
    (hlabel : ∀ i (a : complexFoliationDisk r) (b : complexFoliationDisk c),
      Quotient.mk R ((box i).symm (a.val, b.val)) = label i b)
    (hopen : ∀ i b (h : label i b = q), IsOpenEmbedding
      (fun a : complexFoliationDisk r ↦
        (⟨(box i).symm (a.val, b.val), (hlabel i a b).trans h⟩ :
          IntrinsicFoliationLeaf R q)))
    (W : Set (IntrinsicFoliationLeaf R q)) :
    IsOpen W ↔ ∀ i b (h : label i b = q),
      IsOpen ((fun a : complexFoliationDisk r ↦
        (⟨(box i).symm (a.val, b.val), (hlabel i a b).trans h⟩ :
          IntrinsicFoliationLeaf R q)) ⁻¹' W) := by
  constructor
  · intro hW i b h
    exact hW.preimage (hopen i b h).continuous
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
    let f : complexFoliationDisk r → IntrinsicFoliationLeaf R q :=
      fun a ↦ ⟨(box i).symm (a.val, b.val), (hlabel i a b).trans hl⟩
    have hfa : f a = z := Subtype.ext hab
    have hzimage : z ∈ f '' (f ⁻¹' W) := ⟨a, by
      change f a ∈ W
      rw [hfa]
      exact hz, hfa⟩
    apply Filter.mem_of_superset (((hopen i b hl).isOpenMap _ (hW i b hl)).mem_nhds hzimage)
    rintro y ⟨v, hv, rfl⟩
    exact hv

end
end HolomorphicAnosov.LiftedRegularFoliationSupport

namespace HolomorphicAnosov.LiftedRegularFoliationSupport
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w
variable {d r c : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [ChartedSpace (ComplexModel d) Y]

/-- Lifted classes of a regular holomorphic foliation carry intrinsic complex leaf structures with
the marked path-lift ranges. -/
private theorem original_foliation_lifted_class_structure
    (F : RegularHolomorphicFoliation.{u,w} d r c X)
    (p : Y → X) (hp : IsCoveringMap p)
    (hplocal : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (R : Setoid Y) (q : Quotient R) (y : Y)
    (hclass : ∀ z, Quotient.mk R z = q ↔
      z ∈ liftedIntrinsicLeafRange p (Subtype.val : F.Leaf (p y) → X)
        ⟨p y, rfl⟩ y) :
    ∃ top : TopologicalSpace (IntrinsicFoliationLeaf R q),
      letI := top
      ∃ cs : ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf R q),
        letI := cs
        IsManifold (complexModel r) ∞ (IntrinsicFoliationLeaf R q) ∧
        T2Space (IntrinsicFoliationLeaf R q) ∧
        SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
        ConnectedSpace (IntrinsicFoliationLeaf R q) ∧
        ContMDiff (complexModel r) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf R q → Y) ∧
        (∀ z, Function.Injective (mfderiv (complexModel r) (complexModel d)
          (Subtype.val : IntrinsicFoliationLeaf R q → Y) z)) ∧
        Set.range (Subtype.val : IntrinsicFoliationLeaf R q → Y) =
          liftedIntrinsicLeafRange p (Subtype.val : F.Leaf (p y) → X)
            ⟨p y, rfl⟩ y ∧
        ∃ H : IntrinsicFoliationLeaf R q ≃ₜ
            IntrinsicCoveringPullbackLeaf (Subtype.val : F.Leaf (p y) → X)
              p ⟨p y, rfl⟩ y rfl,
          ∀ z, intrinsicCoveringLeafInclusion (Subtype.val : F.Leaf (p y) → X)
            p ⟨p y, rfl⟩ y rfl (H z) = z.val := by
  have : T2Space (F.Leaf (p y)) := F.leafHausdorff _
  have : SecondCountableTopology (F.Leaf (p y)) := F.leafCountable _
  have : PathConnectedSpace (F.Leaf (p y)) :=
    regularHolomorphicFoliation_leaf_pathConnected F (p y)
  exact pointed_pullback_partition_class p hp hplocal
    (Subtype.val : F.Leaf (p y) → X) (F.inclusion_holomorphic _)
    Subtype.val_injective (F.inclusion_immersion _) ⟨p y, rfl⟩ y rfl R q hclass

end
end HolomorphicAnosov.LiftedRegularFoliationSupport


/-! The derivative of the native leaf inclusion identifies foliation tangents with horizontal plaque
directions. (Nisoli, Defs 1.1.1–1.1.3, pp.9–10) -/

open Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.RegularHolomorphicFoliation

noncomputable section

/-- The inclusion of an open subset has bijective manifold derivative. -/
private theorem opens_val_mfderiv_bijective
    {A H N : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ A H) (U : Opens N) (x : U) :
    Function.Bijective (mfderiv I I (Subtype.val : U → N) x) := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨x⟩
  have he : e.MDifferentiable I I := by
    constructor
    · exact (contMDiff_subtype_val (I := I) (n := ∞)).mdifferentiable
        (by simp) |>.mdifferentiableOn
    · intro y hy
      have hy' : y ∈ (U : Set N) := by simpa [e] using hy
      have hi : ContMDiffWithinAt I I ∞ (Subtype.val ∘ e.symm) (U : Set N) y :=
        contMDiffWithinAt_id.congr_of_mem (fun z hz ↦ e.right_inv (by simpa [e] using hz)) hy'
      have hinv := (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm (U : Set N) y).mp hi
      simpa [e] using hinv.mdifferentiableWithinAt (by simp)
  exact he.mfderiv_bijective (by simp [e])


/-- The chart derivative maps the leaf-inclusion derivative range onto the horizontal subspace when
its plaque parametrization agrees with the chart slice. -/
private theorem plaque_chart_derivative_range
    {E G A H K L N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace L] [ChartedSpace K L]
    [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ A H) (J : ModelWithCorners ℂ E K)
    (U : Opens E) (V : Opens L)
    (e : Diffeomorph 𝓘(ℂ, E) J U V ∞)
    (j : L → N) (hj : ContMDiff J I ∞ j)
    (c : OpenPartialHomeomorph N (E × G))
    (hc : c.MDifferentiable I 𝓘(ℂ, E × G))
    (b : G) (hchart : ∀ u : U, c (j (e u).val) = (u.val, b))
    (a : U) (ha : j (e a).val ∈ c.source) :
    ((mfderiv J I j (e a).val).range).map
      (mfderiv I 𝓘(ℂ, E × G) c (j (e a).val)).toLinearMap =
        (ContinuousLinearMap.inl ℂ E G).toLinearMap.range := by
  let h : U → L := fun u ↦ (e u).val
  have he : MDifferentiable 𝓘(ℂ, E) J e := e.mdifferentiable (by simp)
  have hv : MDifferentiable J J (Subtype.val : V → L) :=
    (contMDiff_subtype_val (I := J) (n := ∞)).mdifferentiable (by simp)
  have hh : MDifferentiable 𝓘(ℂ, E) J h := hv.comp he
  let Dh := mfderiv 𝓘(ℂ, E) J h a
  let Da := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (Subtype.val : U → E) a
  let Dj := mfderiv J I j (h a)
  let Dc := mfderiv I 𝓘(ℂ, E × G) c (j (h a))
  have hDh : Function.Surjective Dh := by
    have heonto := (e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_surjective
      (x := a) (by simp)
    have hVonto := (opens_val_mfderiv_bijective J V (e a)).surjective
    change Function.Surjective (mfderiv 𝓘(ℂ, E) J ((Subtype.val : V → L) ∘ e) a)
    rw [mfderiv_comp a (hv (e a)) (he a)]
    exact hVonto.comp heonto
  have hDa : Function.Surjective Da :=
    (opens_val_mfderiv_bijective 𝓘(ℂ, E) U a).surjective
  let k : E → E × G := fun u ↦ (u, b)
  have hk : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E × G) k a.val :=
    (hasFDerivAt_prodMk_left (𝕜 := ℂ) a.val b).differentiableAt.mdifferentiableAt
  have hcoord : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E × G) (fun u : U ↦ (u.val, b)) a =
      (ContinuousLinearMap.inl ℂ E G).comp Da := by
    change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E × G) (k ∘ Subtype.val) a = _
    rw [mfderiv_comp a hk ((contMDiff_subtype_val (I := 𝓘(ℂ, E))
      (U := U) (n := ∞)).mdifferentiable (by simp) a), mfderiv_eq_fderiv]
    congr 1
    exact (hasFDerivAt_prodMk_left (𝕜 := ℂ) a.val b).fderiv
  have hchain : Dc.comp (Dj.comp Dh) = (ContinuousLinearMap.inl ℂ E G).comp Da := by
    rw [← mfderiv_comp a ((hj.mdifferentiable (by simp)) (h a)) (hh a)]
    dsimp only [Dc]
    erw [← mfderiv_comp a (hc.mdifferentiableAt ha)
      (((hj.mdifferentiable (by simp)).comp hh) a)]
    have heq : (c ∘ (j ∘ h)) = (fun u : U ↦ (u.val, b)) := funext hchart
    rw [heq]
    exact hcoord
  change (Dj.range).map Dc.toLinearMap = _
  ext w
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    obtain ⟨t, rfl⟩ := hDh u
    refine ⟨Da t, ?_⟩
    exact (congrArg (fun D : TangentSpace 𝓘(ℂ, E) a →L[ℂ] (E × G) ↦ D t) hchain).symm
  · rintro ⟨v, rfl⟩
    obtain ⟨t, ht⟩ := hDa v
    refine ⟨Dj (Dh t), ⟨Dh t, rfl⟩, ?_⟩
    exact (congrArg (fun D : TangentSpace 𝓘(ℂ, E) a →L[ℂ] (E × G) ↦ D t) hchain).trans
      (congrArg (ContinuousLinearMap.inl ℂ E G) ht)


universe u v

variable {d r c : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]

/-- The plaque chart maps the native inclusion's derivative range onto the horizontal coordinate
range. (Nisoli, Defs 1.1.1–1.1.3, pp.9–10) -/
private theorem plaque_inclusion_map_box
    (F : RegularHolomorphicFoliation.{u,v} d r c M)
    (i : F.boxIndex) (a : complexFoliationDisk r) (b : complexFoliationDisk c) :
    letI := F.leafTopology (F.label i b)
    letI := F.leafCharts (F.label i b)
    ((mfderiv (complexModel r) (complexModel d)
      (fun t : IntrinsicFoliationLeaf F.partition (F.label i b) ↦ t.val)
      (F.plaqueChart i b a).val).range).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
        (F.box i) (F.plaqueChart i b a).val.val).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range := by
  let : TopologicalSpace (IntrinsicFoliationLeaf F.partition (F.label i b)) :=
    F.leafTopology (F.label i b)
  let : ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf F.partition (F.label i b)) :=
    F.leafCharts (F.label i b)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hf := F.box_holomorphic i
  have hi := F.box_inverse_holomorphic i
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hf hi
  let : ChartedSpace (ModelProd (ComplexModel r) (ComplexModel c))
      (ComplexModel r × ComplexModel c) := chartedSpaceSelf _
  have hc : (F.box i).MDifferentiable (complexModel d)
      𝓘(ℂ, ComplexModel r × ComplexModel c) :=
    ⟨hf.mdifferentiableOn (by simp), hi.mdifferentiableOn (by simp)⟩
  apply plaque_chart_derivative_range (complexModel d) (complexModel r)
    (complexFoliationDisk r) (F.plaque i b) (F.plaqueChart i b)
    (fun t : IntrinsicFoliationLeaf F.partition (F.label i b) ↦ t.val)
    (F.inclusion_holomorphic (F.label i b)) (F.box i) hc b.val
  · intro z
    rw [F.plaqueChart_eq]
    apply (F.box i).right_inv
    rw [F.box_target]
    exact ⟨z.property, b.property⟩
  · rw [F.plaqueChart_eq]
    apply (F.box i).map_target
    rw [F.box_target]
    exact ⟨a.property, b.property⟩

/-- Each intrinsic partition-class leaf has the prescribed tangent distribution when the ambient
boxes flatten that distribution. (Nisoli, Defs 1.1.1–1.1.3, pp.9–10) -/
private theorem intrinsic_inclusion_range_eq
    (F : RegularHolomorphicFoliation.{u,v} d r c M)
    (P : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hflat : ∀ i x, x ∈ (F.box i).source →
      (P x).map (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
        (F.box i) x).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (q : Quotient F.partition) (t : IntrinsicFoliationLeaf F.partition q) :
    letI := F.leafTopology q
    letI := F.leafCharts q
    (mfderiv (complexModel r) (complexModel d)
      (fun z : IntrinsicFoliationLeaf F.partition q ↦ z.val) t).range = P t.val := by
  obtain ⟨i, hx⟩ := F.cover t.val
  have htarget := (F.box i).map_source hx
  rw [F.box_target] at htarget
  let a : complexFoliationDisk r := ⟨((F.box i) t.val).1, htarget.1⟩
  let b : complexFoliationDisk c := ⟨((F.box i) t.val).2, htarget.2⟩
  have hback : (F.box i).symm (a.val, b.val) = t.val := (F.box i).left_inv hx
  clear_value a b
  have hlabel : F.label i b = q := by
    rw [← F.label_eq i a b, hback]
    exact t.property
  subst q
  let : TopologicalSpace (IntrinsicFoliationLeaf F.partition (F.label i b)) :=
    F.leafTopology (F.label i b)
  let : ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf F.partition (F.label i b)) :=
    F.leafCharts (F.label i b)
  have hp : (F.plaqueChart i b a).val = t :=
    Subtype.ext ((F.plaqueChart_eq i a b).trans hback)
  have hr := plaque_inclusion_map_box F i a b
  rw [hp] at hr
  have hc : (F.box i).MDifferentiable (complexModel d)
      ((complexModel r).prod (complexModel c)) :=
    ⟨(F.box_holomorphic i).mdifferentiableOn (by simp),
      (F.box_inverse_holomorphic i).mdifferentiableOn (by simp)⟩
  exact (Submodule.map_injective_of_injective (hc.mfderiv_injective hx))
    (hr.trans (hflat i t.val hx).symm)

/-- A regular foliation's tangent field equals the distribution flattened by its boxes. (Nisoli,
pp.9–10) -/
private theorem tangent_eq_of_box_flattening
    (F : RegularHolomorphicFoliation.{u,v} d r c M)
    (P : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hflat : ∀ i x, x ∈ (F.box i).source →
      (P x).map (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
        (F.box i) x).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (x : M) : F.tangent x = P x :=
  intrinsic_inclusion_range_eq F P hflat (Quotient.mk F.partition x) ⟨x, rfl⟩

/-- A locally biholomorphic projection maps the foliation tangent onto the base distribution when
its boxes flatten the pullback distribution. (Nisoli, pp.9–10) -/
private theorem tangent_map_eq_of_pullback_box_flattening
    {A H N : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ A H)
    (F : RegularHolomorphicFoliation.{u,v} d r c M)
    (p : M → N) (hp : IsLocalDiffeomorph (complexModel d) I ∞ p)
    (P : ∀ x : N, Submodule ℂ (TangentSpace I x))
    (hflat : ∀ i y, y ∈ (F.box i).source →
      ((P (p y)).comap (mfderiv (complexModel d) I p y).toLinearMap).map
        (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
          (F.box i) y).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (y : M) :
    (F.tangent y).map (mfderiv (complexModel d) I p y).toLinearMap = P (p y) := by
  rw [tangent_eq_of_box_flattening F
    (fun z ↦ (P (p z)).comap (mfderiv (complexModel d) I p z).toLinearMap) hflat y]
  apply Submodule.map_comap_eq_self
  intro v hv
  exact (hp.mfderivToContinuousLinearEquiv (by simp) y).surjective v


end
end HolomorphicAnosov.RegularHolomorphicFoliation


namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w z

/-- Complementary holomorphic tangent bundles and native real leaves define a downstairs regular
foliation with a pointed native leaf identification. (Nisoli, pp.9–10; HPS, §7, pp.115–116) -/
private theorem original_regular_foliation
    {d r c : ℕ} {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [IsManifold (realModel d) ∞ X]
    (f : X ≃ₜ X) (hdim : d = r + c)
    (P R : ∀ q : X, Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P) (hR : IsHolomorphicTangentSubbundle c R)
    (hcompl : ∀ q, IsCompl (P q) (R q))
    (Q T : RealTangentDistribution (realModel d) X)
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (hRealR : ∀ q, ((R q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = T q)
    (DP : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (DR : ∀ b, NativeAsymptoticLeafDatum (realModel d) f.symm T b) :
    ∃ F : RegularHolomorphicFoliation.{u,u} d r c X,
      (∀ i x, x ∈ (F.box i).source → (P x).map
        (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
          (F.box i) x).toLinearMap =
        (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range) ∧
      (∀ x, F.tangent x = P x) ∧
      ∀ x : X, letI := F.leafTopology (Quotient.mk F.partition x)
        letI := (DP x).topology
        ∃ H : F.Leaf x ≃ₜ StableAsymptoticLeaf f x,
          (∀ z, (H z).val = z.val) ∧
          (∀ z, (H.symm z).val = z.val) ∧
          H ⟨x, rfl⟩ = ⟨x, (NativeBoxPartition.asymptoticSetoid f).refl x⟩ := by
  obtain ⟨box, hx, ht, hb, hbi, hf⟩ :=
    Theorem12NativeHolomorphicBoxes.exists_native_holomorphic_unit_box_cover_product_model
      f P R hP hR hcompl Q T hRealP hRealR DP DR
  obtain ⟨F, ⟨e, he⟩, _, hn⟩ :=
    NativeLeafRebase.original_tangent_regular_foliation_native_homeomorph
      f Q DP box hdim P hP hRealP ht (fun x ↦ ⟨x, hx x⟩) hb hbi hf
  have hflatF : ∀ i x, x ∈ (F.box i).source → (P x).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
        (F.box i) x).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range := by
    intro i z hz
    obtain ⟨j,rfl⟩ := e.surjective i
    rw [he j]
    exact hf j z (by simpa only [he j] using hz)
  exact ⟨F,hflatF,fun x ↦
    RegularHolomorphicFoliation.tangent_eq_of_box_flattening F P hflatF x,hn⟩

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly


namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w

/-- Sheet-restricted lifted boxes define a partition with intrinsic complex classes equal to the
marked downstairs path-lift ranges. (Hatcher, pp.60–62; Bredon, II.14; Nisoli, pp.9–10) -/
private theorem lifted_partition_and_classes
    {d r c : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (ComplexModel d) Y]
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (hp : IsCoveringMap p)
    (hplocal : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (hsheets : ∀ y : Y, ∃ s : OpenPartialHomeomorph Y X,
      y ∈ s.source ∧ EqOn s p s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target) :
    ∃ (B : Y → OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
      (R : Setoid Y),
      (∀ y, y ∈ (B y).source) ∧
      (∀ y, (B y).target = (complexFoliationDisk r : Set _) ×ˢ
        (complexFoliationDisk c : Set _)) ∧
      (∀ y, ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
        ∞ (B y) (B y).source) ∧
      (∀ y, ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
        ∞ (B y).symm (B y).target) ∧
      (∀ y z, R y z ↔ Relation.EqvGen (LiftedPlaquePartition.rawPlaqueStep B) y z) ∧
      (∀ y z, R y z ↔ z ∈ liftedIntrinsicLeafRange p
        (Subtype.val : F.Leaf (p y) → X) ⟨p y, rfl⟩ y) ∧
      ∀ q : Quotient R,
        ∃ top : TopologicalSpace (IntrinsicFoliationLeaf R q), letI := top
        ∃ cs : ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf R q), letI := cs
          IsManifold (complexModel r) ∞ (IntrinsicFoliationLeaf R q) ∧
          T2Space (IntrinsicFoliationLeaf R q) ∧
          SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
          ConnectedSpace (IntrinsicFoliationLeaf R q) ∧
          ContMDiff (complexModel r) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf R q → Y) ∧
          (∀ z, Function.Injective (mfderiv (complexModel r) (complexModel d)
            (Subtype.val : IntrinsicFoliationLeaf R q → Y) z)) ∧
          Set.range (Subtype.val : IntrinsicFoliationLeaf R q → Y) =
            liftedIntrinsicLeafRange p (Subtype.val : F.Leaf (p q.out) → X)
              ⟨p q.out, rfl⟩ q.out ∧
          ∃ H : IntrinsicFoliationLeaf R q ≃ₜ IntrinsicCoveringPullbackLeaf
              (Subtype.val : F.Leaf (p q.out) → X) p ⟨p q.out, rfl⟩ q.out rfl,
            ∀ z, intrinsicCoveringLeafInclusion
              (Subtype.val : F.Leaf (p q.out) → X) p ⟨p q.out, rfl⟩ q.out rfl (H z) = z.val := by
  classical
  obtain ⟨B, hb⟩ := Theorem12CoverBoxes.exists_lifted_unit_box_family F p hsheets
  choose i s ρ hρ hdata using fun y ↦ (hb y).2.2.2.2
  have htarget : ∀ y, (B y).target = (complexFoliationDisk r : Set _) ×ˢ
      (complexFoliationDisk c : Set _) := fun y ↦ (hb y).2.1
  let center := fun y ↦ F.box (i y) (p y)
  have hsrc : ∀ y, (B y).source ⊆ (s y).source := by
    intro y z hz
    rw [(hdata y).2.2.2.2.1] at hz
    exact hz.1
  have hsp : ∀ y, EqOn (s y) p (s y).source := fun y ↦ (hdata y).2.1
  have hcoord : ∀ y, ∀ a : complexFoliationDisk r, ∀ b : complexFoliationDisk c,
      center y + (ρ y : ℂ) • (a.val, b.val) ∈ (F.box (i y)).target := by
    intro y a b
    have h := (hdata y).2.2.2.2.2.2.2.2.2.2.2.2 ⟨(a.val,b.val), ⟨a.property,b.property⟩,rfl⟩
    exact h.1
  have hproj : ∀ y, ∀ a : complexFoliationDisk r, ∀ b : complexFoliationDisk c,
      p ((B y).symm (a.val,b.val)) =
        (F.box (i y)).symm (center y + (ρ y : ℂ) • (a.val,b.val)) := by
    intro y a b
    exact (hdata y).2.2.2.2.2.2.2.2.2.1 (a.val,b.val) (by rw [htarget]; exact ⟨a.property,b.property⟩)
  let R := Relation.EqvGen.setoid (LiftedPlaquePartition.rawPlaqueStep B)
  have hr : ∀ y z, R y z ↔ z ∈ liftedIntrinsicLeafRange p
      (Subtype.val : F.Leaf (p y) → X) ⟨p y,rfl⟩ y := by
    intro y z
    exact LiftedPlaquePartition.raw_affine_partition_iff_lifted_range F p B
      (fun y ↦ ⟨y,(hb y).1⟩) htarget i s hsrc hsp center ρ hρ hcoord hproj y z
  refine ⟨B,R,fun y ↦ (hb y).1,htarget,fun y ↦ (hb y).2.2.1,
    fun y ↦ (hb y).2.2.2.1,fun _ _ ↦ Iff.rfl,hr,?_⟩
  intro q
  apply LiftedRegularFoliationSupport.original_foliation_lifted_class_structure F p hp
    hplocal R q q.out
  intro z
  have he : Quotient.mk R z = q ↔ R q.out z := by
    constructor
    · intro hz
      exact R.symm (Quotient.exact (hz.trans (Quotient.out_eq q).symm))
    · intro hz
      exact (Quotient.sound (R.symm hz)).trans (Quotient.out_eq q)
  exact he.trans (hr q.out z)

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly


namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w z

/-- An entire lifted slice is an open embedding in the marked pullback class topology. (Nisoli,
pp.9–10) -/
private theorem class_whole_slice_isOpenEmbedding
    {d r c : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y]
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (R : Setoid Y) (q : Quotient R)
    [TopologicalSpace (IntrinsicFoliationLeaf R q)] (y : Y)
    (H : IntrinsicFoliationLeaf R q ≃ₜ IntrinsicCoveringPullbackLeaf
      (Subtype.val : F.Leaf (p y) → X) p ⟨p y,rfl⟩ y rfl)
    (hH : ∀ z, intrinsicCoveringLeafInclusion
      (Subtype.val : F.Leaf (p y) → X) p ⟨p y,rfl⟩ y rfl (H z) = z.val)
    (B : OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (i : F.boxIndex) (A : ComplexModel r ≃ₜ ComplexModel r)
    (K : ComplexModel c ≃ₜ ComplexModel c)
    (hcoord : ∀ a : complexFoliationDisk r, ∀ b : complexFoliationDisk c,
      (A a.val,K b.val) ∈ (F.box i).target)
    (hproj : ∀ a : complexFoliationDisk r, ∀ b : complexFoliationDisk c,
      p (B.symm (a.val,b.val)) = (F.box i).symm (A a.val,K b.val))
    (s : OpenPartialHomeomorph Y X) (hs : B.source ⊆ s.source)
    (hsp : EqOn s p s.source)
    (htarget : B.target = (complexFoliationDisk r : Set _) ×ˢ
      (complexFoliationDisk c : Set _))
    (b : complexFoliationDisk c)
    (hlabel : ∀ a : complexFoliationDisk r, Quotient.mk R (B.symm (a.val,b.val)) = q) :
    IsOpenEmbedding (fun a : complexFoliationDisk r ↦
      (⟨B.symm (a.val,b.val), hlabel a⟩ : IntrinsicFoliationLeaf R q)) := by
  classical
  let a₀ : complexFoliationDisk r := ⟨0, Metric.mem_ball_self (by norm_num)⟩
  let t : complexFoliationDisk r → IntrinsicFoliationLeaf R q :=
    fun a ↦ ⟨B.symm (a.val,b.val),hlabel a⟩
  let Q := H (t a₀)
  have hQ : B.symm (a₀.val,b.val) = Q.val.val.2 := (hH (t a₀)).symm
  obtain ⟨φ,hφ,hφval,_⟩ := LiftedPlaquePartition.original_raw_slice F p y B i A K
    hcoord hproj b a₀ Q.val hQ
  have htarget' : ∀ a : complexFoliationDisk r, (a.val,b.val) ∈ B.target := by
    intro a
    rw [htarget]
    exact ⟨a.property,b.property⟩
  have ht : Continuous (fun a : complexFoliationDisk r ↦ B.symm (a.val,b.val)) :=
    B.continuousOn_invFun.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) htarget'
  have hrange : ∀ a : complexFoliationDisk r, B.symm (a.val,b.val) ∈
      liftedIntrinsicLeafRange p (Subtype.val : F.Leaf (p y) → X) ⟨p y,rfl⟩ y := by
    intro a
    rw [← intrinsicCoveringLeafInclusion_range_eq
      p (Subtype.val : F.Leaf (p y) → X) ⟨p y,rfl⟩ y rfl]
    exact ⟨H (t a), hH (t a)⟩
  obtain ⟨l,hl,_,hli⟩ := LiftedRegularFoliationSupport.lifted_native_plaque_open_embedding
    p (Subtype.val : F.Leaf (p y) → X) Subtype.val_injective ⟨p y,rfl⟩ y rfl
    φ hφ (fun a ↦ B.symm (a.val,b.val)) ht hφval hrange s.source s.open_source
    (fun a ↦ hs (B.map_target (htarget' a))) (by
      intro z hz z' hz' hzz
      exact s.injOn hz hz' ((hsp hz).trans (hzz.trans (hsp hz').symm)))
  have hlift : (fun a ↦ H.symm (l a)) = t := by
    funext a
    apply Subtype.ext
    have hv := hH (H.symm (l a))
    rw [H.apply_symm_apply] at hv
    exact hv.symm.trans (hli a)
  change IsOpenEmbedding t
  rw [← hlift]
  exact H.symm.isOpenEmbedding.comp hl

/-- An open embedding of a whole slice gives local coordinate charts with the ambient inverse-slice
identities. -/
private theorem local_chart_of_whole_slice
    {r c : ℕ} {Y : Type u} [TopologicalSpace Y]
    {L : Type v} [TopologicalSpace L] (j : L → Y)
    (B : OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (b : complexFoliationDisk c)
    (t : complexFoliationDisk r → L) (ht : IsOpenEmbedding t)
    (hvalue : ∀ a, j (t a) = B.symm (a.val,b.val))
    (htarget : B.target = (complexFoliationDisk r : Set _) ×ˢ
      (complexFoliationDisk c : Set _)) (a : complexFoliationDisk r) :
    ∃ k : OpenPartialHomeomorph L (ComplexModel r),
      t a ∈ k.source ∧
      (∀ z ∈ k.source, j z ∈ B.source ∧ k z = (B (j z)).1) ∧
      ∀ u ∈ k.target, (u,b.val) ∈ B.target ∧ j (k.symm u) = B.symm (u,b.val) := by
  classical
  have : Nonempty (complexFoliationDisk r) := ⟨a⟩
  let e := ht.toOpenPartialHomeomorph t
  let D := (complexFoliationDisk r).openPartialHomeomorphSubtypeCoe inferInstance
  let k := e.symm.trans D
  have he : ∀ a, e a = t a := fun _ ↦ rfl
  have hinv : ∀ a, e.symm (t a) = a := fun a ↦ e.left_inv (Set.mem_univ a)
  have hDsource : D.source = Set.univ := rfl
  have hDtarget : D.target = (complexFoliationDisk r : Set _) := by
    simp [D]
  refine ⟨k, ?_, ?_, ?_⟩
  · change t a ∈ e.target ∩ e.symm ⁻¹' D.source
    exact ⟨by simp [e], by simp [hDsource]⟩
  · intro z hz
    have hz' : z ∈ e.target := hz.1
    have hv : t (e.symm z) = z := e.right_inv hz'
    have ht' : ((e.symm z).val,b.val) ∈ B.target := by
      rw [htarget]; exact ⟨(e.symm z).property,b.property⟩
    refine ⟨by rw [← hv,hvalue]; exact B.map_target ht', ?_⟩
    change (e.symm z).val = (B (j z)).1
    rw [← hv,hvalue,B.right_inv ht',hinv]
  · intro u hu
    have huD : u ∈ D.target := hu.1
    have hu' : u ∈ (complexFoliationDisk r : Set _) := hDtarget ▸ huD
    have hDu : (D.symm u).val = u := D.right_inv huD
    refine ⟨by rw [htarget]; exact ⟨hu',b.property⟩, ?_⟩
    change j (t (D.symm u)) = _
    rw [hvalue,hDu]

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly


namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology TopologicalSpace
open scoped ContDiff Manifold
noncomputable section
universe u v

/-- A partition with intrinsic complex class topologies and compatible slice charts defines a
regular holomorphic foliation. (Nisoli, Defs 1.1.1–1.1.3, pp.9–10) -/
private theorem regular_foliation_of_class_charts
    {d r c : ℕ} {M : Type u} {J : Type v}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (box : J → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c))
    (hdim : d = r + c)
    (P : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (htarget : ∀ i, (box i).target = (complexFoliationDisk r : Set _) ×ˢ
      (complexFoliationDisk c : Set _))
    (hcover : ∀ z : M, ∃ i, z ∈ (box i).source)
    (he : ∀ i, ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ (box i) (box i).source)
    (hei : ∀ i, ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ (box i).symm (box i).target)
    (hflat : ∀ i x, x ∈ (box i).source → (P x).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
        (box i) x).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (R : Setoid M)
    (hgenerated : ∀ x y, R x y ↔ Relation.EqvGen
      (LiftedPlaquePartition.rawPlaqueStep box) x y)
    (LT : ∀ q : Quotient R, TopologicalSpace (IntrinsicFoliationLeaf R q))
    (label : J → complexFoliationDisk c → Quotient R)
    (hlabel : ∀ i (a : complexFoliationDisk r) (b : complexFoliationDisk c),
      Quotient.mk R ((box i).symm (a.val,b.val)) = label i b)
    (htop : ∀ q : Quotient R, letI := LT q
      T2Space (IntrinsicFoliationLeaf R q) ∧
      SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
      ConnectedSpace (IntrinsicFoliationLeaf R q))
    (hcharts : ∀ q : Quotient R, letI := LT q
      ∀ i (a : IntrinsicFoliationLeaf R q), a.val ∈ (box i).source →
        ∃ k : OpenPartialHomeomorph (IntrinsicFoliationLeaf R q) (ComplexModel r),
          a ∈ k.source ∧
          (∀ z ∈ k.source, z.val ∈ (box i).source ∧ k z = (box i z.val).1) ∧
          ∀ u ∈ k.target, (u,(box i a.val).2) ∈ (box i).target ∧
            ((k.symm u).val = (box i).symm (u,(box i a.val).2))) :
    ∃ F : RegularHolomorphicFoliation.{u,v} d r c M,
      (∃ e : J ≃ F.boxIndex, ∀ i, F.box (e i) = box i) ∧
      F.partition = R ∧ HEq F.leafTopology LT := by
  classical
  let idx : ∀ q : Quotient R, IntrinsicFoliationLeaf R q → J :=
    fun _ p ↦ (hcover p.val).choose
  have hidx : ∀ q (p : IntrinsicFoliationLeaf R q), p.val ∈ (box (idx q p)).source :=
    fun _ p ↦ (hcover p.val).choose_spec
  let χ : ∀ q : Quotient R, letI := LT q
      IntrinsicFoliationLeaf R q →
        OpenPartialHomeomorph (IntrinsicFoliationLeaf R q) (ComplexModel r) :=
    fun q ↦ by
      letI := LT q
      exact fun p ↦ (hcharts q (idx q p) p (hidx q p)).choose
  have hχ : ∀ q : Quotient R, letI := LT q
      ∀ p : IntrinsicFoliationLeaf R q,
        p ∈ (χ q p).source ∧
        (∀ z ∈ (χ q p).source,
          z.val ∈ (box (idx q p)).source ∧ χ q p z = (box (idx q p) z.val).1) ∧
        ∀ u ∈ (χ q p).target,
          (u, (box (idx q p) p.val).2) ∈ (box (idx q p)).target ∧
          ((χ q p).symm u).val = (box (idx q p)).symm (u, (box (idx q p) p.val).2) :=
    fun q p ↦ (hcharts q (idx q p) p (hidx q p)).choose_spec
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
      fun a ↦ (hcharts q i (h a)
        ((box i).map_target (ht a))).choose
    have hk a := (hcharts q i (h a)
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

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly


namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w

/-- A product vector is horizontal exactly when its second coordinate vanishes. -/
private theorem mem_horizontal_iff {r c : ℕ} (w : ComplexModel r × ComplexModel c) :
    w ∈ (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range ↔
      w.2 = 0 := by
  constructor
  · rintro ⟨a,rfl⟩
    rfl
  · intro h
    exact ⟨w.1, Prod.ext rfl h.symm⟩

/-- An injective chart differential identifies distribution membership with membership in its
flattened image. -/
private theorem mem_flattened_iff {r c : ℕ} {E : Type u} [AddCommGroup E] [Module ℂ E]
    (D : E →ₗ[ℂ] (ComplexModel r × ComplexModel c)) (hD : Function.Injective D)
    (P : Submodule ℂ E)
    (hflat : P.map D =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (v : E) : v ∈ P ↔ (D v).2 = 0 := by
  rw [← mem_horizontal_iff, ← hflat]
  constructor
  · exact fun hv ↦ ⟨v,hv,rfl⟩
  · rintro ⟨w,hw,he⟩
    exact hD he ▸ hw

/-- A locally invertible box satisfying the transverse derivative identity flattens the pullback
distribution. -/
private theorem pullback_flattening
    {r c : ℕ} {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (dp : E →ₗ[ℂ] F) (D : E →ₗ[ℂ] (ComplexModel r × ComplexModel c))
    (Db : F →ₗ[ℂ] (ComplexModel r × ComplexModel c))
    (hD : Function.Surjective D) (hDb : Function.Injective Db)
    (P : Submodule ℂ F)
    (hflat : P.map Db =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (hzero : ∀ v, (D v).2 = 0 ↔ (Db (dp v)).2 = 0) :
    (P.comap dp).map D =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range := by
  ext w
  rw [mem_horizontal_iff]
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (hzero v).mpr ((mem_flattened_iff Db hDb P hflat (dp v)).mp hv)
  · intro hw
    obtain ⟨v,rfl⟩ := hD w
    exact ⟨v,(mem_flattened_iff Db hDb P hflat (dp v)).mpr ((hzero v).mp hw),rfl⟩

/-- The lifted box derivative maps the pullback distribution onto the horizontal subspace. -/
private theorem lifted_box_flattening
    {d r c : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (P : ∀ x, Submodule ℂ (TangentSpace (complexModel d) x))
    (hflat : ∀ i x, x ∈ (F.box i).source → (P x).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
        (F.box i) x).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range)
    (s : OpenPartialHomeomorph Y X) (hsp : EqOn s p s.source)
    (hs : ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source)
    (i : F.boxIndex) (a : ComplexModel r × ComplexModel c) (ρ : ℝ) (hρ : 0 < ρ)
    (B : OpenPartialHomeomorph Y (ComplexModel r × ComplexModel c))
    (hB : B = Theorem12UnitProductBox.unitSubchart (s.trans (F.box i)) a ρ hρ)
    (he : ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c))
      ∞ B B.source)
    (hei : ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d)
      ∞ B.symm B.target) (y : Y) (hy : y ∈ B.source) :
    ((P (p y)).comap (mfderiv (complexModel d) (complexModel d) p y).toLinearMap).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c)) B y).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range := by
  have hy' : y ∈ (s.trans (F.box i)).source :=
    Theorem12UnitProductBox.unitSubchart_source_subset _ a ρ hρ (hB ▸ hy)
  have hpy : p y ∈ (F.box i).source := by
    rw [← hsp hy'.1]
    exact hy'.2
  have hBD : B.MDifferentiable (complexModel d) ((complexModel r).prod (complexModel c)) :=
    ⟨he.mdifferentiableOn (by simp),hei.mdifferentiableOn (by simp)⟩
  have hFD : (F.box i).MDifferentiable (complexModel d)
      ((complexModel r).prod (complexModel c)) :=
    ⟨(F.box_holomorphic i).mdifferentiableOn (by simp),
      (F.box_inverse_holomorphic i).mdifferentiableOn (by simp)⟩
  apply pullback_flattening _ _ _ (hBD.mfderiv_surjective hy)
    (hFD.mfderiv_injective hpy) (P (p y)) (hflat i (p y) hpy)
  intro v
  rw [hB]
  exact Theorem12CoverBoxes.lifted_unit_box_horizontal_iff F p s hsp hs i a ρ hρ y
    (hB ▸ hy) v

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly


namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w

/-- A holomorphic covering pulls back a regular holomorphic foliation, with leaf ranges equal to
marked intrinsic path-lift ranges and tangent projection onto the base distribution. (Hatcher,
pp.60–62; Bredon, II.14; Nisoli, pp.9–10) -/
theorem lifted_regular_foliation
    {d r c : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (ComplexModel d) Y] [IsManifold (complexModel d) ∞ Y]
    (F : RegularHolomorphicFoliation.{u,w} d r c X) (p : Y → X)
    (hp : IsCoveringMap p)
    (hplocal : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (hsheets : ∀ y : Y, ∃ s : OpenPartialHomeomorph Y X,
      y ∈ s.source ∧ EqOn s p s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target)
    (P : ∀ x, Submodule ℂ (TangentSpace (complexModel d) x))
    (hflat : ∀ i x, x ∈ (F.box i).source → (P x).map
      (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
        (F.box i) x).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range) :
    ∃ G : RegularHolomorphicFoliation.{v,v} d r c Y,
      (∀ y, (G.tangent y).map
        (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = P (p y)) ∧
      ∀ y, Set.range (Subtype.val : G.Leaf y → Y) =
        liftedIntrinsicLeafRange p (Subtype.val : F.Leaf (p y) → X) ⟨p y,rfl⟩ y := by
  classical
  obtain ⟨B, hb⟩ := Theorem12CoverBoxes.exists_lifted_unit_box_family F p hsheets
  choose i s ρ hρ hdata using fun y ↦ (hb y).2.2.2.2
  have htarget : ∀ y, (B y).target = (complexFoliationDisk r : Set _) ×ˢ
      (complexFoliationDisk c : Set _) := fun y ↦ (hb y).2.1
  let center := fun y ↦ F.box (i y) (p y)
  have hsrc : ∀ y, (B y).source ⊆ (s y).source := by
    intro y z hz
    rw [(hdata y).2.2.2.2.1] at hz
    exact hz.1
  have hsp : ∀ y, EqOn (s y) p (s y).source := fun y ↦ (hdata y).2.1
  have hcoord : ∀ y, ∀ a : complexFoliationDisk r, ∀ b : complexFoliationDisk c,
      center y + (ρ y : ℂ) • (a.val, b.val) ∈ (F.box (i y)).target := by
    intro y a b
    have h := (hdata y).2.2.2.2.2.2.2.2.2.2.2.2 ⟨(a.val,b.val), ⟨a.property,b.property⟩,rfl⟩
    exact h.1
  have hproj : ∀ y, ∀ a : complexFoliationDisk r, ∀ b : complexFoliationDisk c,
      p ((B y).symm (a.val,b.val)) =
        (F.box (i y)).symm (center y + (ρ y : ℂ) • (a.val,b.val)) := by
    intro y a b
    exact (hdata y).2.2.2.2.2.2.2.2.2.1 (a.val,b.val) (by rw [htarget]; exact ⟨a.property,b.property⟩)
  let R := Relation.EqvGen.setoid (LiftedPlaquePartition.rawPlaqueStep B)
  have hr : ∀ y z, R y z ↔ z ∈ liftedIntrinsicLeafRange p
      (Subtype.val : F.Leaf (p y) → X) ⟨p y,rfl⟩ y := by
    intro y z
    exact LiftedPlaquePartition.raw_affine_partition_iff_lifted_range F p B
      (fun y ↦ ⟨y,(hb y).1⟩) htarget i s hsrc hsp center ρ hρ hcoord hproj y z
  have hclasses : ∀ q : Quotient R,
      ∃ top : TopologicalSpace (IntrinsicFoliationLeaf R q), letI := top
      ∃ cs : ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf R q), letI := cs
        IsManifold (complexModel r) ∞ (IntrinsicFoliationLeaf R q) ∧
        T2Space (IntrinsicFoliationLeaf R q) ∧
        SecondCountableTopology (IntrinsicFoliationLeaf R q) ∧
        ConnectedSpace (IntrinsicFoliationLeaf R q) ∧
        ContMDiff (complexModel r) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf R q → Y) ∧
        (∀ z, Function.Injective (mfderiv (complexModel r) (complexModel d)
          (Subtype.val : IntrinsicFoliationLeaf R q → Y) z)) ∧
        Set.range (Subtype.val : IntrinsicFoliationLeaf R q → Y) =
          liftedIntrinsicLeafRange p (Subtype.val : F.Leaf (p q.out) → X)
            ⟨p q.out,rfl⟩ q.out ∧
        ∃ H : IntrinsicFoliationLeaf R q ≃ₜ IntrinsicCoveringPullbackLeaf
            (Subtype.val : F.Leaf (p q.out) → X) p ⟨p q.out,rfl⟩ q.out rfl,
          ∀ z, intrinsicCoveringLeafInclusion
            (Subtype.val : F.Leaf (p q.out) → X) p ⟨p q.out,rfl⟩ q.out rfl (H z) = z.val := by
    intro q
    apply LiftedRegularFoliationSupport.original_foliation_lifted_class_structure F p hp
      hplocal R q q.out
    intro z
    have he : Quotient.mk R z = q ↔ R q.out z := by
      constructor
      · intro hz
        exact R.symm (Quotient.exact (hz.trans (Quotient.out_eq q).symm))
      · intro hz
        exact (Quotient.sound (R.symm hz)).trans (Quotient.out_eq q)
    exact he.trans (hr q.out z)
  choose LT LC hm ht hsc hc hi hdi hrc H hH using hclasses
  let zero : complexFoliationDisk r := ⟨0,Metric.mem_ball_self (by norm_num)⟩
  let label := fun k (b : complexFoliationDisk c) ↦
    Quotient.mk R ((B k).symm (zero.val,b.val))
  have hlabel : ∀ k (a : complexFoliationDisk r) (b : complexFoliationDisk c),
      Quotient.mk R ((B k).symm (a.val,b.val)) = label k b := by
    intro k a b
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨k,b,a,zero,rfl,rfl⟩)
  have hopen : ∀ q k b (h : label k b = q), letI := LT q
      IsOpenEmbedding (fun a : complexFoliationDisk r ↦
        (⟨(B k).symm (a.val,b.val),(hlabel k a b).trans h⟩ :
          IntrinsicFoliationLeaf R q)) := by
    intro q k b h
    let := LT q
    apply class_whole_slice_isOpenEmbedding F p R q q.out (H q) (hH q)
      (B k) (i k)
      (LiftedPlaquePartition.affineCoordinate (center k).1 (ρ k) (hρ k))
      (LiftedPlaquePartition.affineCoordinate (center k).2 (ρ k) (hρ k))
      (fun a b ↦ hcoord k a b) (fun a b ↦ hproj k a b)
      (s k) (hsrc k) (hsp k) (htarget k) b
      (fun a ↦ (hlabel k a b).trans h)
  have hcharts : ∀ q : Quotient R, letI := LT q
      ∀ k (z : IntrinsicFoliationLeaf R q), z.val ∈ (B k).source →
        ∃ e : OpenPartialHomeomorph (IntrinsicFoliationLeaf R q) (ComplexModel r),
          z ∈ e.source ∧
          (∀ w ∈ e.source, w.val ∈ (B k).source ∧ e w = (B k w.val).1) ∧
          ∀ u ∈ e.target, (u,(B k z.val).2) ∈ (B k).target ∧
            ((e.symm u).val = (B k).symm (u,(B k z.val).2)) := by
    intro q
    let := LT q
    intro k z hz
    have hzt := (B k).map_source hz
    rw [htarget] at hzt
    let a : complexFoliationDisk r := ⟨(B k z.val).1,hzt.1⟩
    let b : complexFoliationDisk c := ⟨(B k z.val).2,hzt.2⟩
    have hab : (B k).symm (a.val,b.val) = z.val := (B k).left_inv hz
    have hl : label k b = q :=
      (hlabel k a b).symm.trans ((congrArg (Quotient.mk R) hab).trans z.property)
    let t : complexFoliationDisk r → IntrinsicFoliationLeaf R q :=
      fun a ↦ ⟨(B k).symm (a.val,b.val),(hlabel k a b).trans hl⟩
    have hta : t a = z := Subtype.ext hab
    obtain ⟨e,he,hf,hi⟩ := local_chart_of_whole_slice Subtype.val (B k) b t
      (hopen q k b hl) (fun _ ↦ rfl) (htarget k) a
    refine ⟨e,hta ▸ he,hf,?_⟩
    exact hi
  have hflatB : ∀ k y, y ∈ (B k).source →
      ((P (p y)).comap (mfderiv (complexModel d) (complexModel d) p y).toLinearMap).map
        (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
          (B k) y).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel c)).toLinearMap.range := by
    intro k y hy
    exact lifted_box_flattening F p P hflat (s k) (hsp k) (hdata k).2.2.1
      (i k) (center k) (ρ k) (hρ k) (B k) (hdata k).1
      (hb k).2.2.1 (hb k).2.2.2.1 y hy
  obtain ⟨G,⟨e,he⟩,hGR,_⟩ := regular_foliation_of_class_charts B F.dimension
    (fun y ↦ (P (p y)).comap (mfderiv (complexModel d) (complexModel d) p y).toLinearMap)
    htarget (fun y ↦ ⟨y,(hb y).1⟩) (fun y ↦ (hb y).2.2.1)
    (fun y ↦ (hb y).2.2.2.1) hflatB R (fun _ _ ↦ Iff.rfl) LT label hlabel
    (fun q ↦ ⟨ht q,hsc q,hc q⟩) hcharts
  have hrel : ∀ x y, G.partition x y ↔ R x y := by
    intro x y
    rw [hGR]
  refine ⟨G,?_,?_⟩
  · intro y
    apply RegularHolomorphicFoliation.tangent_map_eq_of_pullback_box_flattening
      (complexModel d) G p hplocal P
    intro k z hz
    obtain ⟨j,rfl⟩ := e.surjective k
    rw [he j]
    exact hflatB j z (by simpa only [he j] using hz)
  · intro y
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      apply (hr y t.val).mp
      apply R.symm
      exact (hrel t.val y).mp (Quotient.exact t.property)
    · intro hz
      refine ⟨⟨z,?_⟩,rfl⟩
      apply Quotient.sound
      exact (hrel z y).mpr (R.symm ((hr y z).mpr hz))

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly


namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v

/-- A holomorphic distribution with native real leaves defines a regular foliation on a holomorphic
covering whose leaves are the marked intrinsic path-lift ranges. -/
private theorem original_lifted_regular_foliation
    {d r c : ℕ} {X : Type u} {Y : Type v}
    [MetricSpace X] [SecondCountableTopology X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [IsManifold (realModel d) ∞ X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (ComplexModel d) Y] [IsManifold (complexModel d) ∞ Y]
    (f : X ≃ₜ X) (hdim : d = r + c)
    (P R : ∀ q : X, Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P) (hR : IsHolomorphicTangentSubbundle c R)
    (hcompl : ∀ q, IsCompl (P q) (R q))
    (Q T : RealTangentDistribution (realModel d) X)
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (hRealR : ∀ q, ((R q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = T q)
    (DP : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (DR : ∀ b, NativeAsymptoticLeafDatum (realModel d) f.symm T b)
    (p : Y → X) (hp : IsCoveringMap p)
    (hplocal : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (hsheets : ∀ y : Y, ∃ s : OpenPartialHomeomorph Y X,
      y ∈ s.source ∧ EqOn s p s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target) :
    ∃ G : RegularHolomorphicFoliation.{v,v} d r c Y,
      (∀ y, (G.tangent y).map
        (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = P (p y)) ∧
      ∀ y, letI := (DP (p y)).topology
        Set.range (Subtype.val : G.Leaf y → Y) =
          liftedIntrinsicLeafRange p
            (Subtype.val : StableAsymptoticLeaf f (p y) → X)
            ⟨p y,(NativeBoxPartition.asymptoticSetoid f).refl (p y)⟩ y := by
  obtain ⟨F,hflat,_,hn⟩ := original_regular_foliation f hdim P R hP hR hcompl Q T
    hRealP hRealR DP DR
  obtain ⟨G,hG,hr⟩ := lifted_regular_foliation F p hp hplocal hsheets P hflat
  refine ⟨G,hG,?_⟩
  intro y
  let := (DP (p y)).topology
  obtain ⟨H,hH,_,hm⟩ := hn (p y)
  rw [hr y]
  have ht := lifted_range_homeomorph p (Subtype.val : F.Leaf (p y) → X)
    (Subtype.val : StableAsymptoticLeaf f (p y) → X) H hH ⟨p y,rfl⟩ y
  rw [hm] at ht
  exact ht

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly




namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology
open scoped ContDiff Manifold
noncomputable section
universe u v w

/-- Complementary stable and unstable native distributions give two lifted regular foliations with
the specified translated-subspace leaf images. -/
private theorem original_lifted_complementary_foliations
    {d r c : ℕ} {X : Type u} {Y : Type v} {W : Type w} [AddCommGroup W]
    [MetricSpace X] [SecondCountableTopology X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [IsManifold (realModel d) ∞ X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (ComplexModel d) Y] [IsManifold (complexModel d) ∞ Y]
    (f : X ≃ₜ X) (hdim : d = r + c)
    (P R : ∀ q : X, Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P) (hR : IsHolomorphicTangentSubbundle c R)
    (hcompl : ∀ q, IsCompl (P q) (R q))
    (Q T : RealTangentDistribution (realModel d) X)
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (hRealR : ∀ q, ((R q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = T q)
    (DP : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b)
    (DR : ∀ b, NativeAsymptoticLeafDatum (realModel d) f.symm T b)
    (p : Y → X) (hp : IsCoveringMap p)
    (hsheets : ∀ y : Y, ∃ s : OpenPartialHomeomorph Y X,
      y ∈ s.source ∧ EqOn s p s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target)
    (H : Y → W) (Vs Vu : Set W)
    (hStableImage : ∀ y, letI := (DP (p y)).topology
      H '' liftedIntrinsicLeafRange p
        (Subtype.val : StableAsymptoticLeaf f (p y) → X)
        ⟨p y,(NativeBoxPartition.asymptoticSetoid f).refl (p y)⟩ y =
        (fun v ↦ H y + v) '' Vs)
    (hUnstableImage : ∀ y, letI := (DR (p y)).topology
      H '' liftedIntrinsicLeafRange p
        (Subtype.val : StableAsymptoticLeaf f.symm (p y) → X)
        ⟨p y,(NativeBoxPartition.asymptoticSetoid f.symm).refl (p y)⟩ y =
        (fun v ↦ H y + v) '' Vu) :
    ∃ (Ws : RegularHolomorphicFoliation.{v,v} d r c Y)
      (Wu : RegularHolomorphicFoliation.{v,v} d c r Y),
      (∀ y, (Ws.tangent y).map
        (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = P (p y)) ∧
      (∀ y, (Wu.tangent y).map
        (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = R (p y)) ∧
      (∀ y, H '' Set.range (Subtype.val : Ws.Leaf y → Y) =
        {v | ∃ w : Vs, v = H y + w.val}) ∧
      (∀ y, H '' Set.range (Subtype.val : Wu.Leaf y → Y) =
        {v | ∃ w : Vu, v = H y + w.val}) := by
  have hlocal :=
    HolomorphicAnosov.Theorem12LiftedFoliationAssembly.locally_biholomorphic_of_sheets p hsheets
  obtain ⟨Ws,hs,hrs⟩ := original_lifted_regular_foliation f hdim P R hP hR hcompl
    Q T hRealP hRealR DP DR p hp hlocal hsheets
  obtain ⟨Wu,hu,hru⟩ := original_lifted_regular_foliation f.symm
    (hdim.trans (Nat.add_comm r c)) R P hR hP (fun q ↦ (hcompl q).symm)
    T Q hRealR hRealP DR (by simpa only [Homeomorph.symm_symm] using DP)
    p hp hlocal hsheets
  refine ⟨Ws,Wu,hs,hu,?_,?_⟩
  · intro y
    let := (DP (p y)).topology
    rw [hrs y,hStableImage y,
      HolomorphicAnosov.Theorem12LiftedFoliationAssembly.translated_image_eq]
  · intro y
    let := (DR (p y)).topology
    rw [hru y,hUnstableImage y,
      HolomorphicAnosov.Theorem12LiftedFoliationAssembly.translated_image_eq]

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly



namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set Topology _root_.Topology Filter
open scoped ContDiff Manifold
noncomputable section
universe u v

/-- The original Anosov tangent bundles and intrinsic asymptotic leaves define two regular
holomorphic foliations on a holomorphic covering with the specified tangent projections and
translated-subspace leaf images. (Zhang, Thm 1.2, p.11; Lee, Prop 18.5 and Thm 18.6, pp.469–472;
Demailly, I §3.C, p.23; HPS, §7, pp.115–116; Nisoli, Defs 1.1.1–1.1.3, pp.9–10; Hatcher,
pp.60–62; Bredon, II.14, pp.111–112) -/
theorem bool_native_lifted_foliations
    {d r s : ℕ} {X V : Type u}
    [MetricSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    [IsManifold (realModel d) ∞ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [ChartedSpace (ComplexModel d) V]
    [IsManifold (complexModel d) ∞ V]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (P U : ∀ q : X, Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle r P)
    (hU : IsHolomorphicTangentSubbundle s U) (hdim : d = r + s)
    (hcompl : ∀ q, IsCompl (P q) (U q))
    (hRealP : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution q)
    (hRealU : ∀ q, ((U q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution q)
    (native : ∀ (σ : Bool) (x : X), NativeAsymptoticLeafDatum (realModel d)
      (if σ then f.toHomeomorph.symm else f.toHomeomorph)
      (if σ then a.splitting.unstable.toDistribution else a.splitting.stable.toDistribution) x)
    (p : V → X) (hp : IsCoveringMap p)
    (hsheets : ∀ y : V, ∃ e : OpenPartialHomeomorph V X,
      y ∈ e.source ∧ EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    (H : V → V) (decay : Bool → Set V) (Vs Vu : Submodule ℝ V)
    (hVs : (Vs : Set V) = decay false) (hVu : (Vu : Set V) = decay true)
    (hImages : ∀ (σ : Bool) (y : V),
      let leafHomeomorph := if σ then f.toHomeomorph.symm else f.toHomeomorph
      letI := (native σ (p y)).topology
      ∀ b : StableAsymptoticLeaf leafHomeomorph (p y), b.val = p y →
        H '' liftedIntrinsicLeafRange p Subtype.val b y = (fun v ↦ H y + v) '' decay σ) :
    ∃ (Ws : RegularHolomorphicFoliation.{u,u} d r s V)
      (Wu : RegularHolomorphicFoliation.{u,u} d s r V),
      (∀ y, (Ws.tangent y).map
        (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = P (p y)) ∧
      (∀ y, (Wu.tangent y).map
        (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = U (p y)) ∧
      (∀ y, H '' Set.range (Subtype.val : Ws.Leaf y → V) =
        {v | ∃ w : Vs, v = H y + (w : V)}) ∧
      (∀ y, H '' Set.range (Subtype.val : Wu.Leaf y → V) =
        {v | ∃ w : Vu, v = H y + (w : V)}) := by
  apply original_lifted_complementary_foliations f.toHomeomorph hdim P U hP hU hcompl
    a.splitting.stable.toDistribution a.splitting.unstable.toDistribution
    hRealP hRealU (native false) (native true) p hp hsheets H (Vs : Set V) (Vu : Set V)
  · intro y
    let := (native false (p y)).topology
    rw [hVs]
    exact hImages false y
      ⟨p y,(NativeBoxPartition.asymptoticSetoid f.toHomeomorph).refl (p y)⟩ rfl
  · intro y
    let := (native true (p y)).topology
    rw [hVu]
    exact hImages true y
      ⟨p y,(NativeBoxPartition.asymptoticSetoid f.toHomeomorph.symm).refl (p y)⟩ rfl

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly

