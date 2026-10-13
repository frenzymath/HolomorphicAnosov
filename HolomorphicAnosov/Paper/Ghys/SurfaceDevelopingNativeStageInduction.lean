import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingInjectiveBaseStage
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingLeafTools
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingSetTools
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingGraphIntersection
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingOnePointInduction
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingGraphTransport
import HolomorphicAnosov.Paper.Ghys.SurfaceGraphPatching
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Topology.SurfaceInjectivityKernel
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveProduct
import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic

noncomputable section
open Set _root_.Topology
open scoped ContDiff
universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- The developing map is injective on each connected nonempty finite prefix of open unstable
saturations, given a homeomorphism `ComplexProjectiveLine ≃ₜ OnePoint ℂ`.
Each prefix image is the complement of a continuous graph over the projective line with
at most one base point removed. -/
theorem native_stage_induction_with_homeomorph
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (ComplexModel 2) U] [IsManifold (complexModel 2) ∞ U]
    (p : U → S) (D : OrderedProjectiveProductDevelopment A p)
    (hleaves : CompleteLiftedProjectiveLeaves D)
    (e : ComplexProjectiveLine ≃ₜ OnePoint ℂ) (x : ℕ → U)
    (hopen : ∀ i : ℕ, IsOpen (unstableSaturation D (x i)))
    (hprefix : ∀ n, 1 ≤ n → IsConnected
      (⋃ i ∈ Finset.range n, unstableSaturation D (x i))) :
    ∀ n, 1 ≤ n → Set.InjOn D.developingMap
      (⋃ i ∈ Finset.range n, unstableSaturation D (x i)) ∧
      ∃ (F : Set ComplexProjectiveLine)
        (u : C({p : ComplexProjectiveLine // p ∉ F}, ComplexProjectiveLine)),
        (F = ∅ ∨ ∃ pole : ComplexProjectiveLine, F = {pole}) ∧
        D.developingMap '' (⋃ i ∈ Finset.range n, unstableSaturation D (x i)) =
          {z | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} := by
  let E := e.prodCongr e
  let D' := E ∘ D.developingMap
  have hD' : IsLocalHomeomorph D' :=
    E.isLocalHomeomorph.comp D.localBiholomorph.isLocalHomeomorph
  have hbase : ∀ i, Set.InjOn D' (unstableSaturation D (x i)) ∧
      ∃ (b : OnePoint ℂ) (v : C({q : OnePoint ℂ // q ∉ ({b} : Set (OnePoint ℂ))},
        OnePoint ℂ)), (unstableSaturation D (x i)).Nonempty ∧
      D' '' unstableSaturation D (x i) = {z | ∃ hp : z.1 ∉ ({b} : Set (OnePoint ℂ)),
        z.2 ≠ v ⟨z.1, hp⟩} := by
    intro i
    obtain ⟨b, _, v, hne, _, _, hinj, _, himage, _⟩ :=
      surface_developing_injective_base_stage A D hleaves (x i)
    let vn : C({q : ComplexProjectiveLine // q ∉ ({b} : Set ComplexProjectiveLine)},
        ComplexProjectiveLine) := v
    have hi : Set.InjOn D' (unstableSaturation D (x i)) :=
      fun y hy z hz heq ↦ hinj hy hz (E.injective heq)
    have hm : D' '' unstableSaturation D (x i) =
        {z | ∃ hp : z.1 ∉ e '' ({b} : Set ComplexProjectiveLine),
          z.2 ≠ transportMissing e {b} vn ⟨z.1, hp⟩} := by
      rw [Set.image_comp, himage]
      exact transportMissing_image e {b} vn
    let r : {q : OnePoint ℂ // q ∉ ({e b} : Set (OnePoint ℂ))} →
        {q : ComplexProjectiveLine // q ∉ ({b} : Set ComplexProjectiveLine)} :=
      fun q ↦ ⟨e.symm q.val, fun h ↦ q.property (by
        simpa only [Set.mem_singleton_iff, e.apply_symm_apply] using congrArg e h)⟩
    let v' : C({q : OnePoint ℂ // q ∉ ({e b} : Set (OnePoint ℂ))}, OnePoint ℂ) :=
      ⟨fun q ↦ e (vn (r q)), e.continuous.comp (vn.continuous.comp
        ((e.symm.continuous.comp continuous_subtype_val).subtype_mk _))⟩
    refine ⟨hi, e b, v', hne, ?_⟩
    rw [hm]
    ext z
    constructor
    · rintro ⟨hz, hneq⟩
      have hz' : z.1 ∉ ({e b} : Set (OnePoint ℂ)) := by
        simpa only [Set.image_singleton] using hz
      refine ⟨hz', ?_⟩
      change z.2 ≠ e (vn ⟨e.symm z.1, _⟩) at hneq ⊢
      exact hneq
    · rintro ⟨hz, hneq⟩
      have hz' : z.1 ∉ e '' ({b} : Set ComplexProjectiveLine) := by
        simpa only [Set.image_singleton] using hz
      refine ⟨hz', ?_⟩
      change z.2 ≠ e (vn ⟨e.symm z.1, _⟩) at hneq ⊢
      exact hneq
  have hnfull : ∀ n, Set.InjOn D' (⋃ i ∈ Finset.range n, unstableSaturation D (x i)) →
      ∀ q : OnePoint ℂ, ¬∀ r : OnePoint ℂ,
        (q, r) ∈ D' '' (⋃ i ∈ Finset.range n, unstableSaturation D (x i)) := by
    intro n hinj q hfull
    have hi : Set.InjOn D.developingMap
        (⋃ i ∈ Finset.range n, unstableSaturation D (x i)) :=
      fun y hy z hz heq ↦ hinj hy hz (congrArg E heq)
    apply saturated_injective_no_full_fibre D hleaves _
      (fun y hy z hz ↦ prefix_closed_under_leaf D x n hy hz) hi (e.symm q)
    intro r
    obtain ⟨y, hy, heq⟩ := hfull (e r)
    refine ⟨y, hy, ?_⟩
    have hh := congrArg E.symm heq
    dsimp only [D', Function.comp_apply] at hh
    rw [E.symm_apply_apply] at hh
    change D.developingMap y = (e.symm q, e.symm (e r)) at hh
    simpa only [e.symm_apply_apply] using hh
  intro n hn
  obtain ⟨hinj, F, u, hF, himage⟩ := onePoint_finite_prefix_induction D' hD'
    (fun i ↦ unstableSaturation D (x i)) hopen hbase hnfull hprefix n hn
  refine ⟨fun y hy z hz heq ↦ hinj hy hz (congrArg E heq),
    e.symm '' F, transportMissing e.symm F u, ?_, ?_⟩
  · rcases hF with rfl | ⟨pole, rfl⟩
    · exact Or.inl (Set.image_empty _)
    · exact Or.inr ⟨e.symm pole, Set.image_singleton⟩
  · have hh := congrArg (fun C ↦ E.symm '' C) himage
    have hleft : E.symm '' (D' '' (⋃ i ∈ Finset.range n,
        unstableSaturation D (x i))) =
        D.developingMap '' (⋃ i ∈ Finset.range n, unstableSaturation D (x i)) := by
      rw [← Set.image_comp]
      congr 1
      funext y
      exact E.symm_apply_apply (D.developingMap y)
    rw [hleft] at hh
    exact hh.trans (transportMissing_image e.symm F u)


end HolomorphicAnosov.Ghys
