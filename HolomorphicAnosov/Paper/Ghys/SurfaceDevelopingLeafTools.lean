import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingInjectiveBaseStage
import HolomorphicAnosov.Paper.Ghys.SurfaceGraphPatching
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Topology.GraphComplementConnected
import HolomorphicAnosov.Topology.SurfaceInjectivityKernel
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveProduct
import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Connected.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-! This file proves leaf intersection and saturation identities and describes complete unstable
developing images as punctured vertical projective fibres. It also shows that an injective
unstable-saturated set cannot develop onto a full vertical fibre (Ghys, Lemma 5.2, pp. 599–600). -/

noncomputable section
open Set _root_.Topology
open scoped ContDiff

universe u v w
namespace HolomorphicAnosov.Ghys

attribute [local instance] complex_isManifold_real

section NativeLeafAlgebra
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
  [IsCompactComplexManifold 2 S]
  {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
  {A : OrderedProjectiveProductAtlas.{u, v} f a}
  {U : Type w} [TopologicalSpace U] [T2Space U]
  [ChartedSpace (ComplexModel 2) U] [IsManifold (complexModel 2) ∞ U]
  {p : U → S} (D : OrderedProjectiveProductDevelopment A p)

omit [T2Space U] in
/-- Intersecting unstable developing leaf components coincide. -/
theorem unstable_leaf_eq_of_mem {x y : U} (hy : y ∈ unstableDevelopingLeaf D x) :
    unstableDevelopingLeaf D x = unstableDevelopingLeaf D y := by
  have he := connectedComponentIn_subset
    {z | (D.developingMap z).1 = (D.developingMap x).1} x hy
  have hf : {z | (D.developingMap z).1 = (D.developingMap x).1} =
      {z | (D.developingMap z).1 = (D.developingMap y).1} := by rw [he]
  exact (connectedComponentIn_eq hy).trans (congrArg (fun F ↦ connectedComponentIn F y) hf)

omit [T2Space U] in
/-- An unstable saturation contains every complete unstable leaf that meets it. -/
theorem unstable_saturation_closed_under_leaf {x y z : U}
    (hy : y ∈ unstableSaturation D x) (hz : z ∈ unstableDevelopingLeaf D y) :
    z ∈ unstableSaturation D x := by
  obtain ⟨q, hq, hyq⟩ := hy
  exact ⟨q, hq, (unstable_leaf_eq_of_mem D hyq) ▸ hz⟩

omit [T2Space U] in
/-- A finite union of unstable saturations contains every complete unstable leaf that meets it. -/
theorem prefix_closed_under_leaf (x : ℕ → U) (n : ℕ) {y z : U}
    (hy : y ∈ ⋃ i ∈ Finset.range n, unstableSaturation D (x i))
    (hz : z ∈ unstableDevelopingLeaf D y) :
    z ∈ ⋃ i ∈ Finset.range n, unstableSaturation D (x i) := by
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨i, hi, unstable_saturation_closed_under_leaf D hyi hz⟩

omit [T2Space U] in
/-- The developing image of a complete unstable leaf is a vertical projective fibre with one point
omitted. -/
theorem complete_unstable_leaf_image (hleaves : CompleteLiftedProjectiveLeaves D)
    (x : U) : ∃ pole : ComplexProjectiveLine,
    D.developingMap '' unstableDevelopingLeaf D x =
      {q | q.1 = (D.developingMap x).1 ∧ q.2 ≠ pole} := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  obtain ⟨lift, _, _, _, hrange, pole, e, _, _, _, _, _, hfull⟩ := hleaves.2 x
  refine ⟨pole, ?_⟩
  rw [← hrange]
  simpa only [← Set.range_comp, Function.comp_def] using hfull

/-- The complex projective line contains a point distinct from any two specified points. -/
theorem projective_exists_ne_pair (a b : ComplexProjectiveLine) :
    ∃ q : ComplexProjectiveLine, q ≠ a ∧ q ≠ b := by
  have hinj : Function.Injective complexProjectiveLineFinite := by
    intro z w hzw
    have hh := congrArg (fun q ↦ complexProjectiveLineChartFun 1 q 0) hzw
    simpa only [complexProjectiveLineFinite,
      (complexProjectiveLineChart_properties 1).2.2.2.2.2] using hh
  let : Infinite ComplexProjectiveLine := Infinite.of_injective _ hinj
  obtain ⟨q, hq⟩ := (Set.finite_singleton a |>.union (Set.finite_singleton b)).exists_notMem
  exact ⟨q, fun h ↦ hq (Or.inl h), fun h ↦ hq (Or.inr h)⟩

omit [T2Space U] in
/-- The developing image of a union of complete unstable leaves on which `D` is injective cannot
contain a full vertical projective fibre. -/
theorem saturated_injective_no_full_fibre
    (hleaves : CompleteLiftedProjectiveLeaves D) (C : Set U)
    (hsat : ∀ x ∈ C, unstableDevelopingLeaf D x ⊆ C)
    (hinj : Set.InjOn D.developingMap C) :
    ∀ q : ComplexProjectiveLine, ¬∀ r : ComplexProjectiveLine,
      (q, r) ∈ D.developingMap '' C := by
  intro q hfull
  obtain ⟨x, hxC, hxD⟩ := hfull q
  obtain ⟨c, hc⟩ := complete_unstable_leaf_image D hleaves x
  obtain ⟨y, hyC, hyD⟩ := hfull c
  obtain ⟨c', hc'⟩ := complete_unstable_leaf_image D hleaves y
  obtain ⟨r, hrc, hrc'⟩ := projective_exists_ne_pair c c'
  have hxfirst : (D.developingMap x).1 = q := congrArg Prod.fst hxD
  have hyfirst : (D.developingMap y).1 = q := congrArg Prod.fst hyD
  have hrx : (q, r) ∈ D.developingMap '' unstableDevelopingLeaf D x := by
    rw [hc]
    exact ⟨hxfirst.symm, hrc⟩
  have hry : (q, r) ∈ D.developingMap '' unstableDevelopingLeaf D y := by
    rw [hc']
    exact ⟨hyfirst.symm, hrc'⟩
  obtain ⟨x', hx'L, hx'D⟩ := hrx
  obtain ⟨y', hy'L, hy'D⟩ := hry
  have hxy : x' = y' := hinj (hsat x hxC hx'L) (hsat y hyC hy'L)
    (hx'D.trans hy'D.symm)
  have heq : unstableDevelopingLeaf D x = unstableDevelopingLeaf D y := by
    rw [unstable_leaf_eq_of_mem D hx'L, unstable_leaf_eq_of_mem D hy'L, hxy]
  have hyL : y ∈ unstableDevelopingLeaf D x := by
    rw [heq]
    exact mem_connectedComponentIn rfl
  have hymem : D.developingMap y ∈ D.developingMap '' unstableDevelopingLeaf D x :=
    ⟨y, hyL, rfl⟩
  rw [hc] at hymem
  exact hymem.2 (congrArg Prod.snd hyD)

end NativeLeafAlgebra

end HolomorphicAnosov.Ghys
