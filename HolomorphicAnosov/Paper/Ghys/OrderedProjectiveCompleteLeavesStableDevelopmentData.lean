import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveLiftAffineFormula
import HolomorphicAnosov.Paper.Ghys.CompleteAffineLeafHolomorphicLift
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveStableComponent
import HolomorphicAnosov.Paper.Ghys.CompleteAffineProjectiveCoordinate

noncomputable section
open Set _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

/-- Stable complete-leaf data consists of pointed lifts and global coordinates onto punctured projective lines. (Ghys, §5) -/
def OrderedProjectiveCompleteLeavesStableDevelopmentData

    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p) : Prop :=
letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
(∀ u : U,
  let L := A.stableLeaf (p u)
  letI := L.native.topology
  letI := L.complexCharts
  ∃ lift : StableAsymptoticLeaf f.toHomeomorph (p u) → U,
    ContMDiff (complexModel 1) (complexModel 2) ∞ lift ∧
    Function.Injective lift ∧
    (∀ z, p (lift z) = z.val) ∧
    (∀ z, z.val = p u → lift z = u) ∧
    connectedComponentIn
      {v : U | (D.developingMap v).2 = (D.developingMap u).2} u ⊆ Set.range lift ∧
    ∃ (pole : ComplexProjectiveLine)
      (e : OpenPartialHomeomorph
        (StableAsymptoticLeaf f.toHomeomorph (p u)) ComplexProjectiveLine),
      e.source = Set.univ ∧ e.target = {pole}ᶜ ∧
      (∀ z, e z = (D.developingMap (lift z)).1) ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target)

/-- Every complete intrinsic stable leaf has the stated pointed developing coordinate. (Ghys, §5; Thurston, §3.5; Hatcher, Propositions 1.33–1.34) -/
theorem ordered_projective_complete_leaves_stable_development_data

    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p) : OrderedProjectiveCompleteLeavesStableDevelopmentData A D := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  intro u
  let L := A.stableLeaf (p u)
  let := L.native.topology
  let := L.complexCharts
  dsimp only
  obtain ⟨lift, hlift, hinj, hproj, hpoint⟩ := complete_affine_leaf_holomorphic_lift
    f.toHomeomorph a.splitting.stable.toDistribution p D.covering
    D.cover_holomorphic u L
  refine ⟨lift, hlift, hinj, hproj, hpoint,
    ordered_projective_stable_component_subset_lift A D u lift hlift.continuous
      hproj hpoint, ?_⟩
  apply complete_affine_projective_coordinate L.affineStructure L.complete
    (fun z ↦ (D.developingMap (lift z)).1) ?_
    (⟨p u, by simp [ForwardAsymptotic]⟩ : StableAsymptoticLeaf f.toHomeomorph (p u))
  intro z
  obtain ⟨c, hc, hz, g, hg⟩ := ordered_projective_stable_lift_local_affine
    A D u lift hlift.continuous hproj z
  exact ⟨c, hc, hz, g, hg.mono fun _ hy ↦ hy.2.1⟩

end HolomorphicAnosov.Ghys

