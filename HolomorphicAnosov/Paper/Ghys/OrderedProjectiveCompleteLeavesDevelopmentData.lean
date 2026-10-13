import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveCompleteLeavesStableDevelopmentData
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveCompleteLeavesUnstableDevelopmentData
import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import HolomorphicAnosov.Paper.Ghys.CompleteAffineLeafHolomorphicLift
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveLiftComponent
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductImage

noncomputable section
open Set _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

/-- Records the stable and unstable complete-leaf development data for an ordered projective development. (Ghys, §5) -/
theorem ordered_projective_complete_leaves_development_data
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p) :
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
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target) ∧
(∀ u : U,
  let L := A.unstableLeaf (p u)
  letI := L.native.topology
  letI := L.complexCharts
  ∃ lift : UnstableAsymptoticLeaf f.toHomeomorph (p u) → U,
    ContMDiff (complexModel 1) (complexModel 2) ∞ lift ∧
    Function.Injective lift ∧
    (∀ z, p (lift z) = z.val) ∧
    (∀ z, z.val = p u → lift z = u) ∧
    connectedComponentIn
      {v : U | (D.developingMap v).1 = (D.developingMap u).1} u ⊆ Set.range lift ∧
    ∃ (pole : ComplexProjectiveLine)
      (e : OpenPartialHomeomorph
        (UnstableAsymptoticLeaf f.toHomeomorph (p u)) ComplexProjectiveLine),
      e.source = Set.univ ∧ e.target = {pole}ᶜ ∧
      (∀ z, e z = (D.developingMap (lift z)).2) ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target) := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  exact ⟨ordered_projective_complete_leaves_stable_development_data A D,
    ordered_projective_complete_leaves_unstable_development_data A D⟩

end HolomorphicAnosov.Ghys
