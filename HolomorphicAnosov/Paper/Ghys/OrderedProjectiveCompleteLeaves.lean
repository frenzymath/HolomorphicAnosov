import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveLiftAffineFormula
import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import HolomorphicAnosov.Paper.Ghys.CompleteAffineLeafHolomorphicLift
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveLiftComponent
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductImage
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveCompleteLeavesDevelopmentData

noncomputable section
open Set _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

/-- The specified ordered projective development maps each complete intrinsic leaf onto a punctured projective line. (Ghys, Proposition 3.1; §5) -/
theorem ordered_projective_complete_leaves
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p) :
    CompleteLiftedProjectiveLeaves D := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  have hstableLifts (u : U) := complete_affine_leaf_holomorphic_lift
    f.toHomeomorph a.splitting.stable.toDistribution p D.covering D.cover_holomorphic u (A.stableLeaf (p u))
  have hunstableLifts (u : U) := complete_affine_leaf_holomorphic_lift
    f.toHomeomorph.symm a.splitting.unstable.toDistribution p D.covering D.cover_holomorphic u
      (A.unstableLeaf (p u))
  suffices hdevelopment :
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
                ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target) by
    obtain ⟨hstableData, hunstableData⟩ := hdevelopment
    constructor
    · intro u
      let := (A.stableLeaf (p u)).native.topology
      let := (A.stableLeaf (p u)).complexCharts
      obtain ⟨lift, hlift, hinj, hproj, hpoint, hback, pole, e, hsource, htarget,
        heq, he, heinv⟩ := hstableData u
      have hrange : Set.range lift = connectedComponentIn
          {v : U | (D.developingMap v).2 = (D.developingMap u).2} u :=
        (ordered_projective_stable_lift_component_subset A D u lift hlift.continuous
          hproj hpoint).antisymm hback
      refine ⟨lift, hlift, hinj, hproj, hrange, pole, e, hsource, htarget,
        heq, he, heinv, ?_⟩
      have hconst (z) : (D.developingMap (lift z)).2 = (D.developingMap u).2 :=
        connectedComponentIn_subset
          {v : U | (D.developingMap v).2 = (D.developingMap u).2} u
          (hrange ▸ Set.mem_range_self z)
      exact stable_product_image_of_lift_data D.developingMap u lift hconst pole e hsource htarget heq
    · intro u
      let := (A.unstableLeaf (p u)).native.topology
      let := (A.unstableLeaf (p u)).complexCharts
      obtain ⟨lift, hlift, hinj, hproj, hpoint, hback, pole, e, hsource, htarget,
        heq, he, heinv⟩ := hunstableData u
      have hrange : Set.range lift = connectedComponentIn
          {v : U | (D.developingMap v).1 = (D.developingMap u).1} u :=
        (ordered_projective_unstable_lift_component_subset A D u lift hlift.continuous
          hproj hpoint).antisymm hback
      refine ⟨lift, hlift, hinj, hproj, hrange, pole, e, hsource, htarget,
        heq, he, heinv, ?_⟩
      have hconst (z) : (D.developingMap (lift z)).1 = (D.developingMap u).1 :=
        connectedComponentIn_subset
          {v : U | (D.developingMap v).1 = (D.developingMap u).1} u
          (hrange ▸ Set.mem_range_self z)
      exact unstable_product_image_of_lift_data D.developingMap u lift hconst pole e hsource htarget heq
  have hstable_local_affine := ordered_projective_stable_lift_local_affine A D
  have hunstable_local_affine := ordered_projective_unstable_lift_local_affine A D
  exact ordered_projective_complete_leaves_development_data A D

end HolomorphicAnosov.Ghys
