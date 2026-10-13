import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveCompleteLeavesStableDevelopmentData
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseAnosovDatum

noncomputable section
open Set _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

/-- Unstable complete-leaf data for an ordered projective atlas is obtained by exchanging the stable and unstable factors. (Ghys, §5; Proposition 3.1) -/
def OrderedProjectiveCompleteLeavesUnstableDevelopmentData

    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p) : Prop :=
letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
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
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target)

/-- The unstable complete-leaf theorem follows from the stable theorem applied to inverse dynamics with swapped projective factors. (Ghys, §5) -/
theorem ordered_projective_complete_leaves_unstable_development_data

    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p) : OrderedProjectiveCompleteLeavesUnstableDevelopmentData A D := by
  let ainv := TheoremAProof.inverseAnosovDatum f a
  let swap := Diffeomorph.prodComm (complexModel 1) (complexModel 1)
    ComplexProjectiveLine ComplexProjectiveLine ∞
  let B : OrderedProjectiveProductAtlas f.symm ainv := {
    metric := A.metric
    metric_topology := A.metric_topology
    stableLeaf := A.unstableLeaf
    unstableLeaf := A.stableLeaf
    index := A.index
    chart := fun i ↦ (A.chart i).transHomeomorph swap.toHomeomorph
    cover := A.cover
    holomorphic := by
      intro i
      exact ⟨swap.contMDiff.comp_contMDiffOn (A.holomorphic i).1,
        (A.holomorphic i).2.comp swap.symm.contMDiff.contMDiffOn (fun _ h ↦ h)⟩
    transition := fun i j x ↦ (A.transition i j x).swap
    transition_locallyConstant := by
      intro i j
      exact (A.transition_locallyConstant i j).comp Prod.swap
    transition_self := by
      intro i x hx
      rw [A.transition_self i x hx]
      rfl
    transition_comp := by
      intro i j k x hx
      rw [A.transition_comp i j k x hx]
      rfl
    transition_agrees := by
      intro i j x hx
      exact congrArg Prod.swap (A.transition_agrees i j x hx)
    stable_kernel := A.unstable_kernel
    unstable_kernel := A.stable_kernel
    stable_affine := A.unstable_affine
    unstable_affine := A.stable_affine }
  let E : OrderedProjectiveProductDevelopment B p := {
    covering := D.covering
    surjective := D.surjective
    simplyConnected := D.simplyConnected
    cover_holomorphic := D.cover_holomorphic
    developingMap := fun x ↦ (D.developingMap x).swap
    localBiholomorph := fun x ↦ (D.localBiholomorph x).comp ((complexModel 1).prod (complexModel 1))
      (ComplexProjectiveLine × ComplexProjectiveLine) (swap.isLocalDiffeomorph _)
    holonomy := {
      toFun := fun γ ↦ (D.holonomy γ).swap
      map_one' := congrArg Prod.swap D.holonomy.map_one
      map_mul' := fun γ δ ↦ congrArg Prod.swap (D.holonomy.map_mul γ δ) }
    equivariant := by
      intro γ x
      exact congrArg Prod.swap (D.equivariant γ x)
    locally_chart := by
      intro x
      obtain ⟨i, N, g, hN, hxN, hpN, hNformula⟩ := D.locally_chart x
      exact ⟨i, N, g.swap, hN, hxN, hpN,
        fun y hy ↦ congrArg Prod.swap (hNformula y hy)⟩ }
  exact ordered_projective_complete_leaves_stable_development_data B E

end HolomorphicAnosov.Ghys
