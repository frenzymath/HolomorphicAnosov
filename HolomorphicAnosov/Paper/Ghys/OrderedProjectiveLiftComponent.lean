import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import Mathlib.Topology.Connected.Basic

/-! Pointed lifts of complete intrinsic stable and unstable leaves lie in the corresponding
connected developing fibre components. (Ghys, §5 pp.597–598) -/
noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

/-- A continuous pointed lift of a complete intrinsic stable leaf lies in the connected component of
the second-coordinate fibre through its marked point. (Ghys, §5 pp.597–598) -/
theorem ordered_projective_stable_lift_component_subset
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U]
    {p : U → S} (D : OrderedProjectiveProductDevelopment A p) (u : U) :
    let : MetricSpace S := A.metric.replaceTopology A.metric_topology
    let L := A.stableLeaf (p u)
    let := L.native.topology
    ∀ lift : StableAsymptoticLeaf f.toHomeomorph (p u) → U,
      Continuous lift → (∀ z, p (lift z) = z.val) →
      (∀ z, z.val = p u → lift z = u) →
      Set.range lift ⊆ connectedComponentIn
        {v : U | (D.developingMap v).2 = (D.developingMap u).2} u := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  let L := A.stableLeaf (p u)
  let := L.native.topology
  let := L.complexCharts
  let : SimplyConnectedSpace (StableAsymptoticLeaf f.toHomeomorph (p u)) := L.complete.1
  dsimp only
  intro lift hlift hproj hpoint
  have hlocal : IsLocallyConstant (fun z ↦ (D.developingMap (lift z)).2) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    obtain ⟨i, N, g, hNo, hzN, hmap, hformula⟩ := D.locally_chart (lift z)
    have hzsource : z.val ∈ (A.chart i).source := by
      rw [← hproj z]
      exact hmap hzN
    obtain ⟨c, hc, hzc, m, hm⟩ := A.stable_affine (p u) i z hzsource
    have hNmem : ∀ᶠ w in 𝓝 z, lift w ∈ N := hlift.continuousAt (hNo.mem_nhds hzN)
    filter_upwards [hNmem, hm] with w hwN hw
    rw [hformula _ hwN, hformula _ hzN]
    change g.2 • (A.chart i (p (lift w))).2 = g.2 • (A.chart i (p (lift z))).2
    rw [hproj w, hproj z, hw.2.2.2]
  let z0 : StableAsymptoticLeaf f.toHomeomorph (p u) := ⟨p u, by simp [ForwardAsymptotic]⟩
  have h0 : lift z0 = u := hpoint z0 rfl
  have hconst (z) : (D.developingMap (lift z)).2 = (D.developingMap u).2 := by
    rw [← h0]
    exact hlocal.apply_eq_of_preconnectedSpace z z0
  apply (isPreconnected_range hlift).subset_connectedComponentIn ⟨z0, h0⟩
  rintro _ ⟨z, rfl⟩
  exact hconst z

/-- A continuous pointed lift of a complete intrinsic unstable leaf lies in the connected component
of the first-coordinate fibre through its marked point. (Ghys, §5 pp.597–598) -/
theorem ordered_projective_unstable_lift_component_subset
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U]
    {p : U → S} (D : OrderedProjectiveProductDevelopment A p) (u : U) :
    let : MetricSpace S := A.metric.replaceTopology A.metric_topology
    let L := A.unstableLeaf (p u)
    let := L.native.topology
    ∀ lift : UnstableAsymptoticLeaf f.toHomeomorph (p u) → U,
      Continuous lift → (∀ z, p (lift z) = z.val) →
      (∀ z, z.val = p u → lift z = u) →
      Set.range lift ⊆ connectedComponentIn
        {v : U | (D.developingMap v).1 = (D.developingMap u).1} u := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  let L := A.unstableLeaf (p u)
  let := L.native.topology
  let := L.complexCharts
  let : SimplyConnectedSpace (UnstableAsymptoticLeaf f.toHomeomorph (p u)) := L.complete.1
  dsimp only
  intro lift hlift hproj hpoint
  have hlocal : IsLocallyConstant (fun z ↦ (D.developingMap (lift z)).1) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    obtain ⟨i, N, g, hNo, hzN, hmap, hformula⟩ := D.locally_chart (lift z)
    have hzsource : z.val ∈ (A.chart i).source := by
      rw [← hproj z]
      exact hmap hzN
    obtain ⟨c, hc, hzc, m, hm⟩ := A.unstable_affine (p u) i z hzsource
    have hNmem : ∀ᶠ w in 𝓝 z, lift w ∈ N := hlift.continuousAt (hNo.mem_nhds hzN)
    filter_upwards [hNmem, hm] with w hwN hw
    rw [hformula _ hwN, hformula _ hzN]
    change g.1 • (A.chart i (p (lift w))).1 = g.1 • (A.chart i (p (lift z))).1
    rw [hproj w, hproj z, hw.2.2.2]
  let z0 : UnstableAsymptoticLeaf f.toHomeomorph (p u) :=
    ⟨p u, by simp [ForwardAsymptotic]⟩
  have h0 : lift z0 = u := hpoint z0 rfl
  have hconst (z) : (D.developingMap (lift z)).1 = (D.developingMap u).1 := by
    rw [← h0]
    exact hlocal.apply_eq_of_preconnectedSpace z z0
  apply (isPreconnected_range hlift).subset_connectedComponentIn ⟨z0, h0⟩
  rintro _ ⟨z, rfl⟩
  exact hconst z

end HolomorphicAnosov.Ghys
