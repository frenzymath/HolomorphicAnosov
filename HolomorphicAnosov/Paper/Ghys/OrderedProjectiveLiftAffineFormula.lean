import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

/-- Near each point of a continuous lift of an intrinsic stable leaf, its developing coordinate is a
fixed projective transformation of a chart of the supplied complete affine structure. (Ghys, §5
pp.597–598) -/
theorem ordered_projective_stable_lift_local_affine
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U]
    {p : U → S} (D : OrderedProjectiveProductDevelopment A p) (u : U) :
    letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
    let L := A.stableLeaf (p u)
    letI := L.native.topology
    letI := L.complexCharts
    ∀ lift : StableAsymptoticLeaf f.toHomeomorph (p u) → U,
      Continuous lift → (∀ z, p (lift z) = z.val) →
      ∀ z, ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
        z ∈ c.source ∧ ∃ m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ y in 𝓝 z, y ∈ c.source ∧
            (D.developingMap (lift y)).1 = m • complexProjectiveLineFinite (c y) ∧
            (D.developingMap (lift y)).2 = (D.developingMap (lift z)).2 := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  let L := A.stableLeaf (p u)
  let := L.native.topology
  let := L.complexCharts
  dsimp only
  intro lift hlift hproj z
  obtain ⟨i, N, g, hNo, hzN, hmap, hformula⟩ := D.locally_chart (lift z)
  have hzsource : z.val ∈ (A.chart i).source := by
    rw [← hproj z]
    exact hmap hzN
  obtain ⟨c, hc, hzc, m, hm⟩ := A.stable_affine (p u) i z hzsource
  refine ⟨c, hc, hzc, g.1 * m, ?_⟩
  have hNmem : ∀ᶠ y in 𝓝 z, lift y ∈ N := hlift.continuousAt (hNo.mem_nhds hzN)
  filter_upwards [hNmem, hm] with y hyN hy
  refine ⟨hy.1, ?_, ?_⟩
  · rw [hformula _ hyN]
    change g.1 • (A.chart i (p (lift y))).1 = _
    rw [hproj y, hy.2.2.1, mul_smul]
  · rw [hformula _ hyN, hformula _ hzN]
    change g.2 • (A.chart i (p (lift y))).2 =
      g.2 • (A.chart i (p (lift z))).2
    rw [hproj y, hproj z, hy.2.2.2]

/-- Near each point of a continuous lift of an intrinsic unstable leaf, its developing coordinate is
a fixed projective transformation of a chart of the supplied complete affine structure. (Ghys,
§5 pp.597–598) -/
theorem ordered_projective_unstable_lift_local_affine
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U]
    {p : U → S} (D : OrderedProjectiveProductDevelopment A p) (u : U) :
    letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
    let L := A.unstableLeaf (p u)
    letI := L.native.topology
    letI := L.complexCharts
    ∀ lift : UnstableAsymptoticLeaf f.toHomeomorph (p u) → U,
      Continuous lift → (∀ z, p (lift z) = z.val) →
      ∀ z, ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
        z ∈ c.source ∧ ∃ m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ y in 𝓝 z, y ∈ c.source ∧
            (D.developingMap (lift y)).2 = m • complexProjectiveLineFinite (c y) ∧
            (D.developingMap (lift y)).1 = (D.developingMap (lift z)).1 := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  let L := A.unstableLeaf (p u)
  let := L.native.topology
  let := L.complexCharts
  dsimp only
  intro lift hlift hproj z
  obtain ⟨i, N, g, hNo, hzN, hmap, hformula⟩ := D.locally_chart (lift z)
  have hzsource : z.val ∈ (A.chart i).source := by
    rw [← hproj z]
    exact hmap hzN
  obtain ⟨c, hc, hzc, m, hm⟩ := A.unstable_affine (p u) i z hzsource
  refine ⟨c, hc, hzc, g.2 * m, ?_⟩
  have hNmem : ∀ᶠ y in 𝓝 z, lift y ∈ N := hlift.continuousAt (hNo.mem_nhds hzN)
  filter_upwards [hNmem, hm] with y hyN hy
  refine ⟨hy.1, ?_, ?_⟩
  · rw [hformula _ hyN]
    change g.2 • (A.chart i (p (lift y))).2 = _
    rw [hproj y, hy.2.2.1, mul_smul]
  · rw [hformula _ hyN, hformula _ hzN]
    change g.1 • (A.chart i (p (lift y))).1 =
      g.1 • (A.chart i (p (lift z))).1
    rw [hproj y, hproj z, hy.2.2.2]

end HolomorphicAnosov.Ghys
