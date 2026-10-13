import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveFrameEvaluationG7

/-! The evaluation of a continuous ordered frame section locally equals a fixed PSL×PSL
transformation composed with an atlas chart and the covering projection. -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

theorem ordered_projective_section_local_formula
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    (Z : FiberBundleCore A.index S OrderedProjectiveFrameGroup)
    (hbase : Z.baseSet = fun i ↦ (A.chart i).source)
    (hindex : Z.indexAt = fun x ↦ Classical.choose (A.cover x))
    (hchange : Z.coordChange =
      fun i j x g ↦ g * (A.transition i j x)⁻¹)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] (p : U → S) (hp : Continuous p)
    (s : C(U, Z.TotalSpace)) (hsproj : ∀ u, (s u).proj = p u) :
    let ev : Z.TotalSpace → ComplexProjectiveLine × ComplexProjectiveLine :=
      fun z ↦ ((z.2.1 • (A.chart (Z.indexAt z.1) z.1).1),
        (z.2.2 • (A.chart (Z.indexAt z.1) z.1).2))
    ∀ u, ∃ (i : A.index)
      (g : OrderedProjectiveFrameGroup) (N : Set U),
      IsOpen N ∧ u ∈ N ∧ Set.MapsTo p N (A.chart i).source ∧
        ∀ y ∈ N, ev (s y) =
          (g.1 • (A.chart i (p y)).1, g.2 • (A.chart i (p y)).2) := by
  let ev : Z.TotalSpace → ComplexProjectiveLine × ComplexProjectiveLine :=
    fun z ↦ ((z.2.1 • (A.chart (Z.indexAt z.1) z.1).1),
      (z.2.2 • (A.chart (Z.indexAt z.1) z.1).2))
  dsimp only
  intro u
  let i := Z.indexAt (p u)
  have hpu : p u ∈ (A.chart i).source := by
    have h := Z.mem_baseSet_at (p u)
    rw [hbase] at h
    exact h
  have hsu : s u ∈ (Z.localTriv i).source := by
    rw [(Z.localTriv i).mem_source, ← Z.baseSet_at, hbase]
    simpa [hsproj u] using hpu
  let g : OrderedProjectiveFrameGroup := (Z.localTriv i (s u)).2
  have hlabelAt : ContinuousAt (fun z : Z.TotalSpace ↦ (Z.localTriv i z).2) (s u) :=
    ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hsu).snd
  have hevlabel : ∀ᶠ z in 𝓝 (s u), (Z.localTriv i z).2 = g :=
    hlabelAt.eventually ((isOpen_discrete {g}).mem_nhds (mem_singleton _))
  obtain ⟨V, hVsub, hVo, hsuV⟩ := mem_nhds_iff.mp hevlabel
  let N : Set U := p ⁻¹' (A.chart i).source ∩ s ⁻¹' V
  refine ⟨i, g, N, ?_, ?_, ?_, ?_⟩
  · exact hp.isOpen_preimage _ (A.chart i).open_source |>.inter
      (s.continuous.isOpen_preimage V hVo)
  · exact ⟨hpu, hsuV⟩
  · intro y hy
    exact hy.1
  · intro y hy
    have hsy : s y ∈ (Z.localTriv i).source := by
      rw [(Z.localTriv i).mem_source, ← Z.baseSet_at, hbase]
      simpa [hsproj y] using hy.1
    have hev := (ordered_projective_frame_evaluation A Z hbase hindex hchange).2
      i (s y) (hsproj y ▸ hy.1)
    have hlabel : (Z.localTriv i (s y)).2 = g := hVsub hy.2
    change ev (s y) = _
    have hev' : ev (s y) =
        ((Z.localTriv i (s y)).2.1 • (A.chart i (s y).proj).1,
          (Z.localTriv i (s y)).2.2 • (A.chart i (s y).proj).2) := by
      simpa [ev] using hev
    rw [hev', hlabel, hsproj y]

end HolomorphicAnosov.Ghys
