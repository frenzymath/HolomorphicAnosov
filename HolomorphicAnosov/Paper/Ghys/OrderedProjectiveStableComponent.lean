import HolomorphicAnosov.Geometry.ConnectedNativePlaqueAsymptoticG5
import HolomorphicAnosov.SurfaceTorusSupport.OrderedAtlasStablePlaqueInverse

/-! Connected stable developing fibres coincide with pointed intrinsic stable lifts. (Ghys, §5
pp.597–598; Hatcher, Prop. 1.34 p.62) -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology IsManifold
open scoped ContDiff Manifold
universe u v w
attribute [local instance] complex_isManifold_real

/-- A continuous parametrization with locally constant transverse chart coordinate factors
continuously through the specified intrinsic leaf near each point on that leaf. -/
theorem ordered_projective_stable_local_factor
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a) :
    letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
    ∀ x : S, let L := A.stableLeaf x
    letI := L.native.topology
    ∀ {T : Type*} [TopologicalSpace T] (h : T → S) (t : T),
      ContinuousAt h t → ∀ z : StableAsymptoticLeaf f.toHomeomorph x,
      z.val = h t → ∀ i : A.index, h t ∈ (A.chart i).source →
      (∀ᶠ s in 𝓝 t, (A.chart i (h s)).2 = (A.chart i (h t)).2) →
      ∃ ψ : T → StableAsymptoticLeaf f.toHomeomorph x,
        ContinuousAt ψ t ∧ ∀ᶠ s in 𝓝 t, (ψ s).val = h s := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  intro x
  let L := A.stableLeaf x
  let := L.native.topology
  dsimp only
  intro T _ h t hh z hz i hi ht
  obtain ⟨V, inv, hV, hzV, hinv, _, hback⟩ :=
    ordered_atlas_stable_plaque_inverse A x i z (hz ▸ hi)
  have hcoord : ContinuousAt (fun s ↦ A.chart i (h s)) t :=
    ((A.chart i).continuousAt hi).comp hh
  have htarget : (A.chart i (h t)).1 ∈ V := hz ▸ hzV
  let ψ : T → StableAsymptoticLeaf f.toHomeomorph x :=
    fun s ↦ inv ((A.chart i (h s)).1)
  refine ⟨ψ, ?_, ?_⟩
  · exact (hinv.continuousAt (hV.mem_nhds htarget)).comp
      (f := fun s : T ↦ (A.chart i (h s)).1) hcoord.fst
  filter_upwards [hh ((A.chart i).open_source.mem_nhds hi),
    hcoord.fst (hV.mem_nhds htarget), ht] with s hs hsq hst
  change (inv ((A.chart i (h s)).1)).val = h s
  rw [(hback _ hsq).2, hz, ← hst, Prod.mk.eta, (A.chart i).left_inv hs]

/-- The transverse coordinate of a connected developing fibre is constant in each ordered atlas
chart appearing in the local development formula. -/
theorem ordered_projective_fibre_chart_local
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p)
    {T : Type*} [TopologicalSpace T] (h : T → U) (hh : Continuous h)
    (ht : ∀ s t, (D.developingMap (h s)).2 = (D.developingMap (h t)).2)
    (t : T) : ∃ i : A.index, p (h t) ∈ (A.chart i).source ∧
      ∀ᶠ s in 𝓝 t, (A.chart i (p (h s))).2 = (A.chart i (p (h t))).2 := by
  obtain ⟨i, N, g, hN, htN, hmap, hformula⟩ := D.locally_chart (h t)
  refine ⟨i, hmap htN, ?_⟩
  filter_upwards [hh.continuousAt (hN.mem_nhds htN)] with s hs
  apply MulAction.injective g.2
  have he := ht s t
  rw [hformula _ hs, hformula _ htN] at he
  exact he

/-- The connected second-coordinate fibre lies in the pointed lift of the intrinsic stable leaf.
(Ghys, §5 pp.597–598; Hatcher, Prop. 1.34) -/
theorem ordered_projective_stable_component_subset_lift
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p) (u : U) :
    letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
    let L := A.stableLeaf (p u)
    letI := L.native.topology
    ∀ lift : StableAsymptoticLeaf f.toHomeomorph (p u) → U,
      Continuous lift → (∀ z, p (lift z) = z.val) →
      (∀ z, z.val = p u → lift z = u) →
      connectedComponentIn
        {v : U | (D.developingMap v).2 = (D.developingMap u).2} u ⊆ range lift := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  let L := A.stableLeaf (p u)
  let := L.native.topology
  dsimp only
  intro lift hlift hproj hpoint
  let C := connectedComponentIn
    {v : U | (D.developingMap v).2 = (D.developingMap u).2} u
  let : PreconnectedSpace C := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  let u₀ : C := ⟨u, mem_connectedComponentIn rfl⟩
  let inc : C → U := Subtype.val
  let base : C → S := p ∘ inc
  have hbase : Continuous base := D.covering.continuous.comp continuous_subtype_val
  have htrans (s t : C) : (D.developingMap (inc s)).2 =
      (D.developingMap (inc t)).2 :=
    (connectedComponentIn_subset _ _ s.property).trans
      (connectedComponentIn_subset _ _ t.property).symm
  have hlocal (t : C) := ordered_projective_fibre_chart_local A D inc
    continuous_subtype_val htrans t
  have hclass (t : C) : ForwardAsymptotic f.toHomeomorph (p u) (base t) := by
    apply connected_native_plaque_asymptotic_g5 f.toHomeomorph base ?_ u₀ t
    intro s
    let z : StableAsymptoticLeaf f.toHomeomorph (base s) :=
      ⟨base s, by simp [ForwardAsymptotic]⟩
    obtain ⟨i, hi, ht⟩ := hlocal s
    obtain ⟨ψ, _, hψ⟩ := ordered_projective_stable_local_factor A (base s) base s
      hbase.continuousAt z rfl i hi ht
    obtain ⟨V, hVsub, hV, hsV⟩ := mem_nhds_iff.mp hψ
    exact ⟨V, hV, hsV, fun r ↦ ψ r.val, fun r ↦ hVsub r.property⟩
  let into : C → StableAsymptoticLeaf f.toHomeomorph (p u) := fun t ↦ ⟨base t, hclass t⟩
  have hinto : Continuous into := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨i, hi, ht⟩ := hlocal t
    obtain ⟨ψ, hc, he⟩ := ordered_projective_stable_local_factor A (p u) base t
      hbase.continuousAt (into t) rfl i hi ht
    apply hc.congr
    filter_upwards [he] with s hs
    exact Subtype.ext hs
  have hequal : lift ∘ into = inc := D.covering.eq_of_comp_eq
    (hlift.comp hinto) continuous_subtype_val
    (funext fun t ↦ hproj (into t)) u₀ (hpoint (into u₀) rfl)
  intro v hv
  exact ⟨into ⟨v, hv⟩, congrFun hequal ⟨v, hv⟩⟩

end HolomorphicAnosov.Ghys

