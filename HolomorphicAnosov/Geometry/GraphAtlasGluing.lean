import HolomorphicAnosov.Geometry.LocalProjectionGraph
import HolomorphicAnosov.Geometry.NativeLeafGraphCrossAtlasCompatibility
import HolomorphicAnosov.Geometry.NativeLeafGraphComplexTransition
import HolomorphicAnosov.Geometry.NativeLeafGraphComplexManifoldOfTransitions

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-- A complex atlas obtained by gluing local projection graph charts, with compatibility between its
underlying real atlas and the given leaf atlas. -/
structure NativeLeafGraphAtlas
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M) where
  charts : ChartedSpace (ComplexModel k) L
  complex_manifold : letI := charts
    IsManifold (complexModel k) ∞ L
  real_to_complex : ∀ e : OpenPartialHomeomorph L (Fin (2*k) → ℝ),
    e ∈ atlas (Fin (2*k) → ℝ) L →
    ∀ c : OpenPartialHomeomorph L (ComplexModel k),
      c ∈ charts.atlas →
      ContDiffOn ℝ ∞ (c ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' c.source)
  /-- Every local projection graph chart belongs to the glued complex atlas. -/
  graph_chart_mem : ∀ x : L,
    ∀ G : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x,
      G.chart ∈ charts.atlas
  complex_to_real : ∀ c : OpenPartialHomeomorph L (ComplexModel k),
    c ∈ charts.atlas →
    ∀ e : OpenPartialHomeomorph L (Fin (2*k) → ℝ),
      e ∈ atlas (Fin (2*k) → ℝ) L →
      ContDiffOn ℝ ∞ (e ∘ c.symm)
        (c.target ∩ c.symm ⁻¹' e.source)
  graph_transition : ∀ x y : L,
    ∀ A : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x,
    ∀ B : NativeLeafLocalProjectionGraph (k := k) (d := d) inc y,
    ContDiffOn ℝ ∞ (B.chart ∘ A.chart.symm)
      (A.chart.target ∩ A.chart.symm ⁻¹' B.chart.source)

/-- Complex transition certificates for local projection graphs yield a complex atlas compatible
with the given real leaf atlas. -/
theorem native_leaf_graph_atlas_gluing_of_transition_data
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin (2*k) → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (hlocal : ∀ x : L,
      Nonempty (NativeLeafLocalProjectionGraph (k := k) (d := d) inc x))
    (D : NativeLeafGraphComplexTransitionData (k := k) (d := d) inc) :
    Nonempty (NativeLeafGraphAtlas (k := k) (d := d) inc) := by
  classical
  let I := Σ x : L, NativeLeafLocalProjectionGraph (k := k) (d := d) inc x
  let pick : L → I := fun x => ⟨x, Classical.choice (hlocal x)⟩
  let cfun : I → OpenPartialHomeomorph L (ComplexModel k) := fun i => i.2.chart
  let charts : ChartedSpace (ComplexModel k) L := {
    atlas := Set.range cfun
    chartAt := fun x => cfun (pick x)
    mem_chart_source := fun x => (pick x).2.point_mem_chart
    chart_mem_atlas := fun x => ⟨pick x, rfl⟩ }
  have hpair : ∀ e e' : OpenPartialHomeomorph L (ComplexModel k),
      e ∈ charts.atlas → e' ∈ charts.atlas →
      ContDiffOn ℂ ∞ (e' ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' e'.source) := by
    intro e e' he he'
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    exact D.transition i.1 j.1 i.2 j.2
  let := charts
  have hman : IsManifold (complexModel k) ∞ L :=
    native_leaf_graph_complex_manifold_of_transitions charts hpair
  have hgen : ∀ c : OpenPartialHomeomorph L (ComplexModel k),
      c ∈ charts.atlas → ∃ x : L,
        ∃ G : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x,
          G.chart = c := by
    intro c hc
    obtain ⟨i, rfl⟩ := hc
    exact ⟨i.1, i.2, rfl⟩
  have hcross := native_leaf_graph_cross_atlas_compatibility inc charts hgen hlocal
  refine ⟨{
    charts := charts
    complex_manifold := hman
    real_to_complex := hcross.1
    graph_chart_mem := by
      intro x G
      exact ⟨⟨x, G⟩, rfl⟩
    complex_to_real := hcross.2
    graph_transition := by
      intro x y A B
      exact (D.transition x y A B).restrict_scalars ℝ }⟩

/-- A family of pairwise complex transitions between local projection graph charts yields a
compatible complex leaf atlas. -/
theorem native_leaf_graph_atlas_gluing_of_pairwise_transitions
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin (2*k) → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (hlocal : ∀ x : L,
      Nonempty (NativeLeafLocalProjectionGraph (k := k) (d := d) inc x))
    (hpair : ∀ x y : L,
      ∀ A : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x,
      ∀ B : NativeLeafLocalProjectionGraph (k := k) (d := d) inc y,
      ContDiffOn ℂ ∞ (B.chart ∘ A.chart.symm)
        (A.chart.target ∩ A.chart.symm ⁻¹' B.chart.source)) :
    Nonempty (NativeLeafGraphAtlas (k := k) (d := d) inc) := by
  let D : NativeLeafGraphComplexTransitionData (k := k) (d := d) inc :=
    { transition := hpair }
  exact native_leaf_graph_atlas_gluing_of_transition_data inc hlocal D

/-- Local projection graph charts glue to a complex atlas compatible with the given real leaf atlas. -/
theorem native_leaf_graph_atlas_gluing
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin (2*k) → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (hlocal : ∀ x : L,
      Nonempty (NativeLeafLocalProjectionGraph (k := k) (d := d) inc x)) :
    Nonempty (NativeLeafGraphAtlas (k := k) (d := d) inc) := by
  exact native_leaf_graph_atlas_gluing_of_pairwise_transitions inc hlocal
    (fun x y A B ↦ native_leaf_graph_complex_transition inc x y A B)

end HolomorphicAnosov
