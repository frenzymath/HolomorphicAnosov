import HolomorphicAnosov.Geometry.LocalProjectionGraph

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-! This file proves real smoothness of chart changes in both directions between a projection graph
atlas and the original real atlas. (Demailly, I Lemma 7.15, p. 60) -/

/-- An atlas consisting of local projection graph charts has real-smooth chart changes in both
directions with the original real atlas on their overlaps. -/
theorem native_leaf_graph_cross_atlas_compatibility
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin (2*k) → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (charts : ChartedSpace (ComplexModel k) L)
    (hgenerated : ∀ c : OpenPartialHomeomorph L (ComplexModel k),
      c ∈ charts.atlas →
      ∃ x : L, ∃ G : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x,
        G.chart = c)
    (_hlocal : ∀ x : L,
      Nonempty (NativeLeafLocalProjectionGraph (k := k) (d := d) inc x)) :
    (∀ e : OpenPartialHomeomorph L (Fin (2*k) → ℝ),
      e ∈ atlas (Fin (2*k) → ℝ) L →
      ∀ c : OpenPartialHomeomorph L (ComplexModel k),
        c ∈ charts.atlas →
        ContDiffOn ℝ ∞ (c ∘ e.symm)
          (e.target ∩ e.symm ⁻¹' c.source)) ∧
    (∀ c : OpenPartialHomeomorph L (ComplexModel k),
      c ∈ charts.atlas →
      ∀ e : OpenPartialHomeomorph L (Fin (2*k) → ℝ),
        e ∈ atlas (Fin (2*k) → ℝ) L →
        ContDiffOn ℝ ∞ (e ∘ c.symm)
          (c.target ∩ c.symm ⁻¹' e.source)) := by
  constructor
  · intro e he c hc
    obtain ⟨x, G, rfl⟩ := hgenerated c hc
    exact G.real_to_complex e he
  · intro c hc e he
    obtain ⟨x, G, rfl⟩ := hgenerated c hc
    exact G.complex_to_real e he

end HolomorphicAnosov
