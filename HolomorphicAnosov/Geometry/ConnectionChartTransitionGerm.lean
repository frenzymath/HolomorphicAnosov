import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Composing a chart transition with the first chart recovers the second chart near the base point. (Andrews, Exercise 8.3.2) -/
theorem connectionChart_transition_eventuallyEq
    (c c' : OpenPartialHomeomorph (ConnectionWhole M) E)
    (p : M) (hp : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c.source) :
    ((connectionChartMap c' ∘ connectionChartInverse c) ∘ connectionChartMap c)
      =ᶠ[𝓝 p] connectionChartMap c' := by
  have hι : Continuous (fun q : M ↦ (⟨q, mem_univ q⟩ : ConnectionWhole M)) :=
    continuous_id.subtype_mk _
  filter_upwards [hι.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hp)] with q hq
  change c' (c.symm (c ⟨q, mem_univ q⟩)) = c' ⟨q, mem_univ q⟩
  rw [c.left_inv hq]

end
end HolomorphicAnosov
