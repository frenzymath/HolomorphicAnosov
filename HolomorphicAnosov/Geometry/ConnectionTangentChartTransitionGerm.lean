import HolomorphicAnosov.Geometry.ConnectionTangentChartTransitionLaw

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The induced tangent transition formula holds on a neighborhood of each point over a chart
overlap. (Andrews, Ex. 8.11.3, p.84) -/
theorem connectionTangentChart_transition_eventuallyEq
    (c c' : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (hc' : c' ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (z : TangentBundle 𝓘(ℝ, E) M)
    (hp : (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M) ∈ c.source)
    (hp' : (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M) ∈ c'.source) :
    let h := connectionChartMap c' ∘ connectionChartInverse c
    connectionTangentChart c' =ᶠ[𝓝 z]
      (fun w ↦ (h (connectionTangentChart c w).1,
        fderiv ℝ h (connectionTangentChart c w).1 (connectionTangentChart c w).2)) := by
  have hproj : Continuous (fun w : TangentBundle 𝓘(ℝ, E) M ↦
      (⟨w.proj, mem_univ w.proj⟩ : ConnectionWhole M)) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).subtype_mk _
  filter_upwards [hproj.continuousAt.preimage_mem_nhds
    ((c.open_source.inter c'.open_source).mem_nhds ⟨hp, hp'⟩)] with w hw
  exact connectionTangentChart_transition c c' hc hc' w hw.1 hw.2

end
end HolomorphicAnosov
