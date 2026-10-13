import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Coordinates

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- The canonical induced tangent chart is smooth at its center. (Andrews, p.84) -/
theorem connectionTangentChart_chartAt_contMDiffAt (z : TangentBundle 𝓘(ℝ, E) M) :
    ContMDiffAt (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) ∞
      (connectionTangentChart (chartAt E
        (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M))) z := by
  have heq : connectionTangentChart (chartAt E
      (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)) =ᶠ[𝓝 z]
      chartAt (ModelProd E E) z := by
    filter_upwards [(FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).continuousAt.preimage_mem_nhds
      ((chartAt E z.proj).open_source.mem_nhds (mem_chart_source E z.proj))] with w hw
    exact connectionTangentChart_chartAt z w hw
  exact (contMDiffAt_of_mem_maximalAtlas
    (chart_mem_maximalAtlas (I := (𝓘(ℝ, E)).tangent) (n := ∞) z)
    (mem_chart_source (ModelProd E E) z)).congr_of_eventuallyEq heq

end
end HolomorphicAnosov
