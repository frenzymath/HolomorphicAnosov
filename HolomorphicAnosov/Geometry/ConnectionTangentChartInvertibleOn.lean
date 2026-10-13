import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Coordinates

/-!
Invertibility of the derivative of an induced tangent chart on its source. (Lee, Lemma 4.1,
pp.81–82)
-/

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- The derivative of a canonical induced tangent chart is invertible at every point over its base
chart source. (Andrews, p.84) -/
theorem connectionTangentChart_chartAt_mfderiv_isInvertible_of_mem
    (z w : TangentBundle 𝓘(ℝ, E) M) (hw : w.proj ∈ (chartAt E z.proj).source) :
    (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E)
      (connectionTangentChart (chartAt E
        (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M))) w).IsInvertible := by
  have heq : connectionTangentChart (chartAt E
      (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)) =ᶠ[𝓝 w]
      chartAt (ModelProd E E) z := by
    filter_upwards [(FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).continuousAt.preimage_mem_nhds
      ((chartAt E z.proj).open_source.mem_nhds hw)] with q hq
    exact connectionTangentChart_chartAt z q hq
  rw [heq.mfderiv_eq]
  exact isInvertible_mfderiv_extChartAt (I := (𝓘(ℝ, E)).tangent)
    (x := z) (y := w) (by simpa using hw)

end
end HolomorphicAnosov

