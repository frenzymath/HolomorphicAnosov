import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The canonical chart map on the whole open subtype equals the canonical chart map on the original
manifold. (Andrews, pp.83–84) -/
theorem connectionChartMap_chartAt (p : M) :
    connectionChartMap (chartAt E (⟨p, mem_univ p⟩ : ConnectionWhole M)) = chartAt E p := by
  rfl

omit [FiniteDimensional ℝ E] in
/-- The induced tangent chart agrees with the tangent-bundle chart over the base chart source.
(Andrews, pp.83–84) -/
theorem connectionTangentChart_chartAt (z w : TangentBundle 𝓘(ℝ, E) M)
    (hw : w.proj ∈ (chartAt E z.proj).source) :
    connectionTangentChart (chartAt E
      (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)) w =
      chartAt (ModelProd E E) z w := by
  unfold connectionTangentChart
  rw [connectionChartMap_chartAt]
  have h := tangentMap_chart (I := 𝓘(ℝ, E)) (p := z) (q := w) hw
  exact congrArg (TotalSpace.toProd E E) h

omit [FiniteDimensional ℝ E] in
/-- The derivative of the canonical induced tangent chart is invertible at its center. (Andrews,
pp.83–84) -/
theorem connectionTangentChart_chartAt_mfderiv_isInvertible (z : TangentBundle 𝓘(ℝ, E) M) :
    (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E)
      (connectionTangentChart (chartAt E
        (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M))) z).IsInvertible := by
  have heq : connectionTangentChart (chartAt E
      (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)) =ᶠ[𝓝 z]
        (chartAt (ModelProd E E) z) := by
    have hn : (Bundle.TotalSpace.proj ⁻¹' (chartAt E z.proj).source) ∈ 𝓝 z :=
      (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).continuousAt.preimage_mem_nhds
        ((chartAt E z.proj).open_source.mem_nhds (mem_chart_source E z.proj))
    filter_upwards [hn] with w hw
    exact connectionTangentChart_chartAt z w hw
  rw [heq.mfderiv_eq]
  exact (isInvertible_mfderiv_extChartAt (I := (𝓘(ℝ, E)).tangent)
    (x := z) (y := z) (by simp))

omit [FiniteDimensional ℝ E] in
/-- The derivative of the canonical induced tangent chart is injective at its center. (Andrews,
pp.83–84) -/
theorem connectionTangentChart_chartAt_mfderiv_injective (z : TangentBundle 𝓘(ℝ, E) M) :
    Function.Injective (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E)
      (connectionTangentChart (chartAt E
        (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M))) z) := by
  exact (connectionTangentChart_chartAt_mfderiv_isInvertible z).injective

/-- Two vector fields with the connection spray coordinate formula are equal. (Andrews, Ex. 8.11.3,
p.84) -/
theorem hasConnectionSprayCoordinates_unique
    (nabla : SmoothAffineConnection E M)
    {G G' : (z : TangentBundle 𝓘(ℝ, E) M) →
      TangentSpace (𝓘(ℝ, E)).tangent z}
    (hG : HasConnectionSprayCoordinates nabla G)
    (hG' : HasConnectionSprayCoordinates nabla G') : G' = G := by
  funext z
  let c := chartAt E (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  have hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M) :=
    chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
      (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  have hz : (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M) ∈ c.source :=
    mem_chart_source E (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  have heq := hG (finrank ℝ E) (Module.finBasis ℝ E) c hc z hz
  have heq' := hG' (finrank ℝ E) (Module.finBasis ℝ E) c hc z hz
  apply connectionTangentChart_chartAt_mfderiv_injective z
  apply (tangentSpaceCastModel 𝓘(ℝ, E × E)
    (connectionTangentChart c z)).injective
  rw [heq, heq']

/-- A vector field with the connection spray coordinate formula vanishes on the zero section.
(Andrews, p.84) -/
theorem hasConnectionSprayCoordinates_zero
    (nabla : SmoothAffineConnection E M)
    {G : (z : TangentBundle 𝓘(ℝ, E) M) →
      TangentSpace (𝓘(ℝ, E)).tangent z}
    (hG : HasConnectionSprayCoordinates nabla G) (p : M) : G ⟨p, 0⟩ = 0 := by
  let z : TangentBundle 𝓘(ℝ, E) M := ⟨p, 0⟩
  let c := chartAt E (⟨p, mem_univ p⟩ : ConnectionWhole M)
  have hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M) :=
    chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
      (⟨p, mem_univ p⟩ : ConnectionWhole M)
  have hz : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c.source :=
    mem_chart_source E (⟨p, mem_univ p⟩ : ConnectionWhole M)
  have heq := hG (finrank ℝ E) (Module.finBasis ℝ E) c hc z hz
  apply connectionTangentChart_chartAt_mfderiv_injective z
  apply (tangentSpaceCastModel 𝓘(ℝ, E × E)
    (connectionTangentChart c z)).injective
  rw [heq]
  have hv : (connectionTangentChart c z).2 = 0 := by
    simp [connectionTangentChart, z]
  rw [hv]
  simp [connectionChristoffelBilinear]


end
end HolomorphicAnosov


