import HolomorphicAnosov.Geometry.Manifold.ChartGluingGeneratorG1

/-! # Global tangent field from chartwise generator data The local Bochner--Montgomery formulas are assembled on one tangent section whose chart representatives agree on overlaps. Once that dependent section has been constructed, the remaining global statement is a direct application of the chart-gluing provider. -/

open scoped Manifold ContDiff Topology _root_.Topology
open Set

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- Chartwise smooth local generator data on a common dependent tangent section assemble into a smooth global tangent field. -/
theorem tangent_field_from_local_generators_g1
    (hX : ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ∀ x, ∃ U ∈ 𝓝 x, CMDiff[U] ∞ (T% X)) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      CMDiff ∞ (T% X) := by
  rcases hX with ⟨X, hlocal⟩
  exact ⟨X, chart_gluing_generator_g1 X hlocal⟩

end HolomorphicAnosov

