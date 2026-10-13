import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! Real tangent distributions are families of real submodules of the tangent fibres. -/

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]

abbrev RealTangentDistribution (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] :=
  ∀ x : X, Submodule ℝ (TangentSpace I x)

end HolomorphicAnosov
