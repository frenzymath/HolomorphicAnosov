import Mathlib.Geometry.Manifold.Diffeomorph
open scoped Manifold
open scoped ContDiff Manifold
namespace HolomorphicAnosov
lemma diffeomorph_continuous_projection
    {𝕜 E E' H H' M M' : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H' M']
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    (φ : Diffeomorph I I' M M' ∞) : Continuous φ :=
  φ.continuous
end HolomorphicAnosov
