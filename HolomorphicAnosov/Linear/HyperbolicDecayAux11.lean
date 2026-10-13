import HolomorphicAnosov.Linear.HyperbolicDecayAux10

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- The forward map of the restricted automorphism is the restriction of the original continuous linear map. -/
theorem invariantSubspaceEquiv_map
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W ≃L[𝕜] W) (p : Submodule 𝕜 W)
    (hf : ∀ v ∈ p, T v ∈ p) (hb : ∀ v ∈ p, T.symm v ∈ p) :
    (invariantSubspaceEquiv T p hf hb).toContinuousLinearMap = T.toContinuousLinearMap.restrict hf := by
  ext v
  rfl



end HolomorphicAnosov
