import HolomorphicAnosov.Linear.HyperbolicDecayAux11

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- The inverse map of the restricted automorphism is the restriction of the original inverse map. -/
theorem invariantSubspaceEquiv_symm_map
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W ≃L[𝕜] W) (p : Submodule 𝕜 W)
    (hf : ∀ v ∈ p, T v ∈ p) (hb : ∀ v ∈ p, T.symm v ∈ p) :
    (invariantSubspaceEquiv T p hf hb).symm.toContinuousLinearMap =
      T.symm.toContinuousLinearMap.restrict hb := by
  ext v
  rfl



end HolomorphicAnosov
