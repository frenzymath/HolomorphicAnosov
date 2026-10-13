import HolomorphicAnosov.Linear.HyperbolicDecayAux16

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- Powers of the restriction of an automorphism to an invariant subspace agree with its ambient
powers under inclusion. -/
theorem invariantSubspaceEquiv_pow_coe
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W ≃L[𝕜] W) (p : Submodule 𝕜 W)
    (hf : ∀ v ∈ p, T v ∈ p) (hb : ∀ v ∈ p, T.symm v ∈ p) (n : ℕ) (v : p) :
    (((invariantSubspaceEquiv T p hf hb) ^ n) v : W) = (T ^ n) (v : W) := by
  change (((invariantSubspaceEquiv T p hf hb) ^ n).toContinuousLinearMap v : W) =
    (T ^ n).toContinuousLinearMap (v : W)
  rw [equiv_pow_map, equiv_pow_map, invariantSubspaceEquiv_map]
  exact restrict_pow_coe T.toContinuousLinearMap p hf n v



end HolomorphicAnosov
