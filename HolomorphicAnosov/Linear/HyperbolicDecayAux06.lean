import HolomorphicAnosov.Linear.HyperbolicDecayAux05

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- An automorphism restricts to an equivalence on a subspace invariant under both the map and its inverse. -/
def invariantSubspaceEquiv
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W ≃L[𝕜] W) (p : Submodule 𝕜 W)
    (hf : ∀ v ∈ p, T v ∈ p) (hb : ∀ v ∈ p, T.symm v ∈ p) : p ≃L[𝕜] p :=
  T.ofSubmodules p p (by
    apply le_antisymm
    · rintro v ⟨x, hx, rfl⟩
      exact hf x hx
    · intro v hv
      exact ⟨T.symm v, hb v hv, T.apply_symm_apply v⟩)



end HolomorphicAnosov
