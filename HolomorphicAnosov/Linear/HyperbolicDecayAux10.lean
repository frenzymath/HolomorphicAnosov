import HolomorphicAnosov.Linear.HyperbolicDecayAux09

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- An eigenvector of a restriction is a nonzero eigenvector of the ambient operator with the same eigenvalue. -/
theorem restrict_eigenvalue_lifts
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (p : Submodule ℂ W) (h : ∀ v ∈ p, T v ∈ p)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (T.restrict h) μ) : T.HasEigenvalue μ := by
  obtain ⟨v, hv, hvne⟩ := hμ.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨T.eigenspace_restrict_le_eigenspace h μ ⟨v, hv, rfl⟩, ?_⟩
  intro hz
  exact hvne (Subtype.ext hz)



end HolomorphicAnosov
