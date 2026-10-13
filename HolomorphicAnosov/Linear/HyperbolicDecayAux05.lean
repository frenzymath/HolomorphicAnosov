import HolomorphicAnosov.Linear.HyperbolicDecayAux04

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- Every eigenvalue of the restriction to a selected generalized spectral subspace satisfies the selection predicate. -/
theorem generalizedSpectralPart_restrict_eigenvalue
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (P : ℂ → Prop)
    (h : ∀ v ∈ generalizedSpectralPart T P, T v ∈ generalizedSpectralPart T P)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (T.restrict h) μ) : P μ := by
  by_contra hn
  have hd : Disjoint (T.eigenspace μ) (generalizedSpectralPart T P) :=
    (T.independent_maxGenEigenspace.disjoint_biSup hn).mono_left
      T.eigenspace_le_maxGenEigenspace
  exact hμ (Module.End.eigenspace_restrict_eq_bot h hd)



end HolomorphicAnosov
