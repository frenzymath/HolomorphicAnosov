import HolomorphicAnosov.Linear.HyperbolicDecayAux02

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- The selected generalized spectral subspace is the sum of generalized eigenspaces satisfying the given predicate. -/
def generalizedSpectralPart {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (P : ℂ → Prop) : Submodule ℂ W :=
  ⨆ μ : ℂ, ⨆ (_ : P μ), T.maxGenEigenspace μ



end HolomorphicAnosov
