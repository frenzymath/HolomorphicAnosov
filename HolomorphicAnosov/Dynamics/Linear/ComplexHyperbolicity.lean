import Mathlib.LinearAlgebra.Eigenspace.Basic
import HolomorphicAnosov.Geometry.ComplexModel

/-!
# Complex linear hyperbolicity

The predicate tests every complex eigenvalue against the unit circle. It is
vacuous on the zero-dimensional model, as required by the reviewed interface.
-/

namespace HolomorphicAnosov

def ComplexLinearHyperbolic {d : ℕ}
    (A : Module.End ℂ (ComplexModel d)) : Prop :=
  ∀ μ : ℂ, Module.End.HasEigenvalue A μ → ‖μ‖ ≠ 1

end HolomorphicAnosov
