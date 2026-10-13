import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.Recharted
import Mathlib.Topology.Homeomorph.Defs

/-! The identity identifies `X` with its type copy as topological spaces. (Zhang, §3, p. 11) -/

universe u

namespace HolomorphicAnosov.Theorem12SupportW2

/-- The identity homeomorphism from `X` to `Recharted X` with its inherited topology. (Zhang, §3, p.
11) -/
def copyHomeomorph {X : Type u} [TopologicalSpace X] : X ≃ₜ Recharted X :=
  Homeomorph.refl X

end HolomorphicAnosov.Theorem12SupportW2
