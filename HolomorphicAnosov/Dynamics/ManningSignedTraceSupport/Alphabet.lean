import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Blocks
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.AlphabetCondition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.217: the literal finite alphabet, with the original rectangle intersections. -/
abbrev Alphabet {Λ : Type u} {N r : ℕ} (R : Fin N → Set Λ) (c : Composition r) :=
  {s : Blocks N c // AlphabetCondition R c s}

noncomputable instance {Λ : Type u} {N r : ℕ} (R : Fin N → Set Λ)
    (c : Composition r) : Fintype (Alphabet R c) := Fintype.ofFinite _


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
