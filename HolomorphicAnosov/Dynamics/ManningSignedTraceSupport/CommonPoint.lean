import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Blocks

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.217: all union labels contain the same actual point of Λ. -/
def CommonPoint {Λ : Type u} {N r : ℕ} (R : Fin N → Set Λ)
    {c : Composition r} (s : Blocks N c) : Prop :=
  ∃ x : Λ, ∀ k, ∀ i ∈ s k, x ∈ R i


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
